import Lean
import Lean.Data.Lsp.Communication
import ViE.State
import ViE.Window.Actions
import ViE.Window.Analysis
import ViE.Data.PieceTable

namespace ViE.Lsp.Lean

open ViE
open Lean.JsonRpc

abbrev LspCfg : IO.Process.StdioConfig := {
  stdin := .piped
  stdout := .piped
  stderr := .null
}

abbrev LspChild := IO.Process.Child LspCfg

structure HoverInfo where
  uri : String
  line : Nat
  col : Nat
  range? : Option (Nat × Nat × Nat × Nat) := none
  text : String
  deriving Inhabited

structure DiagnosticInfo where
  severity : Nat
  line : Nat
  col : Nat
  message : String
  deriving Inhabited

structure UiState where
  pendingHover : Lean.RBMap Nat (String × Nat × Nat) compare
  hover : Option HoverInfo
  diagnostics : Lean.RBMap String (Array DiagnosticInfo) compare
  deriving Inhabited

structure Session where
  child : LspChild
  rootPath : Option String
  nextId : Nat
  versions : Lean.RBMap String Nat compare
  reader : Task (Except IO.Error Unit)

initialize sessionRef : IO.Ref (Option Session) ← IO.mkRef none
initialize uiStateRef : IO.Ref UiState ← do
  IO.mkRef {
    pendingHover := Lean.RBMap.empty
    hover := none
    diagnostics := Lean.RBMap.empty
  }

private def isLeanPath (path : String) : Bool :=
  path.endsWith ".lean"

def isLeanBuffer (buf : FileBuffer) : Bool :=
  match buf.filename with
  | some f => isLeanPath f
  | none => false

private def fileUri (path : String) : String :=
  if path.startsWith "/" then s!"file://{path}" else s!"file:///{path}"

private def mkRequest (id : Nat) (method : String) (params : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("jsonrpc", .str "2.0"),
    ("id", (id : Lean.Json)),
    ("method", .str method),
    ("params", params)
  ]

private def mkNotification (method : String) (params : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("jsonrpc", .str "2.0"),
    ("method", .str method),
    ("params", params)
  ]

private def send (h : IO.FS.Handle) (msg : Lean.Json) : IO Unit := do
  let body := msg.compress
  let header := s!"Content-Length: {body.toUTF8.size}\r\n\r\n"
  h.putStr header
  h.putStr body
  h.flush

private def resetUiState : IO Unit :=
  uiStateRef.set {
    pendingHover := Lean.RBMap.empty
    hover := none
    diagnostics := Lean.RBMap.empty
  }

private def getObjStr? (j : Lean.Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption

private def getObjNat? (j : Lean.Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption

private def severityLabel (sev : Nat) : String :=
  match sev with
  | 1 => "Error"
  | 2 => "Warning"
  | 3 => "Info"
  | 4 => "Hint"
  | _ => "Info"

private def jsonNat? (j : Lean.Json) : Option Nat :=
  match j with
  | .num n =>
      if n.exponent == 0 && n.mantissa >= 0 then
        some n.mantissa.toNat
      else
        none
  | .str s => s.toNat?
  | _ => none

private partial def hoverContentsText (j : Lean.Json) : String :=
  match j with
  | .str s => s
  | .arr xs =>
      String.intercalate "\n\n" (xs.toList.map hoverContentsText)
  | .obj _ =>
      match getObjStr? j "value", getObjStr? j "language" with
      | some v, some lang => s!"```{lang}\n{v}\n```"
      | some v, none => v
      | none, _ => j.compress
  | _ => ""

private def parseHoverText (result : Lean.Json) : Option String := do
  let contents ← (result.getObjVal? "contents").toOption
  let txt := hoverContentsText contents
  if txt.trimAscii.isEmpty then none else some txt

private def parseHoverRange (result : Lean.Json) : Option (Nat × Nat × Nat × Nat) := do
  let range ← (result.getObjVal? "range").toOption
  let start ← (range.getObjVal? "start").toOption
  let «end» ← (range.getObjVal? "end").toOption
  let sLine ← getObjNat? start "line"
  let sCol ← getObjNat? start "character"
  let eLine ← getObjNat? «end» "line"
  let eCol ← getObjNat? «end» "character"
  some (sLine, sCol, eLine, eCol)

private def parseDiagnostic (j : Lean.Json) : Option DiagnosticInfo := do
  let range ← (j.getObjVal? "range").toOption
  let start ← (range.getObjVal? "start").toOption
  let line ← getObjNat? start "line"
  let col := (getObjNat? start "character").getD 0
  let sev := (getObjNat? j "severity").getD 3
  let msg ← getObjStr? j "message"
  some { severity := sev, line := line, col := col, message := msg }

private def handleDiagnosticsNotification (params : Lean.Json) : IO Unit := do
  let uri := (getObjStr? params "uri").getD ""
  if uri.isEmpty then
    pure ()
  else
    let ds := (params.getObjValAs? (Array Lean.Json) "diagnostics").toOption.getD #[]
    let parsed := ds.foldl (fun acc d =>
      match parseDiagnostic d with
      | some item => acc.push item
      | none => acc
    ) #[]
    let st ← uiStateRef.get
    uiStateRef.set { st with diagnostics := st.diagnostics.insert uri parsed }

private def handleHoverResponse (reqId : Nat) (result : Lean.Json) : IO Unit := do
  let st ← uiStateRef.get
  let pending := st.pendingHover
  let hoverMap := pending.erase reqId
  match pending.find? reqId with
  | none =>
      uiStateRef.set { st with pendingHover := hoverMap }
  | some (uri, line, col) =>
      let hover :=
        match parseHoverText result with
        | some txt =>
            let range? := parseHoverRange result
            some { uri := uri, line := line, col := col, range? := range?, text := txt }
        | none =>
            match st.hover with
            | some h =>
                if h.uri == uri && h.line == line && h.col == col then some h else none
            | none => none
      uiStateRef.set { st with pendingHover := hoverMap, hover := hover }

private def handleIncomingJson (j : Lean.Json) : IO Unit := do
  let method? := getObjStr? j "method"
  match method? with
  | some "textDocument/publishDiagnostics" =>
      match (j.getObjVal? "params").toOption with
      | some params => handleDiagnosticsNotification params
      | none => pure ()
  | _ =>
      match (j.getObjVal? "id").toOption, (j.getObjVal? "result").toOption with
      | some idJson, some result =>
          let some reqId := jsonNat? idJson | return ()
          handleHoverResponse reqId result
      | some idJson, none =>
          if (j.getObjVal? "error").toOption.isSome then
            let some reqId := jsonNat? idJson | return ()
            let st ← uiStateRef.get
            uiStateRef.set { st with pendingHover := st.pendingHover.erase reqId }
          else
            pure ()
      | _, _ => pure ()

private partial def readLoop (h : IO.FS.Handle) : IO Unit := do
  try
    let stream := IO.FS.Stream.ofHandle h
    let raw ← stream.readLspMessageAsString
    match Lean.Json.parse raw with
    | .ok j => handleIncomingJson j
    | .error _ => pure ()
    readLoop h
  catch _ =>
    pure ()

private def startServer (root : Option String) : IO LspChild := do
  let cwd := root.map System.FilePath.mk
  IO.Process.spawn {
    cmd := "lake"
    args := #["env", "lean", "--server"]
    cwd := cwd
    stdin := .piped
    stdout := .piped
    stderr := .null
  }

private def initializeServer (session : Session) : IO Session := do
  let rootUri :=
    match session.rootPath with
    | some p => Lean.Json.str (fileUri p)
    | none => Lean.Json.null
  let initParams := Lean.Json.mkObj [
    ("processId", Lean.Json.null),
    ("rootUri", rootUri),
    ("capabilities", Lean.Json.mkObj []),
    ("clientInfo", Lean.Json.mkObj [("name", .str "vie")])
  ]
  let initializeReq := mkRequest session.nextId "initialize" initParams
  send session.child.stdin initializeReq
  send session.child.stdin (mkNotification "initialized" (Lean.Json.mkObj []))
  pure { session with nextId := session.nextId + 1 }

private def syncBuffer (session : Session) (buf : FileBuffer) : IO Session := do
  match buf.filename with
  | none => pure session
  | some path =>
      if !isLeanPath path then
        pure session
      else
        let uri := fileUri path
        let version := (session.versions.find? uri).getD 0
        let nextVersion := version + 1
        let text := buf.table.toString
        if version == 0 then
          let didOpenParams := Lean.Json.mkObj [
            ("textDocument", Lean.Json.mkObj [
              ("uri", .str uri),
              ("languageId", .str "lean"),
              ("version", (nextVersion : Lean.Json)),
              ("text", .str text)
            ])
          ]
          send session.child.stdin (mkNotification "textDocument/didOpen" didOpenParams)
        else
          let didChangeParams := Lean.Json.mkObj [
            ("textDocument", Lean.Json.mkObj [
              ("uri", .str uri),
              ("version", (nextVersion : Lean.Json))
            ]),
            ("contentChanges", Lean.Json.arr #[
              Lean.Json.mkObj [("text", .str text)]
            ])
          ]
          send session.child.stdin (mkNotification "textDocument/didChange" didChangeParams)
        pure { session with versions := session.versions.insert uri nextVersion }

private def requestHover (session : Session) (uri : String) (line lspCol cursorCol : Nat) : IO Session := do
  let reqId := session.nextId
  let params := Lean.Json.mkObj [
    ("textDocument", Lean.Json.mkObj [("uri", .str uri)]),
    ("position", Lean.Json.mkObj [
      ("line", (line : Lean.Json)),
      ("character", (lspCol : Lean.Json))
    ])
  ]
  send session.child.stdin (mkRequest reqId "textDocument/hover" params)
  let st ← uiStateRef.get
  uiStateRef.set { st with pendingHover := st.pendingHover.insert reqId (uri, line, cursorCol) }
  pure { session with nextId := reqId + 1 }

private def startForState (state : EditorState) : IO EditorState := do
  match (← sessionRef.get) with
  | some s =>
      match (← s.child.tryWait) with
      | some code =>
          sessionRef.set none
          return { state with message := s!"LSP had exited (code={code}); restarting..." }
      | none =>
          return { state with message := s!"LSP already running (pid={s.child.pid})" }
  | none =>
      try
        resetUiState
        let child ← startServer state.getCurrentWorkspace.rootPath
        let reader ← IO.asTask (readLoop child.stdout)
        let session0 : Session := {
          child := child
          rootPath := state.getCurrentWorkspace.rootPath
          nextId := 1
          versions := Lean.RBMap.empty
          reader := reader
        }
        let session1 ← initializeServer session0
        let session2 ← syncBuffer session1 state.getActiveBuffer
        sessionRef.set (some session2)
        return { state with message := s!"LSP started (pid={child.pid})" }
      catch e =>
        return { state with message := s!"Failed to start LSP: {e}" }

private def stopForState (state : EditorState) : IO EditorState := do
  match (← sessionRef.get) with
  | none =>
      return { state with message := "LSP is not running" }
  | some s =>
      try
        s.child.kill
        let _ ← s.child.wait
        sessionRef.set none
        resetUiState
        return { state with message := "LSP stopped" }
      catch e =>
        sessionRef.set none
        resetUiState
        return { state with message := s!"LSP stop error: {e}" }

def stopIfRunning : IO Unit := do
  match (← sessionRef.get) with
  | none => pure ()
  | some s =>
      match (← s.child.tryWait) with
      | some _ =>
          sessionRef.set none
          resetUiState
      | none =>
          try
            s.child.kill
            let _ ← s.child.wait
            sessionRef.set none
            resetUiState
          catch _ =>
            sessionRef.set none
            resetUiState

def syncActiveBufferIfRunning (state : EditorState) : IO Unit := do
  match (← sessionRef.get) with
  | none => pure ()
  | some s =>
      match (← s.child.tryWait) with
      | some _ =>
          sessionRef.set none
      | none =>
          let s' ← syncBuffer s state.getActiveBuffer
          sessionRef.set (some s')

def infoViewVirtualPath : String := "__vie_infoview__"

private def isInfoViewBuffer (buf : FileBuffer) : Bool :=
  buf.filename == some infoViewVirtualPath

private def findBufferById? (ws : WorkspaceState) (bufId : Nat) : Option FileBuffer :=
  ws.buffers.find? (fun b => b.id == bufId)

private def findInfoViewBufferId? (ws : WorkspaceState) : Option Nat :=
  ws.buffers.find? isInfoViewBuffer |>.map (fun b => b.id)

private def findInfoViewWindowId? (ws : WorkspaceState) : Option Nat :=
  match findInfoViewBufferId? ws with
  | none => none
  | some bufId => ws.layout.findWindowIdByBufferId bufId

private def findLeanSourceWindow? (ws : WorkspaceState) : Option (Nat × ViewState × FileBuffer) :=
  let fromWindowId (wid : Nat) : Option (Nat × ViewState × FileBuffer) :=
    match ws.layout.findView wid with
    | none => none
    | some view =>
        match findBufferById? ws view.bufferId with
        | some buf =>
            if isLeanBuffer buf then
              some (wid, view, buf)
            else
              none
        | none => none

  let activeHit :=
    if ws.layout.containsWindow ws.activeWindowId then
      fromWindowId ws.activeWindowId
    else
      none
  match activeHit with
  | some hit => some hit
  | none =>
      let rec findFirst (ids : List Nat) : Option (Nat × ViewState × FileBuffer) :=
        match ids with
        | [] => none
        | wid :: rest =>
            match fromWindowId wid with
            | some hit => some hit
            | none => findFirst rest
      findFirst (ViE.Window.getWindowIds ws.layout)

private def ensureInfoViewBuffer (state : EditorState) : EditorState × Nat :=
  let ws := state.getCurrentWorkspace
  match findInfoViewBufferId? ws with
  | some bufId => (state, bufId)
  | none =>
      let newId := ws.nextBufferId
      let newBuf : FileBuffer := {
        initialBuffer with
          id := newId
          filename := some infoViewVirtualPath
          table := PieceTable.fromString ""
          loaded := true
          dirty := false
      }
      let s' := state.updateCurrentWorkspace fun ws =>
        { ws with buffers := newBuf :: ws.buffers, nextBufferId := ws.nextBufferId + 1 }
      (s', newId)

private def closeInfoViewWindowAndBuffer (state : EditorState) : EditorState :=
  let ws := state.getCurrentWorkspace
  match findInfoViewBufferId? ws with
  | none => state
  | some infoBufId =>
      let infoWindowId := findInfoViewWindowId? ws
      let wsClosed :=
        match infoWindowId with
        | none => ws
        | some wid =>
            match ws.layout.remove wid with
            | none => ws
            | some layout' =>
                let ids := ViE.Window.getWindowIds layout'
                let active' :=
                  if ws.activeWindowId == wid then
                    ids.head?.getD ws.activeWindowId
                  else
                    ws.activeWindowId
                { ws with layout := layout', activeWindowId := active' }.pruneFloatingWindows
      let wsFinal := { wsClosed with buffers := wsClosed.buffers.filter (fun b => b.id != infoBufId) }
      state.updateCurrentWorkspace (fun _ => wsFinal)

private def ensureInfoViewWindow (state : EditorState) (sourceWindowId infoBufId : Nat) : EditorState :=
  let ws := state.getCurrentWorkspace
  match findInfoViewWindowId? ws with
  | some infoWindowId =>
      state.updateCurrentWorkspace fun ws =>
        let layout' := ws.layout.updateView infoWindowId (fun v => { v with bufferId := infoBufId, scrollRow := 0, scrollCol := 0 })
        { ws with layout := layout' }
  | none =>
      let sFocused :=
        if ws.activeWindowId == sourceWindowId then
          state
        else
          state.updateCurrentWorkspace fun ws => { ws with activeWindowId := sourceWindowId }
      let newWindowId := sFocused.getCurrentWorkspace.nextWindowId
      let sSplit := ViE.Window.splitWindow sFocused false
      sSplit.updateCurrentWorkspace fun ws =>
      let layout1 := ws.layout.updateView newWindowId (fun _ => { initialView with bufferId := infoBufId })
      { ws with layout := layout1, activeWindowId := sourceWindowId }

private def utf16UnitsForChar (c : Char) : Nat :=
  if c.toNat <= 0xFFFF then 1 else 2

private def utf16UnitsOfPrefix (s : String) (n : Nat) : Nat :=
  let rec loop (xs : List Char) (remaining acc : Nat) : Nat :=
    match remaining, xs with
    | 0, _ => acc
    | _, [] => acc
    | rem + 1, c :: cs => loop cs rem (acc + utf16UnitsForChar c)
  loop s.toList n 0

private def hoverDisplayColForMode (mode : Mode) (line : String) (tabStop cursorCol : Nat) : Nat :=
  let lineW := ViE.Unicode.stringWidthWithTabStop line tabStop
  let base := min cursorCol lineW
  let shifted :=
    match mode with
    | .normal | .visual | .visualBlock =>
        if base < lineW then
          ViE.Unicode.nextDisplayColWithTabStop line tabStop base
        else
          base
    | _ => base
  min shifted lineW

private def utf16ColFromDisplayCol (line : String) (tabStop displayCol : Nat) : Nat :=
  let charIdx := ViE.Unicode.displayColToCharIndexWithTabStop line tabStop displayCol
  utf16UnitsOfPrefix line charIdx

private def cursorInHoverRange (h : HoverInfo) (line colUtf16 : Nat) : Bool :=
  match h.range? with
  | none =>
      h.line == line && h.col == colUtf16
  | some (sLine, sCol, eLine, eCol) =>
      if line < sLine || line > eLine then
        false
      else if sLine == eLine then
        line == sLine && sCol <= colUtf16 && colUtf16 < eCol
      else if line == sLine then
        sCol <= colUtf16
      else if line == eLine then
        colUtf16 < eCol
      else
        true

private def requestHoverCandidatesForPointIfRunning (path : String) (line cursorCol : Nat) (lspCols : Array Nat) : IO Unit := do
  if !isLeanPath path then
    pure ()
  else
    match (← sessionRef.get) with
    | none => pure ()
    | some s =>
        match (← s.child.tryWait) with
        | some _ =>
            sessionRef.set none
        | none =>
            let uri := fileUri path
            let mut session := s
            for lspCol in lspCols do
              session ← requestHover session uri line lspCol cursorCol
            sessionRef.set (some session)

def syncHoverForActiveIfRunning (state : EditorState) : IO Unit := do
  let buf := state.getActiveBuffer
  let cursor := state.getCursor
  let line := ViE.getLineFromBuffer buf cursor.row |>.getD ""
  let primaryDisplayCol := cursor.col.val
  let fallbackDisplayCol := hoverDisplayColForMode state.mode line state.config.tabStop cursor.col.val
  let primaryLspCol := utf16ColFromDisplayCol line state.config.tabStop primaryDisplayCol
  let fallbackLspCol := utf16ColFromDisplayCol line state.config.tabStop fallbackDisplayCol
  let lspCols :=
    if primaryLspCol == fallbackLspCol then
      #[primaryLspCol]
    else
      #[primaryLspCol, fallbackLspCol]
  match buf.filename with
  | some path => requestHoverCandidatesForPointIfRunning path cursor.row.val cursor.col.val lspCols
  | none => pure ()

private def formatInfoViewContent (tabStop : Nat) (sourceView : ViewState) (sourceBuf : FileBuffer) : IO String := do
  let fileLabel := sourceBuf.filename.getD "[No Name]"
  let cursor := sourceView.cursor
  let line := cursor.row.val + 1
  let col := cursor.col.val + 1
  let byteOffset :=
    ViE.getOffsetFromPointInBufferWithTabStop sourceBuf cursor.row cursor.col tabStop
  let byteText :=
    match byteOffset with
    | some off => toString off
    | none => "-"

  let uri := match sourceBuf.filename with | some p => fileUri p | none => ""
  let lineStr := ViE.getLineFromBuffer sourceBuf cursor.row |>.getD ""
  let cursorUtf16Col := utf16ColFromDisplayCol lineStr tabStop cursor.col.val
  let st ← uiStateRef.get
  let hoverText :=
    match st.hover with
    | some h =>
        if h.uri == uri && cursorInHoverRange h cursor.row.val cursorUtf16Col then
          h.text
        else
          "No type information at cursor."
    | none => "No type information at cursor."

  let problems := st.diagnostics.find? uri |>.getD #[]
  let problemLines :=
    if problems.isEmpty then
      #["No problems."]
    else
      problems.foldl (fun acc d =>
        let pLine := d.line + 1
        let pCol := d.col + 1
        acc.push s!"[{severityLabel d.severity}] ({pLine},{pCol}) {d.message}"
      ) #[]

  let mut lines : Array String := #[]
  lines := lines.push s!"File: {fileLabel}"
  lines := lines.push s!"Position: {line}:{col}  Byte: {byteText}"
  lines := lines.push ""
  lines := lines.push "Type"
  lines := lines.push hoverText
  lines := lines.push ""
  lines := lines.push s!"Problems ({problems.size})"
  lines := lines ++ problemLines
  pure (String.intercalate "\n" lines.toList)

private def updateInfoViewContent (state : EditorState) (infoBufId : Nat) (sourceView : ViewState) (sourceBuf : FileBuffer) : IO EditorState := do
  let content ← formatInfoViewContent state.config.tabStop sourceView sourceBuf
  pure <| state.updateCurrentWorkspace fun ws =>
    let newBuffers := ws.buffers.map fun b =>
      if b.id == infoBufId then
        if b.table.toString == content then
          b
        else
          {
            b with
              table := PieceTable.fromString content state.config.searchBloomBuildLeafBits
              dirty := false
              cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
          }
      else
        b
    { ws with buffers := newBuffers }

def syncInfoViewWindow (state : EditorState) : IO EditorState := do
  let ws := state.getCurrentWorkspace
  if !state.infoViewRequested then
    return closeInfoViewWindowAndBuffer state
  else
    match findLeanSourceWindow? ws with
    | none =>
        return closeInfoViewWindowAndBuffer state
    | some (sourceWindowId, sourceView, sourceBuf) =>
        let (s1, infoBufId) := ensureInfoViewBuffer state
        let s2 := ensureInfoViewWindow s1 sourceWindowId infoBufId
        updateInfoViewContent s2 infoBufId sourceView sourceBuf

/--
Apply Lean/LSP-specific post-update synchronization.
This keeps editor core update flow independent from Lean-specific InfoView/LSP policies.
-/
def syncEditorUpdate (prevState nextState : EditorState) : IO EditorState := do
  let oldBuf? :=
    if prevState.infoViewRequested then
      some prevState.getActiveBuffer
    else
      none
  let oldCursor? :=
    if prevState.infoViewRequested then
      some prevState.getCursor
    else
      none
  let shouldSyncLspNow :=
    match oldBuf? with
    | none => false
    | some oldBuf =>
        let newBuf := nextState.getActiveBuffer
        oldBuf.id == newBuf.id &&
        oldBuf.table.toString != newBuf.table.toString
  let shouldRefreshHoverNow :=
    match oldCursor? with
    | none => false
    | some oldCursor =>
        let newBuf := nextState.getActiveBuffer
        let newCursor := nextState.getCursor
        (match oldBuf? with
        | some oldBuf => oldBuf.id == newBuf.id
        | none => false) &&
        (oldCursor.row != newCursor.row || oldCursor.col != newCursor.col)
  if shouldSyncLspNow then
    syncActiveBufferIfRunning nextState
  if shouldSyncLspNow || shouldRefreshHoverNow then
    syncHoverForActiveIfRunning nextState
  syncInfoViewWindow nextState

private def activeLanguageConfig (config : Config) (state : EditorState) : LanguageRuntimeConfig :=
  let buf := state.getActiveBuffer
  match buf.filename with
  | some path =>
      if isLeanPath path then
        (config.languageConfigs.find? "lean").getD default
      else
        default
  | none => default

/--
Apply per-language startup defaults (e.g. Lean: auto-start LSP and auto-open InfoView).
-/
def applyStartupLanguageDefaults (config : Config) (state : EditorState) : IO EditorState := do
  let langCfg := activeLanguageConfig config state
  let mut s := state
  if langCfg.autoStartLsp then
    s ← startForState s
  if langCfg.autoOpenInfoView then
    let sReq := { s with infoViewRequested := true }
    let sInfo ← syncInfoViewWindow sReq
    if langCfg.autoStartLsp then
      syncHoverForActiveIfRunning sInfo
    pure sInfo
  else
    pure s

def cmdLsp (args : List String) (state : EditorState) : IO EditorState := do
  let sub := args.head?.getD "status"
  match sub with
  | "start" => startForState state
  | "stop" => stopForState state
  | "status" =>
      match (← sessionRef.get) with
      | none =>
          return { state with message := "LSP: stopped" }
      | some s =>
          match (← s.child.tryWait) with
          | none =>
              return { state with message := s!"LSP: running (pid={s.child.pid})" }
          | some code =>
              sessionRef.set none
              return { state with message := s!"LSP: exited (code={code})" }
  | "sync" => do
      match (← sessionRef.get) with
      | none =>
          return { state with message := "LSP is not running" }
      | some s =>
          let s' ← syncBuffer s state.getActiveBuffer
          sessionRef.set (some s')
          return { state with message := "LSP synced current buffer" }
  | "restart" => do
      let _ ← stopForState state
      startForState state
  | "infoview" =>
      match args.drop 1 with
      | ["on"] =>
          let s := { state with infoViewRequested := true, message := "InfoView: on" }
          let s' ← syncInfoViewWindow s
          syncHoverForActiveIfRunning s'
          pure s'
      | ["off"] =>
          let s := { state with infoViewRequested := false, message := "InfoView: off" }
          syncInfoViewWindow s
      | ["toggle"] =>
          let next := !state.infoViewRequested
          let s := { state with infoViewRequested := next, message := s!"InfoView: {if next then "on" else "off"}" }
          let s' ← syncInfoViewWindow s
          if next then
            syncHoverForActiveIfRunning s'
          pure s'
      | ["status"] | [] =>
          return { state with message := s!"InfoView: {if state.infoViewRequested then "on" else "off"}" }
      | _ =>
          return { state with message := "Usage: :lsp infoview [on|off|toggle|status]" }
  | _ =>
      return { state with message := "Usage: :lsp [start|stop|restart|status|sync|infoview]" }

end ViE.Lsp.Lean
