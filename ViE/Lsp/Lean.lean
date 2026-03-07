-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import Lean
import Lean.Data.Lsp.Communication
import ViE.State
import ViE.Window.Actions
import ViE.Window.Analysis
import ViE.Data.PieceTable
import ViE.Unicode

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
  pendingCompletion : Lean.RBMap Nat (String × Nat × Nat × String) compare
  hover : Option HoverInfo
  completion : Option (String × CompletionPopup)
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
    pendingCompletion := Lean.RBMap.empty
    hover := none
    completion := none
    diagnostics := Lean.RBMap.empty
  }
initialize initializeAckRef : IO.Ref (Option Nat) ← IO.mkRef none
initialize readerFailureRef : IO.Ref (Option (UInt32 × String)) ← IO.mkRef none

private def isLeanPath (path : String) : Bool :=
  path.endsWith ".lean"

def isLeanBuffer (buf : FileBuffer) : Bool :=
  match buf.filename with
  | some f => isLeanPath f
  | none => false

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (65 + (n - 10))

private def pctEncodeByte (b : UInt8) : String :=
  let n := b.toNat
  let hi := n / 16
  let lo := n % 16
  String.singleton '%' ++ String.singleton (hexDigit hi) ++ String.singleton (hexDigit lo)

private def isUriPathSafeByte (b : UInt8) : Bool :=
  let n := b.toNat
  (48 <= n && n <= 57) ||   -- 0-9
  (65 <= n && n <= 90) ||   -- A-Z
  (97 <= n && n <= 122) ||  -- a-z
  n == 45 ||                -- -
  n == 46 ||                -- .
  n == 95 ||                -- _
  n == 126 ||               -- ~
  n == 47                   -- /

private def encodeUriPath (path : String) : String :=
  let bytes := path.toUTF8
  Id.run do
    let mut out := ""
    for b in bytes do
      if isUriPathSafeByte b then
        out := out.push (Char.ofNat b.toNat)
      else
        out := out ++ pctEncodeByte b
    return out

def fileUri (path : String) : String :=
  let absPath :=
    if path.startsWith "/" then
      path
    else
      "/" ++ path
  s!"file://{encodeUriPath absPath}"

private def resolvePathForUri (workspaceRoot : Option String) (path : String) : IO String := do
  let candidate : System.FilePath ←
    if path.startsWith "/" then
      pure (System.FilePath.mk path)
    else
      match workspaceRoot with
      | some root =>
          pure <| System.FilePath.mk (root ++ "/" ++ path)
      | none =>
          let cwd ← IO.currentDir
          pure <| System.FilePath.mk (cwd.toString ++ "/" ++ path)
  try
    let rp ← IO.FS.realPath candidate
    pure rp.toString
  catch _ =>
    pure candidate.normalize.toString

def fileUriWithWorkspace (workspaceRoot : Option String) (path : String) : IO String := do
  let absPath ← resolvePathForUri workspaceRoot path
  pure (fileUri absPath)

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

private def waitForExit (child : LspChild) (tries : Nat := 50) (sleepMs : Nat := 20) : IO Bool := do
  let rec loop : Nat → IO Bool
    | 0 => do
        match (← child.tryWait) with
        | some _ => pure true
        | none => pure false
    | n + 1 => do
        match (← child.tryWait) with
        | some _ => pure true
        | none =>
            IO.sleep sleepMs.toUInt32
            loop n
  loop tries

private def gracefulStopTries : Nat := 8
private def postKillStopTries : Nat := 12
private def finalStopTries : Nat := 6
private def stopPollMs : Nat := 10

private def terminateSession (s : Session) : IO Bool := do
  let killDescendants (sig : String) : IO Unit := do
    try
      let _ ← IO.Process.output {
        cmd := "pkill"
        args := #["-" ++ sig, "-P", toString s.child.pid]
        stdin := .null
        stderr := .null
      }
      pure ()
    catch _ =>
      pure ()
  let shutdownReq := mkRequest s.nextId "shutdown" (Lean.Json.mkObj [])
  let exitNotif := mkNotification "exit" (Lean.Json.mkObj [])
  try
    send s.child.stdin shutdownReq
    send s.child.stdin exitNotif
  catch _ =>
    pure ()
  let stoppedGracefully ← waitForExit s.child gracefulStopTries stopPollMs
  if stoppedGracefully then
    pure true
  else
    killDescendants "TERM"
    try
      s.child.kill
    catch _ =>
      pure ()
    let stoppedAfterKill ← waitForExit s.child postKillStopTries stopPollMs
    if stoppedAfterKill then
      pure true
    else
      killDescendants "KILL"
      waitForExit s.child finalStopTries stopPollMs

private def resetUiState : IO Unit :=
  uiStateRef.set {
    pendingHover := Lean.RBMap.empty
    pendingCompletion := Lean.RBMap.empty
    hover := none
    completion := none
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

def responseId? (j : Lean.Json) : Option Nat := do
  let id ← (j.getObjVal? "id").toOption
  jsonNat? id

def isResponseForRequest (j : Lean.Json) (reqId : Nat) : Bool :=
  responseId? j == some reqId

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

private def parseCompletionItem (j : Lean.Json) : Option CompletionItem := do
  let label ← getObjStr? j "label"
  let insertText :=
    (getObjStr? j "insertText").getD <|
      match (j.getObjVal? "textEdit").toOption with
      | some te => (getObjStr? te "newText").getD label
      | none => label
  some { label := label, insertText := insertText }

private def parseCompletionItems (result : Lean.Json) : Array CompletionItem :=
  let rawItems : Array Lean.Json :=
    match result with
    | .arr xs => xs
    | .obj _ => (result.getObjValAs? (Array Lean.Json) "items").toOption.getD #[]
    | _ => #[]
  rawItems.foldl (fun acc j =>
    match parseCompletionItem j with
    | some item =>
        if item.insertText.isEmpty then acc else acc.push item
    | none => acc
  ) #[]

private def asciiLowerChar (c : Char) : Char :=
  let n := c.toNat
  if 65 <= n && n <= 90 then
    Char.ofNat (n + 32)
  else
    c

private def asciiLower (s : String) : String :=
  String.map asciiLowerChar s

private def startsWithAt (s p : Array Char) (idx : Nat) : Bool :=
  if idx + p.size > s.size then
    false
  else
    Id.run do
      let mut ok := true
      for i in [0:p.size] do
        if s[idx + i]! != p[i]! then
          ok := false
      return ok

private def findSubseqMatch (q target : Array Char) : Option (Nat × Nat × Nat) :=
  if q.isEmpty then
    some (0, 0, 0)
  else
    Id.run do
      let mut qi := 0
      let mut start := 0
      let mut «end» := 0
      let mut foundStart := false
      for i in [0:target.size] do
        if qi < q.size && target[i]! == q[qi]! then
          if !foundStart then
            start := i
            foundStart := true
          qi := qi + 1
          if qi == q.size then
            «end» := i + 1
      if qi == q.size then
        let span := «end» - start
        some (start, «end», span)
      else
        none

private def scoreCompletion (query : String) (item : CompletionItem) : Int :=
  if query.isEmpty then
    0
  else
    let q := (asciiLower query).toList.toArray
    let tStr := asciiLower item.label
    let t := tStr.toList.toArray
    match findSubseqMatch q t with
    | none => -1000000
    | some (start, _, span) =>
        let isPrefix := startsWithAt t q 0
        let contiguous := span == q.size
        let prefixBonus : Int := if isPrefix then 1200 else 0
        let contiguousBonus : Int := if contiguous then 600 else 0
        let boundaryBonus : Int :=
          if start == 0 then
            200
          else
            let prev := t[start - 1]!
            if prev == '.' || prev == '_' || prev == ' ' then 120 else 0
        let gapPenalty : Int := Int.ofNat (span - q.size) * 8
        let lenPenalty : Int := Int.ofNat t.size
        prefixBonus + contiguousBonus + boundaryBonus - gapPenalty - lenPenalty

structure RankedCompletion where
  item : CompletionItem
  score : Int
  deriving Inhabited

private def betterRanked (a b : RankedCompletion) : Bool :=
  if a.score == b.score then
    a.item.label < b.item.label
  else
    a.score > b.score

private def heapSwap (arr : Array RankedCompletion) (i j : Nat) : Array RankedCompletion :=
  let ai := arr[i]!
  let aj := arr[j]!
  (arr.set! i aj).set! j ai

private def siftUp (heap : Array RankedCompletion) (idx : Nat) : Array RankedCompletion := Id.run do
  let mut h := heap
  let mut i := idx
  while i > 0 do
    let p := (i - 1) / 2
    if betterRanked h[p]! h[i]! then
      h := heapSwap h i p
      i := p
    else
      i := 0
  return h

private def siftDown (heap : Array RankedCompletion) (idx : Nat) : Array RankedCompletion := Id.run do
  let mut h := heap
  let mut i := idx
  let n := h.size
  let mut keep := true
  while keep do
    let l := 2 * i + 1
    if l >= n then
      keep := false
    else
      let r := l + 1
      let child :=
        if r < n && betterRanked h[l]! h[r]! then r else l
      if betterRanked h[i]! h[child]! then
        h := heapSwap h i child
        i := child
      else
        keep := false
  return h

private def heapPushTopK (heap : Array RankedCompletion) (k : Nat) (x : RankedCompletion) : Array RankedCompletion :=
  if k == 0 then
    #[]
  else if heap.size < k then
    siftUp (heap.push x) heap.size
  else if betterRanked x heap[0]! then
    siftDown (heap.set! 0 x) 0
  else
    heap

private def sortRankedDesc (arr : Array RankedCompletion) : Array RankedCompletion := Id.run do
  let mut out := arr
  let n := out.size
  for i in [1:n] do
    let cur := out[i]!
    let mut j := i
    while j > 0 && betterRanked cur out[j - 1]! do
      out := out.set! j out[j - 1]!
      j := j - 1
    out := out.set! j cur
  return out

private def rankAndSelectCompletions (query : String) (items : Array CompletionItem) (k : Nat := 40) : Array CompletionItem :=
  let heap := items.foldl (fun h item =>
    let sc := scoreCompletion query item
    if sc <= -1000000 then
      h
    else
      heapPushTopK h k { item := item, score := sc }
  ) #[]
  let ranked := sortRankedDesc heap
  ranked.map (fun r => r.item)

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

private def handleCompletionResponse (reqId : Nat) (result : Lean.Json) : IO Unit := do
  let st ← uiStateRef.get
  let pending := st.pendingCompletion
  let pending' := pending.erase reqId
  match pending.find? reqId with
  | none =>
      uiStateRef.set { st with pendingCompletion := pending' }
  | some (uri, row, col, query) =>
      let items := rankAndSelectCompletions query (parseCompletionItems result) 40
      let completion :=
        if items.isEmpty then
          none
        else
          some (uri, { items := items, selected := 0, anchorRow := row, anchorCol := col })
      uiStateRef.set { st with pendingCompletion := pending', completion := completion }

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
          initializeAckRef.set (some reqId)
          let st ← uiStateRef.get
          if st.pendingHover.find? reqId |>.isSome then
            handleHoverResponse reqId result
          else if st.pendingCompletion.find? reqId |>.isSome then
            handleCompletionResponse reqId result
          else
            pure ()
      | some idJson, none =>
          if (j.getObjVal? "error").toOption.isSome then
            let some reqId := jsonNat? idJson | return ()
            initializeAckRef.set (some reqId)
            let st ← uiStateRef.get
            uiStateRef.set {
              st with
                pendingHover := st.pendingHover.erase reqId
                pendingCompletion := st.pendingCompletion.erase reqId
            }
          else
            pure ()
      | _, _ => pure ()

private partial def readLoop (pid : UInt32) (h : IO.FS.Handle) : IO Unit := do
  try
    let stream := IO.FS.Stream.ofHandle h
    let raw ← stream.readLspMessageAsString
    match Lean.Json.parse raw with
    | .ok j => handleIncomingJson j
    | .error _ => pure ()
    readLoop pid h
  catch e =>
    readerFailureRef.set (some (pid, toString e))
    pure ()

private def clearFailedSessionIfAny : IO Unit := do
  match (← sessionRef.get), (← readerFailureRef.get) with
  | some s, some (pid, _) =>
      if s.child.pid == pid then
        readerFailureRef.set none
        try
          let _ ← terminateSession s
          pure ()
        catch _ =>
          pure ()
        sessionRef.set none
        resetUiState
      else
        pure ()
  | _, _ => pure ()

private def waitForInitializeAck (child : LspChild) (reqId : Nat) (timeoutMs : Nat := 5000) : IO Bool := do
  let tries := (timeoutMs / 10) + 1
  let rec loop : Nat → IO Bool
    | 0 => pure false
    | n + 1 => do
        match (← child.tryWait) with
        | some _ => pure false
        | none =>
            match (← initializeAckRef.get) with
            | some got =>
                initializeAckRef.set none
                if got == reqId then
                  pure true
                else
                  loop n
            | none =>
                IO.sleep 10
                loop n
  loop tries

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
  let rootUri ←
    match session.rootPath with
    | some p => do
        let uri ← fileUriWithWorkspace none p
        pure (Lean.Json.str uri)
    | none =>
        pure Lean.Json.null
  let initParams := Lean.Json.mkObj [
    ("processId", Lean.Json.null),
    ("rootUri", rootUri),
    ("capabilities", Lean.Json.mkObj []),
    ("clientInfo", Lean.Json.mkObj [("name", .str "vie")])
  ]
  let reqId := session.nextId
  let initializeReq := mkRequest reqId "initialize" initParams
  initializeAckRef.set none
  send session.child.stdin initializeReq
  let acked ← waitForInitializeAck session.child reqId
  if !acked then
    throw (IO.userError "LSP initialize handshake timed out")
  send session.child.stdin (mkNotification "initialized" (Lean.Json.mkObj []))
  pure { session with nextId := reqId + 1 }

private def syncBuffer (session : Session) (buf : FileBuffer) : IO Session := do
  match buf.filename with
  | none => pure session
  | some path =>
      if !isLeanPath path then
        pure session
      else
        let uri ← fileUriWithWorkspace session.rootPath path
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

private def requestCompletion (session : Session) (uri : String) (line lspCol row col : Nat) (query : String) : IO Session := do
  let reqId := session.nextId
  let params := Lean.Json.mkObj [
    ("textDocument", Lean.Json.mkObj [("uri", .str uri)]),
    ("position", Lean.Json.mkObj [
      ("line", (line : Lean.Json)),
      ("character", (lspCol : Lean.Json))
    ]),
    ("context", Lean.Json.mkObj [("triggerKind", (1 : Lean.Json))])
  ]
  send session.child.stdin (mkRequest reqId "textDocument/completion" params)
  let st ← uiStateRef.get
  uiStateRef.set { st with pendingCompletion := st.pendingCompletion.insert reqId (uri, row, col, query) }
  pure { session with nextId := reqId + 1 }

private def startForState (state : EditorState) : IO EditorState := do
  clearFailedSessionIfAny
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
        readerFailureRef.set none
        let child ← startServer state.getCurrentWorkspace.rootPath
        let reader ← IO.asTask (readLoop child.pid child.stdout)
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
        clearFailedSessionIfAny
        return { state with message := s!"Failed to start LSP: {e}" }

private def stopForState (state : EditorState) : IO EditorState := do
  match (← sessionRef.get) with
  | none =>
      return { state with message := "LSP is not running" }
  | some s =>
      try
        let stopped ← terminateSession s
        sessionRef.set none
        readerFailureRef.set none
        resetUiState
        return { state with message := if stopped then "LSP stopped" else "LSP stop timeout; force-detached" }
      catch e =>
        sessionRef.set none
        readerFailureRef.set none
        resetUiState
        return { state with message := s!"LSP stop error: {e}" }

def stopIfRunning : IO Unit := do
  match (← sessionRef.get) with
  | none => pure ()
  | some s =>
      match (← s.child.tryWait) with
      | some _ =>
          sessionRef.set none
          readerFailureRef.set none
          resetUiState
      | none =>
          try
            let _ ← terminateSession s
            sessionRef.set none
            readerFailureRef.set none
            resetUiState
          catch _ =>
            sessionRef.set none
            readerFailureRef.set none
            resetUiState

def syncActiveBufferIfRunning (state : EditorState) : IO Unit := do
  clearFailedSessionIfAny
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
      let (wsClosed, forceQuit) :=
        match infoWindowId with
        | none => (ws, false)
        | some wid =>
            match ws.layout.remove wid with
            | none =>
                (ws, true)
            | some layout' =>
                let ids := ViE.Window.getWindowIds layout'
                let active' :=
                  if ws.activeWindowId == wid then
                    ids.head?.getD ws.activeWindowId
                  else
                    ws.activeWindowId
                ({ ws with layout := layout', activeWindowId := active' }.pruneFloatingWindows, false)
      let wsFinal := { wsClosed with buffers := wsClosed.buffers.filter (fun b => b.id != infoBufId) }
      let s' := state.updateCurrentWorkspace (fun _ => wsFinal)
      if forceQuit then
        { s' with shouldQuit := true }
      else
        s'

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
    | .normal | .visual | .visualLine | .visualBlock =>
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
            let uri ← fileUriWithWorkspace s.rootPath path
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

private def completionIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def completionPrefixStartDisplayCol (line : String) (tabStop cursorCol : Nat) : Nat :=
  let charIdx := ViE.Unicode.displayColToCharIndexWithTabStop line tabStop cursorCol
  let prefixChars : Array Char := (line.toList.take charIdx).toArray
  let startIdx := Id.run do
    let mut i := prefixChars.size
    while i > 0 do
      let j := i - 1
      let c := prefixChars[j]!
      if completionIdentChar c then
        i := j
      else
        return i
    return 0
  let before := String.ofList (prefixChars.toList.take startIdx)
  ViE.Unicode.stringWidthWithTabStop before tabStop

def clearCompletionPopup (state : EditorState) : EditorState :=
  { state with completionPopup := none }

private def clearUiCompletion : IO Unit := do
  let st ← uiStateRef.get
  uiStateRef.set { st with pendingCompletion := Lean.RBMap.empty }

def selectNextCompletion (state : EditorState) : EditorState :=
  match state.completionPopup with
  | none => state
  | some popup =>
      if popup.items.isEmpty then
        { state with completionPopup := none }
      else
        let next := (popup.selected + 1) % popup.items.size
        { state with completionPopup := some { popup with selected := next } }

def selectPrevCompletion (state : EditorState) : EditorState :=
  match state.completionPopup with
  | none => state
  | some popup =>
      if popup.items.isEmpty then
        { state with completionPopup := none }
      else
        let prev := if popup.selected == 0 then popup.items.size - 1 else popup.selected - 1
        { state with completionPopup := some { popup with selected := prev } }

private def applySelectedCompletion (state : EditorState) : EditorState :=
  match state.completionPopup with
  | none => state
  | some popup =>
      if popup.items.isEmpty || popup.selected >= popup.items.size then
        { state with completionPopup := none }
      else
        let item := popup.items[popup.selected]!
        let cursor := state.getCursor
        let line := ViE.getLineFromBuffer state.getActiveBuffer cursor.row |>.getD ""
        let startCol := completionPrefixStartDisplayCol line state.config.tabStop cursor.col.val
        let deleteCount := cursor.col.val - startCol
        let sDeleted := Id.run do
          let mut s := state
          for _ in [0:deleteCount] do
            s := s.deleteBeforeCursor
          return s
        let sInserted := Id.run do
          let mut s := sDeleted
          for c in item.insertText.toList do
            s := s.insertChar c
          return s
        { sInserted with completionPopup := none }

def requestCompletionForActiveIfRunning (state : EditorState) : IO EditorState := do
  let buf := state.getActiveBuffer
  let cursor := state.getCursor
  match buf.filename with
  | none => pure state
  | some path =>
      if !isLeanPath path then
        pure state
      else
        match (← sessionRef.get) with
        | none => pure state
        | some s =>
            match (← s.child.tryWait) with
            | some _ =>
                sessionRef.set none
                pure state
            | none =>
                let lineStr := ViE.getLineFromBuffer buf cursor.row |>.getD ""
                let startCol := completionPrefixStartDisplayCol lineStr state.config.tabStop cursor.col.val
                let startIdx := ViE.Unicode.displayColToCharIndexWithTabStop lineStr state.config.tabStop startCol
                let endIdx := ViE.Unicode.displayColToCharIndexWithTabStop lineStr state.config.tabStop cursor.col.val
                let chars := lineStr.toList
                let query := String.ofList (chars.drop startIdx |>.take (endIdx - startIdx))
                let uri ← fileUriWithWorkspace s.rootPath path
                let line := cursor.row.val
                let lspCol := cursor.col.val
                let s' ← requestCompletion s uri line lspCol cursor.row.val cursor.col.val query
                sessionRef.set (some s')
                pure state

def acceptSelectedCompletion (state : EditorState) : IO EditorState := do
  clearUiCompletion
  let applied := applySelectedCompletion state
  if applied.mode == .insert then
    requestCompletionForActiveIfRunning applied
  else
    pure applied

private def syncCompletionPopupFromUi (state : EditorState) : IO EditorState := do
  let st ← uiStateRef.get
  match st.completion with
  | none => pure state
  | some (uri, popup) =>
      let matchesActive ←
        match state.getActiveBuffer.filename with
        | some path =>
            let activeUri ← fileUriWithWorkspace state.getCurrentWorkspace.rootPath path
            pure (activeUri == uri)
        | none =>
            pure false
      let cursor := state.getCursor
      let sameLine := cursor.row.val == popup.anchorRow
      if state.mode == .insert && matchesActive && sameLine then
        pure { state with completionPopup := some popup }
      else
        pure state

private def formatInfoViewContent (workspaceRoot : Option String) (tabStop : Nat) (sourceView : ViewState) (sourceBuf : FileBuffer) : IO String := do
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

  let uri ←
    match sourceBuf.filename with
    | some p => fileUriWithWorkspace workspaceRoot p
    | none => pure ""
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
  let content ← formatInfoViewContent state.getCurrentWorkspace.rootPath state.config.tabStop sourceView sourceBuf
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
  clearFailedSessionIfAny
  let prevBuf := prevState.getActiveBuffer
  let nextBuf := nextState.getActiveBuffer
  let sameActiveBuffer := prevBuf.id == nextBuf.id
  let textChanged := sameActiveBuffer && prevBuf.table.toString != nextBuf.table.toString
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
  let noCompletion :=
    if nextState.mode != .insert then
      clearCompletionPopup nextState
    else
      nextState
  let infoSynced ← syncInfoViewWindow noCompletion
  let completionRequested ←
    if infoSynced.mode == .insert && isLeanBuffer infoSynced.getActiveBuffer && textChanged then
      requestCompletionForActiveIfRunning infoSynced
    else
      pure infoSynced
  syncCompletionPopupFromUi completionRequested

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
