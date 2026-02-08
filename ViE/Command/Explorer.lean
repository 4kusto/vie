import ViE.State
import ViE.Types
import ViE.Buffer.Manager
import ViE.Buffer.Content
import ViE.Basic
import ViE.State.Config
import ViE.Buffer.LowIO
import ViE.Window.Actions


namespace ViE.Feature

open ViE

def previewMaxBytes : Nat := 65536

def updateExplorerState (state : EditorState) (bufId : Nat) (f : ExplorerState → ExplorerState) : EditorState :=
  { state with explorers := state.explorers.map (fun (id, ex) => if id == bufId then (id, f ex) else (id, ex)) }

def openActiveAsFloating (state : EditorState) : EditorState :=
  state.updateCurrentWorkspace fun ws =>
    (ws.setWindowFloating ws.activeWindowId true).pruneFloatingWindows

def openExplorerWindowsAsFloating (state : EditorState) (previewWindowId : Option Nat) : EditorState :=
  state.updateCurrentWorkspace fun ws =>
    let ws := ws.setWindowFloating ws.activeWindowId true
    let ws :=
      match previewWindowId with
      | some wid =>
          if ws.layout.findView wid |>.isSome then
            ws.setWindowFloating wid true
          else
            ws
      | none => ws
    ws.pruneFloatingWindows

def placeExplorerInWindow (state : EditorState) (bufferId : Nat) (cursorRow : Nat) (reuseActive : Bool) : EditorState :=
  if reuseActive then
    state.updateActiveView fun v =>
      { v with bufferId := bufferId, cursor := {row := ⟨cursorRow⟩, col := 0}, scrollRow := 0, scrollCol := 0 }
  else
    let ws := state.getCurrentWorkspace
    let newWinId := ws.nextWindowId
    let s1 := ViE.Window.splitWindow state false
    s1.updateCurrentWorkspace fun ws =>
      { ws with
          activeWindowId := newWinId,
          layout := ws.layout.updateView newWinId (fun v =>
            { v with bufferId := bufferId, cursor := {row := ⟨cursorRow⟩, col := 0}, scrollRow := 0, scrollCol := 0 })
      }

def openNameInputFloat (state : EditorState) (title : String) (initialText : String) (commandPrefix : String) : EditorState :=
  let ov : FloatingOverlay := {
    title := title
    lines := #[initialText]
    maxWidth := 48
    cursorRow := 0
    cursorCol := initialText.toList.length
  }
  {
    state with
      mode := .normal
      floatingOverlay := some ov
      floatingInputCommand := some commandPrefix
      inputState := {
        state.inputState with
          commandBuffer := ""
          countBuffer := ""
          previousKey := none
          pendingKeys := ""
      }
      message := ""
      dirty := true
  }

def fileExplorerNewFileLabel : String := "[New File]"
def fileExplorerNewDirectoryLabel : String := "[New Directory]"

def isFileExplorerActionEntry (entry : FileEntry) : Bool :=
  entry.name == fileExplorerNewFileLabel || entry.name == fileExplorerNewDirectoryLabel

def fileExplorerActionEntries : List FileEntry := [
  {
    name := fileExplorerNewFileLabel
    path := ""
    isDirectory := false
  },
  {
    name := fileExplorerNewDirectoryLabel
    path := ""
    isDirectory := false
  }
]

def firstNonActionEntryIndex (entries : List FileEntry) : Option Nat :=
  let rec loop (rest : List FileEntry) (idx : Nat) : Option Nat :=
    match rest with
    | [] => none
    | e :: tail =>
        if isFileExplorerActionEntry e then
          loop tail (idx + 1)
        else
          some idx
  loop entries 0

def defaultExplorerCursorRow (entries : List FileEntry) : Nat :=
  match firstNonActionEntryIndex entries with
  | some idx => 2 + idx
  | none => 2

def ensureTrailingSlash (path : String) : String :=
  if path.endsWith "/" then path else path ++ "/"

def getSelectedEntry (state : EditorState) (explorer : ExplorerState) : Option FileEntry :=
  let cursor := state.getCursor
  if cursor.row < 2 then
    none
  else
    let idx := cursor.row - 2
    if idx.val < explorer.entries.length then
      some (explorer.entries[idx.val]!)
    else
      none

def getSelectedIndex (state : EditorState) (explorer : ExplorerState) : Option Nat :=
  let cursor := state.getCursor
  if cursor.row < 2 then
    none
  else
    let idx := cursor.row - 2
    if idx.val < explorer.entries.length then
      some idx.val
    else
      none

def buildWorkspacePreviewLines (ws : WorkspaceState) : List String :=
  let header := [s!"Workspace: {ws.name}", ""]
  let entries := ws.buffers.map fun b =>
    match b.filename with
    | some name => name
    | none => s!"[Untitled:{b.id}]"
  if entries.isEmpty then
    header ++ ["(no buffers)"]
  else
    header ++ entries

def buildWorkgroupPreviewLines (wg : WorkgroupState) : List String :=
  let header := [s!"Workgroup: {wg.name}", ""]
  let entries := wg.workspaces.toList.map (fun ws => ws.name)
  if entries.isEmpty then
    header ++ ["(no workspaces)"]
  else
    header ++ entries

def bufferEntryPrefix : String := "buffer://"

def makeBufferEntryPath (bufferId : Nat) : String :=
  s!"{bufferEntryPrefix}{bufferId}"

def parseBufferEntryId (path : String) : Option Nat :=
  if path.startsWith bufferEntryPrefix then
    (path.drop bufferEntryPrefix.length).toString.toNat?
  else
    none

def selectedBufferIdFromExplorer (state : EditorState) (explorer : ExplorerState) : Option Nat :=
  match getSelectedEntry state explorer with
  | none => none
  | some entry =>
      match parseBufferEntryId entry.path with
      | none => none
      | some bid =>
          let ws := state.getCurrentWorkspace
          if ws.buffers.any (fun b => b.id == bid) then
            some bid
          else
            none

def bufferExplorerLabel (buf : FileBuffer) : String :=
  let name := buf.filename.getD s!"[No Name:{buf.id}]"
  let dirty := if buf.dirty then " [+]" else ""
  s!"[{buf.id}] {name}{dirty}"

def ensurePreviewTextBuffer (state : EditorState) (explorer : ExplorerState) (title : String) (lines : List String) : (EditorState × Nat) :=
  let content : TextBuffer := if lines.isEmpty then #[#[]] else lines.toArray.map stringToLine
  let buildLeafBits := state.config.searchBloomBuildLeafBits
  let buf := { ViE.Buffer.fileBufferFromTextBufferWithConfig 0 (some s!"preview://{title}") content buildLeafBits with dirty := false }
  match explorer.previewBufferId with
  | some pid =>
    let ws := state.getCurrentWorkspace
    if ws.buffers.any (fun b => b.id == pid) then
      let updated := { buf with id := pid }
      let s' := state.updateCurrentWorkspace fun ws =>
        { ws with buffers := ws.buffers.map (fun b => if b.id == pid then updated else b) }
      (s', pid)
    else
      let (pid, s') := ViE.Buffer.addBuffer state buf
      (s', pid)
  | none =>
    let (pid, s') := ViE.Buffer.addBuffer state buf
    (s', pid)

def getPreviewWorkspace (state : EditorState) (explorer : ExplorerState) : WorkspaceState :=
  let wg := state.getCurrentWorkgroup
  match getSelectedIndex state explorer with
  | some idx =>
    if idx >= 2 then
      let real := idx - 2
      if real < wg.workspaces.size then
        wg.workspaces[real]!
      else
        state.getCurrentWorkspace
    else
      state.getCurrentWorkspace
  | none => state.getCurrentWorkspace

def getPreviewWorkgroup (state : EditorState) (explorer : ExplorerState) : WorkgroupState :=
  match getSelectedIndex state explorer with
  | some idx =>
    if idx >= 2 then
      let real := idx - 2
      if real < state.workgroups.size then
        state.workgroups[real]!
      else
        state.getCurrentWorkgroup
    else
      state.getCurrentWorkgroup
  | none => state.getCurrentWorkgroup

def ensurePreviewBuffer (state : EditorState) (explorer : ExplorerState) (entry : FileEntry) : IO (EditorState × Nat) := do
  let resolved := entry.path
  let loaded ← ViE.loadPreviewBufferByteArrayWithConfig resolved previewMaxBytes state.config
  let previewName := some s!"preview://{resolved}"
  let previewBuf := { loaded with filename := previewName, dirty := false }

  match explorer.previewBufferId with
  | some pid =>
    let ws := state.getCurrentWorkspace
    if ws.buffers.any (fun b => b.id == pid) then
      let updated := { previewBuf with id := pid }
      let s' := state.updateCurrentWorkspace fun ws =>
        { ws with buffers := ws.buffers.map (fun b => if b.id == pid then updated else b) }
      return (s', pid)
    else
      let (pid, s') := ViE.Buffer.addBuffer state previewBuf
      return (s', pid)
  | none =>
    let (pid, s') := ViE.Buffer.addBuffer state previewBuf
    return (s', pid)

def refreshExplorerPreview (state : EditorState) : IO EditorState := do
  let buf := state.getActiveBuffer
  let explorerOpt := state.explorers.find? (fun (id, _) => id == buf.id)
  match explorerOpt with
  | none => return state
  | some (bufId, explorer) =>
    match explorer.previewWindowId with
    | none => return state
    | some previewWinId =>
      match explorer.mode with
      | .files =>
        match getSelectedEntry state explorer with
        | none => return state
        | some entry =>
          if isFileExplorerActionEntry entry then
            return state
          else if entry.isDirectory then
            return state
          else
            let (s1, previewBufId) ← ensurePreviewBuffer state explorer entry
            let s2 := s1.updateCurrentWorkspace fun ws =>
              { ws with layout := ws.layout.updateView previewWinId (fun v =>
                { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
            let s3 := updateExplorerState s2 bufId (fun ex => { ex with previewBufferId := some previewBufId })
            return s3
      | .workspaces =>
          let ws := getPreviewWorkspace state explorer
          let lines := buildWorkspacePreviewLines ws
          let (s1, previewBufId) := ensurePreviewTextBuffer state explorer ws.name lines
          let s2 := s1.updateCurrentWorkspace fun ws =>
            { ws with layout := ws.layout.updateView previewWinId (fun v =>
              { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
          let s3 := updateExplorerState s2 bufId (fun ex => { ex with previewBufferId := some previewBufId })
          return s3
      | .workgroups =>
          let wg := getPreviewWorkgroup state explorer
          let lines := buildWorkgroupPreviewLines wg
          let (s1, previewBufId) := ensurePreviewTextBuffer state explorer wg.name lines
          let s2 := s1.updateCurrentWorkspace fun ws =>
            { ws with layout := ws.layout.updateView previewWinId (fun v =>
              { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
          let s3 := updateExplorerState s2 bufId (fun ex => { ex with previewBufferId := some previewBufId })
          return s3
      | .buffers =>
          match selectedBufferIdFromExplorer state explorer with
          | none => return state
          | some previewBufId =>
              let s1 := state.updateCurrentWorkspace fun ws =>
                { ws with layout := ws.layout.updateView previewWinId (fun v =>
                  { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
              let s2 := updateExplorerState s1 bufId (fun ex => { ex with previewBufferId := none })
              return s2

def openExplorerDefaultPreview (state : EditorState) (bufId : Nat) (explorer : ExplorerState) : IO EditorState := do
  match explorer.previewWindowId with
  | some _ => return state
  | none =>
    let ws := state.getCurrentWorkspace
    let previewWinId := ws.nextWindowId
    let s1 := ViE.Window.splitWindow state false
    let (s2, previewBufId) ←
      match explorer.mode with
      | .files =>
        let selected := getSelectedEntry s1 explorer
        let entryOpt : Option FileEntry :=
          match selected with
          | some e =>
              if isFileExplorerActionEntry e then
                explorer.entries.find? (fun x => !isFileExplorerActionEntry x)
              else
                some e
          | none =>
              explorer.entries.find? (fun x => !isFileExplorerActionEntry x)
        match entryOpt with
        | some entry =>
            if entry.isDirectory then
              let content : TextBuffer := #[#[]]
              let buildLeafBits := s1.config.searchBloomBuildLeafBits
              let buf := { ViE.Buffer.fileBufferFromTextBufferWithConfig 0 (some "preview://") content buildLeafBits with dirty := false }
              let (pid, s2) := ViE.Buffer.addBuffer s1 buf
              pure (s2, pid)
            else
              ensurePreviewBuffer s1 explorer entry
        | none =>
            let content : TextBuffer := #[#[]]
            let buildLeafBits := s1.config.searchBloomBuildLeafBits
            let buf := { ViE.Buffer.fileBufferFromTextBufferWithConfig 0 (some "preview://") content buildLeafBits with dirty := false }
            let (pid, s2) := ViE.Buffer.addBuffer s1 buf
            pure (s2, pid)
      | .workspaces =>
        let ws := getPreviewWorkspace s1 explorer
        let lines := buildWorkspacePreviewLines ws
        let (s2, pid) := ensurePreviewTextBuffer s1 explorer ws.name lines
        pure (s2, pid)
      | .workgroups =>
        let wg := getPreviewWorkgroup s1 explorer
        let lines := buildWorkgroupPreviewLines wg
        let (s2, pid) := ensurePreviewTextBuffer s1 explorer wg.name lines
        pure (s2, pid)
      | .buffers =>
        let fallbackBufId :=
          match explorer.entries.find? (fun e => (parseBufferEntryId e.path).isSome) with
          | some e => (parseBufferEntryId e.path).getD s1.getActiveBuffer.id
          | none => s1.getActiveBuffer.id
        let previewBufId := (selectedBufferIdFromExplorer s1 explorer).getD fallbackBufId
        pure (s1, previewBufId)
    let s3 := s2.updateCurrentWorkspace fun ws =>
      { ws with layout := ws.layout.updateView previewWinId (fun v =>
        { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
    let s4 := updateExplorerState s3 bufId (fun ex =>
      {
        ex with
          previewWindowId := some previewWinId
          previewBufferId := if explorer.mode == .buffers then none else some previewBufId
      })
    return openExplorerWindowsAsFloating s4 (some previewWinId)

def toggleExplorerPreview (state : EditorState) : IO EditorState := do
  let buf := state.getActiveBuffer
  let explorerOpt := state.explorers.find? (fun (id, _) => id == buf.id)
  match explorerOpt with
  | none => return state
  | some (bufId, explorer) =>
    match explorer.previewWindowId with
    | some previewWinId =>
      let s1 := state.updateCurrentWorkspace fun ws =>
        match ws.layout.remove previewWinId with
        | some newLayout => ({ ws with layout := newLayout }).pruneFloatingWindows
        | none => ws.pruneFloatingWindows
      let s2 := updateExplorerState s1 bufId (fun ex => { ex with previewWindowId := none, previewBufferId := none })
      return { s2 with message := "Preview closed" }
    | none =>
      match explorer.mode with
      | .files =>
        match getSelectedEntry state explorer with
        | none => return { state with message := "Preview: no selection" }
        | some entry =>
          if entry.isDirectory then
            return { state with message := "Preview: directory" }
          else
            let ws := state.getCurrentWorkspace
            let previewWinId := ws.nextWindowId
            let s1 := ViE.Window.splitWindow state false
            let (s2, previewBufId) ← ensurePreviewBuffer s1 explorer entry
            let s3 := s2.updateCurrentWorkspace fun ws =>
              { ws with layout := ws.layout.updateView previewWinId (fun v =>
                { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
            let s4 := updateExplorerState s3 bufId (fun ex => { ex with previewWindowId := some previewWinId, previewBufferId := some previewBufId })
            let s5 := openExplorerWindowsAsFloating s4 (some previewWinId)
            return { s5 with message := "Preview opened" }
      | .workspaces =>
          let ws := state.getCurrentWorkspace
          let previewWinId := ws.nextWindowId
          let s1 := ViE.Window.splitWindow state false
          let previewWs := getPreviewWorkspace s1 explorer
          let lines := buildWorkspacePreviewLines previewWs
          let (s2, previewBufId) := ensurePreviewTextBuffer s1 explorer previewWs.name lines
          let s3 := s2.updateCurrentWorkspace fun ws =>
            { ws with layout := ws.layout.updateView previewWinId (fun v =>
              { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
          let s4 := updateExplorerState s3 bufId (fun ex => { ex with previewWindowId := some previewWinId, previewBufferId := some previewBufId })
          let s5 := openExplorerWindowsAsFloating s4 (some previewWinId)
          return { s5 with message := "Preview opened" }
      | .workgroups =>
          let ws := state.getCurrentWorkspace
          let previewWinId := ws.nextWindowId
          let s1 := ViE.Window.splitWindow state false
          let previewWg := getPreviewWorkgroup s1 explorer
          let lines := buildWorkgroupPreviewLines previewWg
          let (s2, previewBufId) := ensurePreviewTextBuffer s1 explorer previewWg.name lines
          let s3 := s2.updateCurrentWorkspace fun ws =>
            { ws with layout := ws.layout.updateView previewWinId (fun v =>
              { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
          let s4 := updateExplorerState s3 bufId (fun ex => { ex with previewWindowId := some previewWinId, previewBufferId := some previewBufId })
          let s5 := openExplorerWindowsAsFloating s4 (some previewWinId)
          return { s5 with message := "Preview opened" }
      | .buffers =>
          match selectedBufferIdFromExplorer state explorer with
          | none =>
              return { state with message := "Preview: no buffer selection" }
          | some previewBufId =>
              let ws := state.getCurrentWorkspace
              let previewWinId := ws.nextWindowId
              let s1 := ViE.Window.splitWindow state false
              let s2 := s1.updateCurrentWorkspace fun ws =>
                { ws with layout := ws.layout.updateView previewWinId (fun v =>
                  { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
              let s3 := updateExplorerState s2 bufId (fun ex => { ex with previewWindowId := some previewWinId, previewBufferId := none })
              let s4 := openExplorerWindowsAsFloating s3 (some previewWinId)
              return { s4 with message := "Preview opened" }

/-- Open the file explorer at the specified path (or current workspace root) -/
def openExplorer (state : EditorState) (pathArg : String) : IO EditorState := do
  let ws := state.getCurrentWorkspace
  let path := if pathArg == "." || pathArg == "" then
                ws.rootPath.getD "."
              else if pathArg.startsWith "/" then
                pathArg
              else
                match ws.rootPath with
                | some root =>
                  if pathArg == root then root else root ++ "/" ++ pathArg
                | none => pathArg

  -- Read directory contents
  try
    let dirPath := System.FilePath.mk path
    let entries := (← System.FilePath.readDir dirPath).toList
    let mut navEntries : List FileEntry := []

    -- Add parent directory entry if not at root
    if path != "/" then
      let parentPath := match dirPath.parent with
        | some p => p.toString
        | none => "/"
      navEntries := navEntries ++ [{
        name := ".."
        path := parentPath
        isDirectory := true
      }]

    -- Convert directory entries to FileEntry
    for entry in entries do
      let entryPath := entry.path.toString
      let isDir ← entry.path.isDir
      navEntries := navEntries ++ [{
        name := entry.fileName
        path := entryPath
        isDirectory := isDir
      }]

    -- Sort: directories first, then files, alphabetically
    let sortedEntries := navEntries.toArray.qsort fun a b =>
      if a.isDirectory != b.isDirectory then
        a.isDirectory -- directories first
      else
        a.name < b.name
    let allEntries := fileExplorerActionEntries ++ sortedEntries.toList

    -- Create explorer state
    let explorerState : ExplorerState := {
      currentPath := path
      entries := allEntries
      selectedIndex := 0
      mode := .files
      previewWindowId := none
      previewBufferId := none
    }

    -- Generate buffer content
    let header := [s!"Explorer: {path}", ""]
    let mut content := header
    let mut idx := 0
    for entry in explorerState.entries do
      let pref := if idx == 0 then "> " else "  "
      let isAction := isFileExplorerActionEntry entry
      let icon :=
        if isAction then ""
        else if entry.isDirectory then state.config.dirIcon
        else state.config.fileIcon
      let suffix := if !isAction && entry.isDirectory then "/" else ""
      content := content ++ [s!"{pref}{icon}{entry.name}{suffix}"]
      idx := idx + 1
     -- Create new buffer
    let contentBuffer := content.toArray.map stringToLine
    let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some s!"explorer://{path}")

    -- Register explorer
    let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }

    -- Open explorer in a dedicated window by default; reuse active only when already in explorer.
    let reuseActive := state.explorers.any (fun (id, _) => id == state.getActiveBuffer.id)
    let s''' := placeExplorerInWindow s'' bufferId (defaultExplorerCursorRow explorerState.entries) reuseActive
    let s'''' := { s''' with message := s!"Explorer: {path}" }
    let s''''' := openActiveAsFloating s''''

    -- Auto-open preview by default for file explorer
    return (← openExplorerDefaultPreview s''''' bufferId explorerState)

  catch e =>
    return { state with message := s!"Error reading directory: {e}" }

def openExplorerWithPreview (state : EditorState) (pathArg : String) (previewWindowId : Option Nat) (previewBufferId : Option Nat) : IO EditorState := do
  let ws := state.getCurrentWorkspace
  let path := if pathArg == "." || pathArg == "" then
                ws.rootPath.getD "."
              else if pathArg.startsWith "/" then
                pathArg
              else
                match ws.rootPath with
                | some root =>
                  if pathArg == root then root else root ++ "/" ++ pathArg
                | none => pathArg

  try
    let dirPath := System.FilePath.mk path
    let entries := (← System.FilePath.readDir dirPath).toList
    let mut navEntries : List FileEntry := []

    if path != "/" then
      let parentPath := match dirPath.parent with
        | some p => p.toString
        | none => "/"
      navEntries := navEntries ++ [{
        name := ".."
        path := parentPath
        isDirectory := true
      }]

    for entry in entries do
      let entryPath := entry.path.toString
      let isDir ← entry.path.isDir
      navEntries := navEntries ++ [{
        name := entry.fileName
        path := entryPath
        isDirectory := isDir
      }]

    let sortedEntries := navEntries.toArray.qsort fun a b =>
      if a.isDirectory != b.isDirectory then
        a.isDirectory
      else
        a.name < b.name
    let allEntries := fileExplorerActionEntries ++ sortedEntries.toList

    let explorerState : ExplorerState := {
      currentPath := path
      entries := allEntries
      selectedIndex := 0
      mode := .files
      previewWindowId := previewWindowId
      previewBufferId := previewBufferId
    }

    let header := [s!"Explorer: {path}", ""]
    let mut content := header
    let mut idx := 0
    for entry in explorerState.entries do
      let pref := if idx == 0 then "> " else "  "
      let isAction := isFileExplorerActionEntry entry
      let icon :=
        if isAction then ""
        else if entry.isDirectory then state.config.dirIcon
        else state.config.fileIcon
      let suffix := if !isAction && entry.isDirectory then "/" else ""
      content := content ++ [s!"{pref}{icon}{entry.name}{suffix}"]
      idx := idx + 1
    let contentBuffer := content.toArray.map stringToLine
    let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some s!"explorer://{path}")

    let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }
    let reuseActive := state.explorers.any (fun (id, _) => id == state.getActiveBuffer.id)
    let s''' := placeExplorerInWindow s'' bufferId (defaultExplorerCursorRow explorerState.entries) reuseActive
    let s'''' := { s''' with message := s!"Explorer: {path}" }
    let s''''' := openActiveAsFloating s''''

    match previewWindowId with
    | some wid => refreshExplorerPreview (openExplorerWindowsAsFloating s''''' (some wid))
    | none => openExplorerDefaultPreview s''''' bufferId explorerState
  catch e =>
    return { state with message := s!"Error reading directory: {e}" }

/-- Open the workspace explorer to list workspaces. -/
def openWorkspaceExplorer (state : EditorState) : IO EditorState := do
  let wg := state.getCurrentWorkgroup
  let mut entries : List FileEntry := []
  entries := entries ++ [{
    name := "[New Workspace]"
    path := ""
    isDirectory := false
  }]
  entries := entries ++ [{
    name := "[Rename Workspace]"
    path := ""
    isDirectory := false
  }]
  for ws in wg.workspaces.toList do
    let label :=
      match ws.rootPath with
      | some root => s!"{ws.name} — {root}"
      | none => ws.name
    entries := entries ++ [{
      name := label
      path := ws.rootPath.getD ""
      isDirectory := true
    }]

  let explorerState : ExplorerState := {
    currentPath := s!"workgroup:{wg.name}"
    entries := entries
    selectedIndex := 0
    mode := .workspaces
    previewWindowId := none
    previewBufferId := none
  }

  let header := [s!"Workspace Explorer: {wg.name}", ""]
  let mut content := header
  let mut idx := 0
  for entry in explorerState.entries do
    let pref := if idx == 0 then "> " else "  "
    let mark := if idx == (wg.currentWorkspace + 1) then "* " else "  "
    let icon := if entry.isDirectory then state.config.dirIcon else state.config.fileIcon
    content := content ++ [s!"{pref}{mark}{icon}{entry.name}"]
    idx := idx + 1

  let contentBuffer := content.toArray.map stringToLine
  let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some "explorer://workgroup")
  let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }
  let reuseActive := state.explorers.any (fun (id, _) => id == state.getActiveBuffer.id)
  let s''' := placeExplorerInWindow s'' bufferId 2 reuseActive
  let s'''' := { s''' with message := s!"Workspace Explorer: {wg.name}" }
  let s''''' := openActiveAsFloating s''''
  return (← openExplorerDefaultPreview s''''' bufferId explorerState)

/-- Open the workgroup explorer to list workgroups. -/
def openWorkgroupExplorer (state : EditorState) : IO EditorState := do
  let mut entries : List FileEntry := []
  entries := entries ++ [{
    name := "[New Workgroup]"
    path := ""
    isDirectory := false
  }]
  entries := entries ++ [{
    name := "[Rename Workgroup]"
    path := ""
    isDirectory := false
  }]
  for wg in state.workgroups.toList do
    entries := entries ++ [{
      name := wg.name
      path := ""
      isDirectory := true
    }]

  let explorerState : ExplorerState := {
    currentPath := "workgroups"
    entries := entries
    selectedIndex := 0
    mode := .workgroups
    previewWindowId := none
    previewBufferId := none
  }

  let header := ["Workgroup Explorer", ""]
  let mut content := header
  let mut idx := 0
  for entry in explorerState.entries do
    let pref := if idx == explorerState.selectedIndex then "> " else "  "
    let mark := if idx == (state.currentGroup + 1) then "* " else "  "
    let icon := if entry.isDirectory then state.config.dirIcon else state.config.fileIcon
    content := content ++ [s!"{pref}{mark}{icon}{entry.name}"]
    idx := idx + 1

  let contentBuffer := content.toArray.map stringToLine
  let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some "explorer://workgroups")
  let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }
  let reuseActive := state.explorers.any (fun (id, _) => id == state.getActiveBuffer.id)
  let s''' := placeExplorerInWindow s'' bufferId (2 + explorerState.selectedIndex) reuseActive
  let s'''' := { s''' with message := "Workgroup Explorer" }
  let s''''' := openActiveAsFloating s''''
  return (← openExplorerDefaultPreview s''''' bufferId explorerState)

/-- Open the buffer explorer to list currently opened workspace buffers. -/
def openBufferExplorer (state : EditorState) : IO EditorState := do
  let ws := state.getCurrentWorkspace
  let explorerBufIds := state.explorers.map (fun (id, _) => id)
  let previewBufIds := state.explorers.filterMap (fun (_, ex) => ex.previewBufferId)
  let skipBufferId (bid : Nat) : Bool :=
    explorerBufIds.contains bid || previewBufIds.contains bid
  let candidates := ws.buffers.filter (fun b => !skipBufferId b.id)
  if candidates.isEmpty then
    return { state with message := "No open buffers" }
  let sortedBuffers := (candidates.toArray.qsort fun a b => a.id < b.id).toList
  let entries := sortedBuffers.map fun b =>
    {
      name := bufferExplorerLabel b
      path := makeBufferEntryPath b.id
      isDirectory := false
    }
  let activeBufferId := state.getActiveBuffer.id
  let rec findSelectedIndex (rest : List FileEntry) (idx : Nat) : Nat :=
    match rest with
    | [] => 0
    | entry :: tail =>
        if parseBufferEntryId entry.path == some activeBufferId then
          idx
        else
          findSelectedIndex tail (idx + 1)
  let selectedIndex := findSelectedIndex entries 0

  let explorerState : ExplorerState := {
    currentPath := "buffers"
    entries := entries
    selectedIndex := selectedIndex
    mode := .buffers
    previewWindowId := none
    previewBufferId := none
  }

  let header := [s!"Buffer Explorer: {ws.name}", ""]
  let mut content := header
  let mut idx := 0
  for entry in explorerState.entries do
    let pref := if idx == explorerState.selectedIndex then "> " else "  "
    let mark :=
      if parseBufferEntryId entry.path == some activeBufferId then
        "* "
      else
        "  "
    content := content ++ [s!"{pref}{mark}{state.config.fileIcon}{entry.name}"]
    idx := idx + 1

  let contentBuffer := content.toArray.map stringToLine
  let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some "explorer://buffers")
  let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }
  let reuseActive := state.explorers.any (fun (id, _) => id == state.getActiveBuffer.id)
  let s''' := placeExplorerInWindow s'' bufferId (2 + explorerState.selectedIndex) reuseActive
  let s'''' := { s''' with message := "Buffer Explorer" }
  let s''''' := openActiveAsFloating s''''
  return (← openExplorerDefaultPreview s''''' bufferId explorerState)

/-- Handle Enter key in explorer buffer -/
def handleExplorerEnter (state : EditorState) : IO EditorState := do
  let buf := state.getActiveBuffer

  -- Check if this is an explorer buffer
  let explorerOpt := state.explorers.find? (fun (id, _) => id == buf.id)

  match explorerOpt with
  | none =>
    match state.searchState with
    | some _ => return ViE.findNextMatch state
    | none => return state.moveCursorDown
  | some (_, explorer) =>
    -- Get current cursor row
    let cursor := state.getCursor
    if cursor.row < 2 then return state -- Header rows

    -- Explorer header is 2 lines, so subtract 2
    let selectedIdx := cursor.row - 2

    if selectedIdx.val >= explorer.entries.length then
      return state

    match explorer.mode with
    | .files =>
      -- Get selected entry
      let entry := explorer.entries[selectedIdx.val]!

      if entry.name == fileExplorerNewFileLabel then
        let cmdPrefix := s!"mkfile {ensureTrailingSlash explorer.currentPath}"
        return openNameInputFloat state "New File" "" cmdPrefix
      else if entry.name == fileExplorerNewDirectoryLabel then
        let cmdPrefix := s!"mkdir {ensureTrailingSlash explorer.currentPath}"
        return openNameInputFloat state "New Directory" "" cmdPrefix
      else if entry.isDirectory then
        -- Navigate to directory
        openExplorerWithPreview state entry.path explorer.previewWindowId explorer.previewBufferId
      else
        let ws0 := state.getCurrentWorkspace
        let explorerWinId := ws0.activeWindowId
        let explorerBufIds := state.explorers.map (fun (id, _) => id)
        let targetWinOpt :=
          let ids := ViE.Window.getWindowIds ws0.layout
          ids.find? fun wid =>
            if wid == explorerWinId then
              false
            else if explorer.previewWindowId == some wid then
              false
            else
              match ws0.layout.findView wid with
              | some v =>
                  let isExplorerBuf := explorerBufIds.contains v.bufferId
                  let isPreviewBuf :=
                    match explorer.previewBufferId with
                    | some pid => v.bufferId == pid
                    | none => false
                  !isExplorerBuf && !isPreviewBuf
              | none => false

        -- Close preview and unregister explorer metadata.
        let s1 :=
          match explorer.previewWindowId with
          | none => state
          | some previewId =>
              let s1 := state.updateCurrentWorkspace fun ws =>
                match ws.layout.remove previewId with
                | some newLayout => ({ ws with layout := newLayout }).pruneFloatingWindows
                | none => ws.pruneFloatingWindows
              let s2 := updateExplorerState s1 buf.id (fun ex => { ex with previewWindowId := none, previewBufferId := none })
              match explorer.previewBufferId with
              | some previewBufId => ViE.Buffer.removeBuffer s2 previewBufId
              | none => s2
        let s1 := { s1 with explorers := s1.explorers.filter (fun (id, _) => id != buf.id) }

        match targetWinOpt with
        | some targetWinId =>
            let s2 := s1.updateCurrentWorkspace fun ws =>
              match ws.layout.remove explorerWinId with
              | some newLayout =>
                  let ids := ViE.Window.getWindowIds newLayout
                  let activeId :=
                    if ids.contains targetWinId then
                      targetWinId
                    else
                      match ids with
                      | h :: _ => h
                      | [] => ws.activeWindowId
                  ({ ws with layout := newLayout, activeWindowId := activeId }).pruneFloatingWindows
              | none =>
                  ws.pruneFloatingWindows
            let s3 := ViE.Buffer.removeBuffer s2 buf.id
            let opened ← ViE.Buffer.openBuffer s3 entry.path
            return opened
        | none =>
            let opened ← ViE.Buffer.openBuffer s1 entry.path
            let s2 := opened.updateCurrentWorkspace fun ws =>
              (ws.setWindowFloating ws.activeWindowId false).pruneFloatingWindows
            let s3 := ViE.Buffer.removeBuffer s2 buf.id
            return s3
    | .buffers =>
      let entry := explorer.entries[selectedIdx.val]!
      match parseBufferEntryId entry.path with
      | none =>
          return { state with message := "Invalid buffer entry" }
      | some targetBufId =>
          let ws0 := state.getCurrentWorkspace
          if !ws0.buffers.any (fun b => b.id == targetBufId) then
            return { state with message := s!"Buffer not found: {targetBufId}" }
          else
            let explorerWinId := ws0.activeWindowId
            let explorerBufIds := state.explorers.map (fun (id, _) => id)
            let targetWinOpt :=
              let ids := ViE.Window.getWindowIds ws0.layout
              ids.find? fun wid =>
                if wid == explorerWinId then
                  false
                else if explorer.previewWindowId == some wid then
                  false
                else
                  match ws0.layout.findView wid with
                  | some v =>
                      let isExplorerBuf := explorerBufIds.contains v.bufferId
                      !isExplorerBuf
                  | none => false

            let targetLabel :=
              match ws0.buffers.find? (fun b => b.id == targetBufId) with
              | some b => b.filename.getD s!"[No Name:{targetBufId}]"
              | none => s!"[No Name:{targetBufId}]"

            -- Close preview and unregister explorer metadata.
            let s1 :=
              match explorer.previewWindowId with
              | none => state
              | some previewId =>
                  let s1 := state.updateCurrentWorkspace fun ws =>
                    match ws.layout.remove previewId with
                    | some newLayout => ({ ws with layout := newLayout }).pruneFloatingWindows
                    | none => ws.pruneFloatingWindows
                  updateExplorerState s1 buf.id (fun ex => { ex with previewWindowId := none, previewBufferId := none })
            let s1 := { s1 with explorers := s1.explorers.filter (fun (id, _) => id != buf.id) }

            match targetWinOpt with
            | some targetWinId =>
                let s2 := s1.updateCurrentWorkspace fun ws =>
                  match ws.layout.remove explorerWinId with
                  | some newLayout =>
                      let ids := ViE.Window.getWindowIds newLayout
                      let activeId :=
                        if ids.contains targetWinId then
                          targetWinId
                        else
                          match ids with
                          | h :: _ => h
                          | [] => ws.activeWindowId
                      ({ ws with layout := newLayout, activeWindowId := activeId }).pruneFloatingWindows
                  | none =>
                      ws.pruneFloatingWindows
                let s3 := ViE.Buffer.removeBuffer s2 buf.id
                let s4 := s3.updateActiveView fun v =>
                  { v with bufferId := targetBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }
                return { s4 with message := s!"Switched to buffer: {targetLabel}" }
            | none =>
                let s2 := s1.updateActiveView fun v =>
                  { v with bufferId := targetBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }
                let s3 := s2.updateCurrentWorkspace fun ws =>
                  (ws.setWindowFloating ws.activeWindowId false).pruneFloatingWindows
                let s4 := ViE.Buffer.removeBuffer s3 buf.id
                return { s4 with message := s!"Switched to buffer: {targetLabel}" }
    | .workgroups =>
      let idx := selectedIdx.val
      if idx == 0 then
        return openNameInputFloat state "New Workgroup" "" "wg new "
      else if idx == 1 then
        let current := state.getCurrentWorkgroup.name
        return openNameInputFloat state "Rename Workgroup" current "wg rename "
      else
        let realIdx := idx - 2
        if realIdx < state.workgroups.size then
          let s' := { state with currentGroup := realIdx }
          let wg := s'.getCurrentWorkgroup
          return { s' with message := s!"Switched workgroup: {wg.name}" }
        else
          return state
    | .workspaces =>
      let idx := selectedIdx.val
      if idx == 0 then
        return openNameInputFloat state "New Workspace" "" "ws new "
      else if idx == 1 then
        let current := state.getCurrentWorkspace.name
        return openNameInputFloat state "Rename Workspace" current "ws rename "
      else
        let realIdx := idx - 2
        let s' := state.updateCurrentWorkgroup fun wg =>
          if realIdx < wg.workspaces.size then
            { wg with currentWorkspace := realIdx }
          else
            wg
        let ws := s'.getCurrentWorkspace
        return { s' with message := s!"Switched workspace: {ws.name}" }

end ViE.Feature
