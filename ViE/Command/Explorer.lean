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
          if entry.isDirectory then
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
        let entryOpt := getSelectedEntry s1 explorer
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
    let s3 := s2.updateCurrentWorkspace fun ws =>
      { ws with layout := ws.layout.updateView previewWinId (fun v =>
        { v with bufferId := previewBufId, cursor := Point.zero, scrollRow := 0, scrollCol := 0 }) }
    let s4 := updateExplorerState s3 bufId (fun ex =>
      { ex with previewWindowId := some previewWinId, previewBufferId := some previewBufId })
    return s4

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
        | some newLayout => { ws with layout := newLayout }
        | none => ws
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
            return { s4 with message := "Preview opened" }
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
          return { s4 with message := "Preview opened" }
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
    let mut fileEntries : List FileEntry := []

    -- Add parent directory entry if not at root
    if path != "/" then
      let parentPath := match dirPath.parent with
        | some p => p.toString
        | none => "/"
      fileEntries := fileEntries ++ [{
        name := ".."
        path := parentPath
        isDirectory := true
      }]

    -- Convert directory entries to FileEntry
    for entry in entries do
      let entryPath := entry.path.toString
      let isDir ← entry.path.isDir
      fileEntries := fileEntries ++ [{
        name := entry.fileName
        path := entryPath
        isDirectory := isDir
      }]

    -- Sort: directories first, then files, alphabetically
    let sortedEntries := fileEntries.toArray.qsort fun a b =>
      if a.isDirectory != b.isDirectory then
        a.isDirectory -- directories first
      else
        a.name < b.name

    -- Create explorer state
    let explorerState : ExplorerState := {
      currentPath := path
      entries := sortedEntries.toList
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
      let icon := if entry.isDirectory then state.config.dirIcon else state.config.fileIcon
      let suffix := if entry.isDirectory then "/" else ""
      content := content ++ [s!"{pref}{icon}{entry.name}{suffix}"]
      idx := idx + 1
     -- Create new buffer
    let contentBuffer := content.toArray.map stringToLine
    let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some s!"explorer://{path}")

    -- Register explorer
    let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }

    -- Switch to explorer buffer
    let s''' := s''.updateActiveView fun v => { v with bufferId := bufferId, cursor := {row := 2, col := 0}, scrollRow := 0, scrollCol := 0 }
    let s'''' := { s''' with message := s!"Explorer: {path}" }

    -- Auto-open preview by default for file explorer
    return (← openExplorerDefaultPreview s'''' bufferId explorerState)

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
    let mut fileEntries : List FileEntry := []

    if path != "/" then
      let parentPath := match dirPath.parent with
        | some p => p.toString
        | none => "/"
      fileEntries := fileEntries ++ [{
        name := ".."
        path := parentPath
        isDirectory := true
      }]

    for entry in entries do
      let entryPath := entry.path.toString
      let isDir ← entry.path.isDir
      fileEntries := fileEntries ++ [{
        name := entry.fileName
        path := entryPath
        isDirectory := isDir
      }]

    let sortedEntries := fileEntries.toArray.qsort fun a b =>
      if a.isDirectory != b.isDirectory then
        a.isDirectory
      else
        a.name < b.name

    let explorerState : ExplorerState := {
      currentPath := path
      entries := sortedEntries.toList
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
      let icon := if entry.isDirectory then state.config.dirIcon else state.config.fileIcon
      let suffix := if entry.isDirectory then "/" else ""
      content := content ++ [s!"{pref}{icon}{entry.name}{suffix}"]
      idx := idx + 1
    let contentBuffer := content.toArray.map stringToLine
    let (bufferId, s') := ViE.Buffer.createNewBuffer state contentBuffer (some s!"explorer://{path}")

    let s'' := { s' with explorers := (bufferId, explorerState) :: s'.explorers }
    let s''' := s''.updateActiveView fun v => { v with bufferId := bufferId, cursor := {row := 2, col := 0}, scrollRow := 0, scrollCol := 0 }
    let s'''' := { s''' with message := s!"Explorer: {path}" }

    match previewWindowId with
    | some _ => refreshExplorerPreview s''''
    | none => openExplorerDefaultPreview s'''' bufferId explorerState
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
  let s''' := s''.updateActiveView fun v => { v with bufferId := bufferId, cursor := {row := 2, col := 0}, scrollRow := 0, scrollCol := 0 }
  let s'''' := { s''' with message := s!"Workspace Explorer: {wg.name}" }
  return (← openExplorerDefaultPreview s'''' bufferId explorerState)

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
  let s''' := s''.updateActiveView fun v =>
    { v with bufferId := bufferId, cursor := {row := ⟨2 + explorerState.selectedIndex⟩, col := 0}, scrollRow := 0, scrollCol := 0 }
  let s'''' := { s''' with message := "Workgroup Explorer" }
  return (← openExplorerDefaultPreview s'''' bufferId explorerState)

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

      if entry.isDirectory then
        -- Navigate to directory
        openExplorerWithPreview state entry.path explorer.previewWindowId explorer.previewBufferId
      else
        -- Close preview window if it exists
        let s1 :=
          match explorer.previewWindowId with
          | none => state
          | some previewId =>
            let s1 := state.updateCurrentWorkspace fun ws =>
              match ws.layout.remove previewId with
              | some newLayout => { ws with layout := newLayout }
              | none => ws
            let s2 := updateExplorerState s1 buf.id (fun ex => { ex with previewWindowId := none, previewBufferId := none })
            match explorer.previewBufferId with
            | some previewBufId => ViE.Buffer.removeBuffer s2 previewBufId
            | none => s2
        -- Open file
        ViE.Buffer.openBuffer s1 entry.path
    | .workgroups =>
      let idx := selectedIdx.val
      if idx == 0 then
        let s' := { state with
          mode := .command
          inputState := { state.inputState with commandBuffer := "wg new ", countBuffer := "", previousKey := none, pendingKeys := "" }
        }
        return { s' with message := "Workgroup name:" }
      else if idx == 1 then
        let current := state.getCurrentWorkgroup.name
        let s' := { state with
          mode := .command
          inputState := { state.inputState with commandBuffer := s!"wg rename {current}", countBuffer := "", previousKey := none, pendingKeys := "" }
        }
        return { s' with message := "Workgroup rename:" }
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
        let s' := { state with
          mode := .command
          inputState := { state.inputState with commandBuffer := "ws new ", countBuffer := "", previousKey := none, pendingKeys := "" }
        }
        return { s' with message := "Workspace name:" }
      else if idx == 1 then
        let current := state.getCurrentWorkspace.name
        let s' := { state with
          mode := .command
          inputState := { state.inputState with commandBuffer := s!"ws rename {current}", countBuffer := "", previousKey := none, pendingKeys := "" }
        }
        return { s' with message := "Workspace rename:" }
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
