import ViE.State
import ViE.Types
import ViE.Buffer.Manager
import ViE.Basic


namespace ViE.Feature

open ViE

/-- Open the file explorer at the specified path (or current workspace root) -/
def openExplorer (state : EditorState) (pathArg : String) : IO EditorState := do
  let path := if pathArg == "." || pathArg == "" then state.workspace.rootPath.getD "."
              else if pathArg.startsWith "/" then pathArg
              else match state.workspace.rootPath with
                   | some root => root ++ "/" ++ pathArg
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
    return { s''' with message := s!"Explorer: {path}" }

  catch e =>
    return { state with message := s!"Error reading directory: {e}" }

/-- Handle Enter key in explorer buffer -/
def handleExplorerEnter (state : EditorState) : IO EditorState := do
  let buf := state.getActiveBuffer

  -- Check if this is an explorer buffer
  let explorerOpt := state.explorers.find? (fun (id, _) => id == buf.id)

  match explorerOpt with
  | none => return state.insertNewline -- Not an explorer, normal behavior
  | some (_, explorer) =>
    -- Get current cursor row
    let cursor := state.getCursor
    -- Explorer header is 2 lines, so subtract 2
    let selectedIdx := cursor.row - 2

    if selectedIdx < 0 || selectedIdx >= explorer.entries.length then
      return state

    -- Get selected entry
    let entry := explorer.entries[selectedIdx]!

    if entry.isDirectory then
      -- Navigate to directory
      openExplorer state entry.path
    else
      -- Open file
      ViE.Buffer.openBuffer state entry.path

end ViE.Feature
