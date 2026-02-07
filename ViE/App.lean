import Lean
import ViE.Basic
import ViE.State
import ViE.Terminal
import ViE.UI
import ViE.Actions
import ViE.IO
import ViE.Config
import ViE.Checkpoint
import ViE.Loader

namespace ViE


/-- Resolve startup arguments into workspace path and filename. -/
def resolveStartupTarget (filename : Option String) : IO (Option String × Option String) := do
  match filename with
  | some path =>
    let filePath := System.FilePath.mk path
    if ← filePath.pathExists then
      if ← filePath.isDir then
        -- It's a directory, use as workspace
        pure (some path, none)
      else
        -- It's a file, use its parent directory as workspace
        let parentDir := match filePath.parent with
          | some p => p.toString
          | none => "."
        pure (some parentDir, some path)
    else
      -- Path doesn't exist, treat as new file
      pure (none, some path)
  | none => pure (none, none)

def clampCursorInBuffer (buffer : FileBuffer) (row col : Nat) : Point :=
  let lineCount := buffer.lineCount
  let clampedRow := if lineCount == 0 then 0 else min row (lineCount - 1)
  let lineLen := ViE.getLineLengthFromBuffer buffer ⟨clampedRow⟩ |>.getD 0
  let clampedCol := if lineLen == 0 then 0 else min col (lineLen - 1)
  { row := ⟨clampedRow⟩, col := ⟨clampedCol⟩ }

/-- Build startup workspace from a restored checkpoint session. -/
def buildRestoredWorkspace (settings : EditorConfig) (workspacePath : Option String)
  (files : List String) (activeIdx : Nat) (cursors : List (Nat × Nat)) : IO WorkspaceState := do
  let mut loaded : Array FileBuffer := #[]
  let mut nextId := 0
  for fname in files do
    let buf ← loadBufferByteArrayWithConfig fname settings
    loaded := loaded.push {
      buf with
        id := nextId
        table := { buf.table with undoLimit := settings.historyLimit }
    }
    nextId := nextId + 1

  let wsName := match workspacePath with
    | some path => (System.FilePath.fileName path).getD defaultWorkspaceName
    | none => defaultWorkspaceName

  if loaded.isEmpty then
    let empty : FileBuffer := {
      id := 0
      filename := none
      dirty := false
      table := PieceTable.fromString "" settings.searchBloomBuildLeafBits
      missingEol := false
      cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
    }
    return {
      name := wsName
      rootPath := workspacePath
      buffers := [empty]
      nextBufferId := 1
      layout := .window 0 { initialView with bufferId := 0 }
      activeWindowId := 0
      nextWindowId := 1
    }

  let activeIdx := if activeIdx < loaded.size then activeIdx else 0
  let activeBuf := loaded[activeIdx]!
  let (row, col) := List.getD cursors activeIdx (0, 0)
  let cursor := clampCursorInBuffer activeBuf row col
  return {
    name := wsName
    rootPath := workspacePath
    buffers := loaded.toList
    nextBufferId := loaded.size
    layout := .window 0 { initialView with bufferId := activeBuf.id, cursor := cursor }
    activeWindowId := 0
    nextWindowId := 1
  }

/-- Main event loop. -/
partial def loop (config : Config) (state : EditorState) : IO Unit := do
  -- Only render if state is dirty
  let state ← if state.dirty then
    ViE.UI.render state
  else
    pure state

  -- Reset dirty flag after render (or if it was already clean, keep it clean)
  let state := { state with dirty := false }

  let currentTime ← IO.monoMsNow
  let c ← ViE.Terminal.readKey

  -- Update window size
  let (rows, cols) ← ViE.Terminal.getWindowSize
  let resized := rows != state.windowHeight || cols != state.windowWidth
  let state := { state with windowHeight := rows, windowWidth := cols, dirty := state.dirty || resized }

  -- Handle the case where readKey returns None (no input available)
  match c with
  | none =>
    -- Check for timeout
    let (stateAfterTimeout, keys) := ViE.checkTimeout state currentTime
    let stateAfterTimeout := ViE.maybeRunIncrementalSearch stateAfterTimeout currentTime
    if keys.isEmpty then
       -- No input and no timeout events, sleep briefly to avoid busy loop
       IO.sleep 10 -- 10ms
       loop config stateAfterTimeout
    else
       -- Process timeout keys (e.g. flushed Esc)
       let mut finalState := stateAfterTimeout
       for key in keys do
         finalState ← ViE.update config finalState key

       if finalState.shouldQuit then
         return ()

       loop config { finalState with dirty := true }

  | some ch =>
    -- Parse the character into keys using the new parseKey function
    let (stateAfterParse, keys) := ViE.parseKey state ch currentTime

    -- Process all returned keys
    let mut finalState := stateAfterParse
    for key in keys do
      finalState ← ViE.update config finalState key

    if finalState.shouldQuit then
      return ()

    loop config { finalState with dirty := true }

/-- Entry point for the editor.
    Accepts a configuration and command line arguments. -/
def start (config : Config) (args : List String) : IO Unit := do

  -- Check for checkpoint session
  let checkpoint ← ViE.Checkpoint.loadSession

  -- Determine initial args (files to open)
  -- If we have a checkpoint and no args, use the checkpoint files.
  -- Otherwise use provided args.
  let (startArgs, restoreMeta) := match checkpoint with
    | some (files, activeIdx, cursors) =>
       if args.isEmpty then
         (files, some (activeIdx, cursors))
       else
         (args, none)
    | none => (args, none)

  let filename := startArgs.head?

  -- Check if the argument is a directory
  let (workspacePath, actualFilename) ← resolveStartupTarget filename

  let restoreFromCheckpoint := args.isEmpty && restoreMeta.isSome && !startArgs.isEmpty
  let state ←
    if restoreFromCheckpoint then
      match restoreMeta with
      | some (activeIdx, cursors) => do
          let restored ← buildRestoredWorkspace config.settings workspacePath startArgs activeIdx cursors
          let s := { ViE.initialState with
            config := config.settings
            message := s!"Restored {restored.buffers.length} file(s)"
          }
          pure <| s.updateCurrentWorkspace (fun _ => restored)
      | none =>
          pure { ViE.initialState with config := config.settings }
    else do
      -- Load buffer if file exists
      let initialBuffer ← match actualFilename with
        | some fname => loadBufferByteArrayWithConfig fname config.settings
        | none => pure {
            id := 0
            filename := actualFilename
            dirty := false
            table := PieceTable.fromString "" config.settings.searchBloomBuildLeafBits
            missingEol := false
            cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
          }

      -- Check if initial load had an error
      let firstLine := getLineFromBuffer initialBuffer 0 |>.getD ""
      let hasError := firstLine.startsWith "Error loading file:"

      let s := { ViE.initialState with
        config := config.settings,
        message := if hasError then firstLine
                   else match actualFilename with
                     | some f => s!"\"{f}\" [Read]"
                     | none => match workspacePath with
                       | some ws => s!"Workspace: {ws}"
                       | none => "New File"
      }

      -- Update the first workspace with the initial buffer and root path
      pure <| s.updateCurrentWorkspace fun ws =>
        let wsName := match workspacePath with
          | some path => (System.FilePath.fileName path).getD ws.name
          | none => ws.name
        { ws with
            name := wsName,
            rootPath := workspacePath,
            buffers := [initialBuffer],
            nextBufferId := 1
        }

  ViE.Terminal.enableRawMode
  try
    loop config state
  finally
    ViE.Terminal.disableRawMode
    ViE.Terminal.clearScreen
    IO.println "Bye!"

end ViE
