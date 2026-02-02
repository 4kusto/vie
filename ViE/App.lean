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
  let state := { state with windowHeight := rows, windowWidth := cols }

  -- Handle the case where readKey returns None (no input available)
  match c with
  | none =>
    -- Check for timeout
    let (stateAfterTimeout, keys) := ViE.checkTimeout state currentTime
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
  let (startArgs, _) := match checkpoint with
    | some (files, activeIdx, cursors) =>
       if args.isEmpty then
         (files, some (activeIdx, cursors))
       else
         (args, none)
    | none => (args, none)

  let filename := startArgs.head?

  -- Check if the argument is a directory
  let (workspacePath, actualFilename) ← match filename with
    | some path =>
      let filePath := System.FilePath.mk path
      if ← filePath.pathExists then
        if ← filePath.isDir then
          -- It's a directory, use as workspace
          pure (some path, none)
        else
          -- It's a file
          pure (none, some path)
      else
        -- Path doesn't exist, treat as new file
        pure (none, some path)
    | none => pure (none, none)

  -- Load buffer if file exists
  let initialBuffer ← match actualFilename with
    | some fname => loadBufferByteArray fname
    | none => pure {
        id := 0
        filename := actualFilename
        dirty := false
        table := PieceTable.fromString ""
        missingEol := false
        cache := { lineMap := Lean.RBMap.empty }
      }

  -- Check if initial load had an error
  let firstLine := getLineFromBuffer initialBuffer 0 |>.getD ""
  let hasError := firstLine.startsWith "Error loading file:"

  let workspace := match workspacePath with
    | some path => { rootPath := some path }
    | none => ViE.defaultWorkspace

  let state := { ViE.initialState with
    config := config.settings,
    workspace := workspace,
    message := if hasError then firstLine
               else match actualFilename with
                 | some f => s!"\"{f}\" [Read]"
                 | none => match workspacePath with
                   | some ws => s!"Workspace: {ws}"
                   | none => "New File"
  }

  -- Update the first workgroup with the initial buffer
  let state := state.updateCurrentWorkgroup fun wg =>
    { wg with buffers := [initialBuffer] }

  ViE.Terminal.enableRawMode
  try
    loop config state
  finally
    ViE.Terminal.disableRawMode
    ViE.Terminal.clearScreen
    IO.println "Bye!"

end ViE
