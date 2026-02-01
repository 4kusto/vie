import ViE.State
import ViE.Command
import ViE.Key
import ViE.IO
import ViE.Config
import ViE.Basic
import ViE.Loader
import ViE.Checkpoint
import ViE.Types
import ViE.Window.Actions
import ViE.Buffer.Manager

namespace ViE

/-- Insert a character at the cursor position. -/
def insertAtCursor (state : EditorState) (c : Char) : EditorState :=
  state.insertChar c

/-- Parse filename argument from command args.
    Returns the filename from args, or the current buffer's filename if no args provided.
    Returns error message if multiple args or no filename available. -/
def parseFilenameArg (args : List String) (currentFilename : Option String) : Except String String :=
  match args with
  | [fname] => .ok fname
  | [] => match currentFilename with
    | some fname => .ok fname
    | none => .error "No file name"
  | _ => .error "Too many arguments"


def executeCommand (commands : CommandMap) (state : EditorState) : IO EditorState := do
  let fullCmd := state.inputState.commandBuffer
  let parts := fullCmd.splitOn " "
  match parts with
  | [] => return state
  | cmd :: args =>
    match commands.lookup cmd with
    | some action => action args state
    | none => return { state with message := s!"Unknown command: {fullCmd}" }

/-- Handle Enter key in explorer buffer -/
def handleExplorerEnter (commands : CommandMap) (state : EditorState) : IO EditorState := do
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
      let s' := { state with inputState := { state.inputState with commandBuffer := s!"ee {entry.path}" } }
      executeCommand commands s'
    else
      -- Open file
      let s' := { state with inputState := { state.inputState with commandBuffer := s!"e {entry.path}" } }
      executeCommand commands s'


def handleCommandInput (commands : CommandMap) (state : EditorState) (k : Key) : IO EditorState := do
  match k with
  | Key.esc => return { state with mode := .normal, message := "", inputState := { state.inputState with commandBuffer := "" } }
  | Key.enter =>
    let newState ← executeCommand commands state
    if newState.shouldQuit then
      return newState
    else
      return { newState with mode := .normal, inputState := { newState.inputState with commandBuffer := "" } }
  | Key.backspace =>
    if state.inputState.commandBuffer.length > 0 then
      let newCmd := state.inputState.commandBuffer.dropEnd 1
      return { state with inputState := { state.inputState with commandBuffer := newCmd.toString } }
    else
      return state
  | Key.char c => return { state with inputState := { state.inputState with commandBuffer := state.inputState.commandBuffer.push c } }
  | _ => return state

def clearInput (s : EditorState) : EditorState :=
  { s with inputState := { s.inputState with countBuffer := "", previousKey := none } }


end ViE
