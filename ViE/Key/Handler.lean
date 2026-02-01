import ViE.State
import ViE.Types
import ViE.Command.Dispatch

namespace ViE.Key

open ViE

def handleCommandInput (commands : CommandMap) (state : EditorState) (k : Key) : IO EditorState := do
  match k with
  | Key.esc => return { state with mode := .normal, message := "", inputState := { state.inputState with commandBuffer := "" } }
  | Key.enter =>
    let newState ← ViE.Command.executeCommand commands state
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

end ViE.Key
