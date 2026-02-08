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

def handleSearchInput (state : EditorState) (k : Key) : IO EditorState := do
  match k with
  | Key.esc =>
      return {
        state with
          mode := .normal
          inputState := { state.inputState with commandBuffer := "", pendingSearch := false }
      }
  | Key.enter =>
      let pattern := state.inputState.commandBuffer
      if pattern.isEmpty then
        return {
          state with
            mode := .normal
            message := "Empty search pattern"
            inputState := { state.inputState with commandBuffer := "", pendingSearch := false }
        }
      else
        let direction := if state.mode == .searchBackward then SearchDirection.backward else SearchDirection.forward
        let s' :=
          match state.searchState with
          | some st =>
              if st.pattern == pattern && st.direction == direction then
                state
              else
                ViE.startOrUpdateSearch state pattern direction false
          | none =>
              ViE.startOrUpdateSearch state pattern direction false
        let s'' := ViE.findNextMatch s' (some direction)
        return {
          s'' with
            mode := .normal
            inputState := { s''.inputState with commandBuffer := "", pendingSearch := false }
        }
  | Key.backspace =>
      if state.inputState.commandBuffer.length > 0 then
        let newCmd := state.inputState.commandBuffer.dropEnd 1
        if newCmd.isEmpty then
          return {
            state with
              searchState := none
              message := ""
              dirty := true
              inputState := {
                state.inputState with
                  commandBuffer := ""
                  pendingSearch := false
              }
          }
        else
        let now ← IO.monoMsNow
        let s1 := {
          state with
            inputState := {
              state.inputState with
                commandBuffer := newCmd.toString
                lastSearchInputTime := now
                pendingSearch := true
            }
        }
        if now - state.inputState.lastSearchRunTime >= ViE.incrementalSearchDebounceMs then
          let s2 := ViE.runIncrementalSearch s1
          return { s2 with inputState := { s2.inputState with pendingSearch := false, lastSearchRunTime := now } }
        else
          return s1
      else
        return state
  | Key.char c =>
      let now ← IO.monoMsNow
      let s1 := {
        state with
          inputState := {
            state.inputState with
              commandBuffer := state.inputState.commandBuffer.push c
              lastSearchInputTime := now
              pendingSearch := true
          }
      }
      if now - state.inputState.lastSearchRunTime >= ViE.incrementalSearchDebounceMs then
        let s2 := ViE.runIncrementalSearch s1
        return { s2 with inputState := { s2.inputState with pendingSearch := false, lastSearchRunTime := now } }
      else
        return s1
  | _ => return state

def clearInput (s : EditorState) : EditorState :=
  { s with inputState := { s.inputState with countBuffer := "", previousKey := none } }

end ViE.Key
