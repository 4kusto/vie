import ViE.State
import ViE.Lsp.Lean

namespace ViE.Language.Lean.Key

open ViE

def handleInsertKey? (state : EditorState) (k : Key) : IO (Option EditorState) := do
  if !ViE.Lsp.Lean.isLeanBuffer state.getActiveBuffer then
    return none

  match state.completionPopup with
  | some _ =>
      match k with
      | Key.ctrl 'n' | Key.down =>
          return some <| ViE.Lsp.Lean.selectNextCompletion state
      | Key.ctrl 'p' | Key.up =>
          return some <| ViE.Lsp.Lean.selectPrevCompletion state
      | Key.ctrl 'y' | Key.char '\t' =>
          return some (← ViE.Lsp.Lean.acceptSelectedCompletion state)
      | Key.enter =>
          return some <| ViE.Lsp.Lean.clearCompletionPopup state.insertNewline
      | Key.esc =>
          return some <| ViE.Lsp.Lean.clearCompletionPopup ((state.commitEdit.moveCursorLeft).setMode Mode.normal)
      | Key.backspace =>
          let s' := state.deleteBeforeCursor
          return some (← ViE.Lsp.Lean.requestCompletionForActiveIfRunning s')
      | Key.char c =>
          let s' := state.insertChar c
          return some (← ViE.Lsp.Lean.requestCompletionForActiveIfRunning s')
      | _ =>
          return none
  | none =>
      match k with
      | Key.ctrl 'n' =>
          return some (← ViE.Lsp.Lean.requestCompletionForActiveIfRunning state)
      | Key.ctrl 'y' =>
          return some state
      | Key.char c =>
          let s' := state.insertChar c
          return some (← ViE.Lsp.Lean.requestCompletionForActiveIfRunning s')
      | Key.backspace =>
          let s' := state.deleteBeforeCursor
          return some (← ViE.Lsp.Lean.requestCompletionForActiveIfRunning s')
      | _ =>
          return none

end ViE.Language.Lean.Key
