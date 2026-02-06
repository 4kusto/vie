import ViE.State
import ViE.Types
import ViE.Key.Handler
import ViE.Window.Actions
import ViE.Command.Explorer
import ViE.Command.Dispatch
import ViE.Basic

namespace ViE.Key

open ViE
open ViE.Window
open ViE.Feature
open ViE.Key

/-- Default key bindings. -/
def makeKeyMap (commands : CommandMap) : KeyMap := {
  normal := fun s k =>
  let handleMotion (state : EditorState) (motion : EditorState → EditorState) : IO EditorState :=
      let n := if state.getCount == 0 then 1 else state.getCount
      let rec applyN (st : EditorState) (count : Nat) : EditorState :=
        match count with
        | 0 => st
        | n + 1 => applyN (motion st) n
      termination_by count

      match state.inputState.previousKey with
      | none => pure $ clearInput (EditorState.clampCursor (applyN state n))
      | some 'd' =>
          let start := state.getCursor
          let endP := (applyN state n).getCursor
          pure $ clearInput (state.deleteRange start endP)
      | some 'c' =>
          let start := state.getCursor
          let endP := (applyN state n).getCursor
          pure $ clearInput (state.deleteRange start endP |>.setMode Mode.insert)
      | _ => pure $ clearInput (EditorState.clampCursor (applyN state n))


  match k with
  | Key.char 'h' =>
      -- Check if in explorer buffer
      let buf := s.getActiveBuffer
      let isExplorer := s.explorers.any (fun (id, _) => id == buf.id)
      if isExplorer then
        -- Navigate to parent directory
        let explorerOpt := s.explorers.find? (fun (id, _) => id == buf.id)
        match explorerOpt with
        | some (_, explorer) =>
          let parentPath := match (System.FilePath.mk explorer.currentPath).parent with
            | some p => p.toString
            | none => "/"
          ViE.Feature.openExplorerWithPreview s parentPath explorer.previewWindowId explorer.previewBufferId
        | none => pure $ clearInput (EditorState.moveCursorLeftN s s.getCount)
      else

        handleMotion s EditorState.moveCursorLeft
  | Key.char 'j' => do
      let s' ← handleMotion s EditorState.moveCursorDown
      ViE.Feature.refreshExplorerPreview s'
  | Key.char 'k' => do
      let s' ← handleMotion s EditorState.moveCursorUp
      ViE.Feature.refreshExplorerPreview s'
  | Key.char 'l' => handleMotion s EditorState.moveCursorRight
  | Key.enter => ViE.Feature.handleExplorerEnter s
  | Key.char 'i' => pure $ s.setMode Mode.insert
  | Key.char 'a' =>
      let s' := EditorState.moveCursorRight s
      pure $ s'.setMode Mode.insert
  | Key.char 'A' =>
      let s' := EditorState.moveToLineEnd s
      pure $ s'.setMode Mode.insert
  | Key.char ':' => pure $ s.setMode Mode.command
  | Key.char '/' =>
      pure {
        s with
          mode := Mode.searchForward
          inputState := {
            s.inputState with
              commandBuffer := ""
              countBuffer := ""
              previousKey := none
              pendingSearch := false
          }
      }
  | Key.char '?' =>
      pure {
        s with
          mode := Mode.searchBackward
          inputState := {
            s.inputState with
              commandBuffer := ""
              countBuffer := ""
              previousKey := none
              pendingSearch := false
          }
      }
  | Key.char 'q' => pure $ s.setMode Mode.command
  | Key.char 'o' => pure $ (EditorState.insertLineBelow s).setMode Mode.insert
  | Key.char 'O' => pure $ (EditorState.insertLineAbove s).setMode Mode.insert
  | Key.char 'v' => pure $ EditorState.startVisualMode s
  | Key.char 'V' => pure $ EditorState.startVisualBlockMode s
  | Key.char '0' =>
     if s.inputState.countBuffer.isEmpty then handleMotion s EditorState.moveToLineStart
     else
        pure { s with inputState := { s.inputState with countBuffer := s.inputState.countBuffer.push '0' } }
  | Key.char '$' => handleMotion s EditorState.moveToLineEnd

  | Key.char 'w' =>
      match s.inputState.previousKey with
      | some 'c' => pure $ clearInput (s.changeWord)
      | _ => handleMotion s EditorState.moveWordForward
  | Key.char 'b' => handleMotion s EditorState.moveWordBackward
  | Key.char 'e' => handleMotion s EditorState.moveWordEnd
  | Key.char 'x' => pure $ clearInput (EditorState.deleteCharAfterCursor s)
  | Key.char 'n' => pure $ clearInput (ViE.findNextMatch s)
  | Key.char 'N' =>
      let overrideDir :=
        match s.searchState with
        | some st =>
            if st.direction == .forward then some SearchDirection.backward else some SearchDirection.forward
        | none => none
      pure $ clearInput (ViE.findNextMatch s overrideDir)
  | Key.char 'p' =>
      let buf := s.getActiveBuffer
      let isExplorer := s.explorers.any (fun (id, _) => id == buf.id)
      if isExplorer then
        ViE.Feature.toggleExplorerPreview s
      else
        pure $ clearInput (EditorState.pasteBelow s)
  | Key.char 'P' => pure $ clearInput (EditorState.pasteAbove s)
  | Key.char 'y' =>
     match s.inputState.previousKey with
     | some 'y' => pure $ clearInput (EditorState.yankCurrentLine s)
     | _ => pure { s with inputState := { s.inputState with previousKey := some 'y' } }
  | Key.char '|' =>
    let n := s.getCount
    pure $ clearInput (EditorState.jumpToColumn s n)
  | Key.char 'c' =>
    match s.inputState.previousKey with
    | some 'c' =>
        -- cc: delete line and enter insert mode
        -- For now, approximate with delete line. Ideally should preserve line as empty.
        pure $ (s.deleteCurrentLine).setMode Mode.insert
    | _ => pure { s with inputState := { s.inputState with previousKey := some 'c' } }
  | Key.char 'd' =>
    match s.inputState.previousKey with
    | some 'd' => pure $ s.deleteCurrentLine
    | _ => pure { s with inputState := { s.inputState with previousKey := some 'd' } }
  | Key.char 'u' => pure $ s.undo
  | Key.ctrl 'r' => pure $ s.redo
  | Key.ctrl 'w' =>
      pure { s with inputState := { s.inputState with previousKey := some '\x17' } }
  | Key.char c =>
      if s.inputState.previousKey == some '\x17' then
         -- Handle window command
         let s' := { s with inputState := { s.inputState with previousKey := none } }
         match c with
         | 'h' => pure $ switchWindow s' .left
         | 'j' => pure $ switchWindow s' .down
         | 'k' => pure $ switchWindow s' .up
         | 'l' => pure $ switchWindow s' .right
         | 's' => pure $ splitWindow s' true
         | 'v' => pure $ splitWindow s' false
         | 'q' => pure $ closeActiveWindow s'
         | 'w' => pure $ cycleWindow s'
         | 'c' => pure $ cycleWindow s'
         | _ => pure s'
      else if s.inputState.previousKey == some 'g' then
         -- Handle g commands
         let s' := { s with inputState := { s.inputState with previousKey := none } }
         match c with
         | 't' =>
            let size := s.workgroups.size
            if size == 0 then
              pure s'
            else
              let next := (s.currentGroup + 1) % size
              let s'' := s.switchToWorkgroup next
              pure { s'' with message := s!"Switched to workgroup {next}" }
         | 'T' =>
            let size := s.workgroups.size
            if size == 0 then
              pure s'
            else
              let prev := if s.currentGroup == 0 then size - 1 else s.currentGroup - 1
              let s'' := s.switchToWorkgroup prev
              pure { s'' with message := s!"Switched to workgroup {prev}" }
         | 'g' =>
            -- gg implementation
            let n := s.getCount
            let line := if n > 0 then n else 1
            pure $ clearInput (EditorState.jumpToLine s line)
         | _ => pure s'
      else
         match c with
         | 'g' =>
             pure { s with inputState := { s.inputState with previousKey := some 'g' } }
         | 'G' =>
            let line := match s.inputState.countBuffer.toNat? with
              | some n => n
              | none => s.getActiveBuffer.lineCount
            pure $ clearInput (EditorState.jumpToLine s line)
         | _ =>
            if c.isDigit then
               pure { s with inputState := { s.inputState with countBuffer := s.inputState.countBuffer.push c } }
            else
               pure { s with inputState := { s.inputState with countBuffer := "", previousKey := none } }
  | Key.alt c =>
      let s' := { s with inputState := { s.inputState with previousKey := none } }
      match c with
      | 'h' => pure $ switchWindow s' .left
      | 'j' => pure $ switchWindow s' .down
      | 'k' => pure $ switchWindow s' .up
      | 'l' => pure $ switchWindow s' .right
      | 'H' => pure $ resizeWindow s' .left 0.05
      | 'J' => pure $ resizeWindow s' .down 0.05
      | 'K' => pure $ resizeWindow s' .up 0.05
      | 'L' => pure $ resizeWindow s' .right 0.05
      | _ =>
        if c.isDigit then
          match c.toString.toNat? with
          | some idx =>
            if idx < s.workgroups.size then
              let s'' := s.switchToWorkgroup idx
              pure { s'' with message := s!"Switched to workgroup {idx}" }
            else
              pure s'
          | none => pure s'
        else
          pure s'
  | _ => pure { s with inputState := { s.inputState with countBuffer := "", previousKey := none } },

  insert := fun s k => match k with
    | Key.esc => pure $ (s.commitEdit.moveCursorLeft).setMode Mode.normal
    | Key.backspace => pure $ s.deleteBeforeCursor
    | Key.char c => pure $ s.insertChar c
    | Key.enter => pure s.insertNewline
    | _ => pure s,

  command := handleCommandInput commands,

  visual := fun s k => match k with
    | Key.esc => pure $ EditorState.exitVisualMode s
    | Key.char 'v' => pure $ EditorState.exitVisualMode s
    | Key.char 'h' => pure $ clearInput (EditorState.moveCursorLeftN s s.getCount)
    | Key.char 'j' => pure $ clearInput (EditorState.moveCursorDownN s s.getCount)
    | Key.char 'k' => pure $ clearInput (EditorState.moveCursorUpN s s.getCount)
    | Key.char 'l' => pure $ clearInput (EditorState.moveCursorRightN s s.getCount)
    | Key.char 'w' => pure $ clearInput (EditorState.moveWordForward s)
    | Key.char 'b' => pure $ clearInput (EditorState.moveWordBackward s)
    | Key.char 'e' => pure $ clearInput (EditorState.moveWordEnd s)
    | Key.char '0' => pure $ clearInput (EditorState.moveToLineStart s)
    | Key.char '$' => pure $ clearInput (EditorState.moveToLineEnd s)
    | Key.char 'G' =>
        let line := match s.inputState.countBuffer.toNat? with
          | some n => n
          | none => s.getActiveBuffer.lineCount
        pure $ clearInput (EditorState.jumpToLine s line)
    | Key.char 'd' => pure $ EditorState.deleteSelection s
    | Key.char 'x' => pure $ EditorState.deleteSelection s
    | Key.char 'y' => pure $ EditorState.yankSelection s
    | Key.char c =>
         match c with
         | 'g' =>
            match s.inputState.previousKey with
            | some 'g' =>
               let n := s.getCount
               let line := if n > 0 then n else 1
               pure $ clearInput (EditorState.jumpToLine s line)
            | _ => pure { s with inputState := { s.inputState with previousKey := some 'g' } }
         | _ =>
            if c.isDigit then
               pure { s with inputState := { s.inputState with countBuffer := s.inputState.countBuffer.push c } }
            else
               pure s
    | _ => pure s,

  visualBlock := fun s k => match k with
    | Key.esc => pure $ EditorState.exitVisualMode s
    | Key.char 'v' => pure $ EditorState.exitVisualMode s
    | Key.char 'V' => pure $ EditorState.exitVisualMode s
    | Key.char 'h' => pure $ clearInput (EditorState.moveCursorLeftN s s.getCount)
    | Key.char 'j' => pure $ clearInput (EditorState.moveCursorDownN s s.getCount)
    | Key.char 'k' => pure $ clearInput (EditorState.moveCursorUpN s s.getCount)
    | Key.char 'l' => pure $ clearInput (EditorState.moveCursorRightN s s.getCount)
    | Key.char '0' => pure $ clearInput (EditorState.moveToLineStart s)
    | Key.char '$' => pure $ clearInput (EditorState.moveToLineEnd s)
    | Key.char 'G' =>
        let line := match s.inputState.countBuffer.toNat? with
          | some n => n
          | none => s.getActiveBuffer.lineCount
        pure $ clearInput (EditorState.jumpToLine s line)
    | Key.char 'd' => pure $ EditorState.deleteSelection s
    | Key.char 'x' => pure $ EditorState.deleteSelection s
    | Key.char 'y' => pure $ EditorState.yankSelection s
    | Key.char c =>
         match c with
         | 'g' =>
            match s.inputState.previousKey with
            | some 'g' =>
               let n := s.getCount
               let line := if n > 0 then n else 1
               pure $ clearInput (EditorState.jumpToLine s line)
            | _ => pure { s with inputState := { s.inputState with previousKey := some 'g' } }
         | _ =>
            if c.isDigit then
               pure { s with inputState := { s.inputState with countBuffer := s.inputState.countBuffer.push c } }
            else
               pure s
    | _ => pure s
}

end ViE.Key
