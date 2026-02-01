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
  normal := fun s k => match k with
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
          let s' := { s with inputState := { s.inputState with commandBuffer := s!"ee {parentPath}" } }
          ViE.Command.executeCommand commands s'
        | none => pure $ clearInput (EditorState.moveCursorLeftN s s.getCount)
      else
        pure $ clearInput (EditorState.moveCursorLeftN s s.getCount)
  | Key.char 'j' => pure $ clearInput (EditorState.moveCursorDownN s s.getCount)
  | Key.char 'k' => pure $ clearInput (EditorState.moveCursorUpN s s.getCount)
  | Key.char 'l' => pure $ clearInput (EditorState.moveCursorRightN s s.getCount)
  | Key.enter => ViE.Feature.handleExplorerEnter s
  | Key.char 'i' => pure $ s.setMode Mode.insert
  | Key.char 'a' =>
      let s' := EditorState.moveCursorRight s
      pure $ s'.setMode Mode.insert
  | Key.char 'A' =>
      let s' := EditorState.moveToLineEnd s
      pure $ s'.setMode Mode.insert
  | Key.char ':' => pure $ s.setMode Mode.command
  | Key.char 'q' => pure $ s.setMode Mode.command
  | Key.char 'o' => pure $ (EditorState.insertLineBelow s).setMode Mode.insert
  | Key.char 'O' => pure $ (EditorState.insertLineAbove s).setMode Mode.insert
  | Key.char 'v' => pure $ EditorState.startVisualMode s
  | Key.char 'V' => pure $ EditorState.startVisualBlockMode s
  | Key.char '0' =>
     if s.inputState.countBuffer.isEmpty then pure $ clearInput (EditorState.moveToLineStart s)
     else
        pure { s with inputState := { s.inputState with countBuffer := s.inputState.countBuffer.push '0' } }
  | Key.char '$' => pure $ clearInput (EditorState.moveToLineEnd s)
  | Key.char 'p' => pure $ clearInput (EditorState.pasteBelow s)
  | Key.char 'P' => pure $ clearInput (EditorState.pasteAbove s)
  | Key.char 'y' =>
     match s.inputState.previousKey with
     | some 'y' => pure $ clearInput (EditorState.yankCurrentLine s)
     | _ => pure { s with inputState := { s.inputState with previousKey := some 'y' } }
  | Key.char '|' =>
    let n := s.getCount
    pure $ clearInput (EditorState.jumpToColumn s n)
  | Key.char 'd' =>
    match s.inputState.previousKey with
    | some 'd' => pure $ s.deleteCurrentLine
    | _ => pure { s with inputState := { s.inputState with previousKey := some 'd' } }
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
            let next := (s.currentGroup + 1) % 10
            let s'' := s.switchToWorkgroup next
            pure { s'' with message := s!"Switched to workgroup {next}" }
         | 'T' =>
            let prev := if s.currentGroup == 0 then 9 else s.currentGroup - 1
            let s'' := s.switchToWorkgroup prev
            pure { s'' with message := s!"Switched to workgroup {prev}" }
         | _ => pure s'
      else
         match c with
         | 'g' =>
            match s.inputState.previousKey with
            | some 'g' =>
               -- gg implementation
               let n := s.getCount
               let line := if n > 0 then n else 1
               pure $ clearInput (EditorState.jumpToLine s line)
            | _ => pure { s with inputState := { s.inputState with previousKey := some 'g' } }
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
      | _ => pure s'
  | _ => pure { s with inputState := { s.inputState with countBuffer := "", previousKey := none } },

  insert := fun s k => match k with
    | Key.esc => pure $ s.setMode Mode.normal
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
