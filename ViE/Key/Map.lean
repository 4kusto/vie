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

def arrayInsertAt (arr : Array α) (idx : Nat) (x : α) : Array α :=
  let i := min idx arr.size
  (arr.toList.take i ++ [x] ++ arr.toList.drop i).toArray

def arrayEraseAt (arr : Array α) (idx : Nat) : Array α :=
  if idx >= arr.size then arr
  else
    (arr.toList.take idx ++ arr.toList.drop (idx + 1)).toArray

def overlayLineLen (line : String) : Nat :=
  line.toList.length

def overlayNormalize (ov : FloatingOverlay) : FloatingOverlay :=
  if ov.lines.isEmpty then
    { ov with lines := #[""], cursorRow := 0, cursorCol := 0 }
  else
    let row := min ov.cursorRow (ov.lines.size - 1)
    let col := min ov.cursorCol (overlayLineLen (ov.lines[row]!))
    { ov with cursorRow := row, cursorCol := col }

def updateOverlay (s : EditorState) (f : FloatingOverlay → FloatingOverlay) : EditorState :=
  match s.floatingOverlay with
  | none => s
  | some ov =>
      { s with
          floatingOverlay := some (overlayNormalize (f ov))
          dirty := true
      }

def overlayMoveLeft (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    if ov.cursorCol > 0 then { ov with cursorCol := ov.cursorCol - 1 } else ov)

def overlayMoveRight (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let len := overlayLineLen (ov.lines[ov.cursorRow]!)
    if ov.cursorCol < len then { ov with cursorCol := ov.cursorCol + 1 } else ov)

def overlayMoveUp (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    if ov.cursorRow > 0 then { ov with cursorRow := ov.cursorRow - 1 } else ov)

def overlayMoveDown (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    if ov.cursorRow + 1 < ov.lines.size then { ov with cursorRow := ov.cursorRow + 1 } else ov)

def overlayMoveLineStart (s : EditorState) : EditorState :=
  updateOverlay s (fun ov => { ov with cursorCol := 0 })

def overlayMoveLineEnd (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    { ov with cursorCol := overlayLineLen (ov.lines[ov.cursorRow]!) })

def overlayInsertChar (s : EditorState) (c : Char) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let row := ov.cursorRow
    let col := ov.cursorCol
    let line := ov.lines[row]!
    let chars := line.toList
    let newLine := String.ofList (chars.take col ++ [c] ++ chars.drop col)
    { ov with lines := ov.lines.set! row newLine, cursorCol := col + 1 })

def overlayBackspace (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let row := ov.cursorRow
    let col := ov.cursorCol
    let line := ov.lines[row]!
    if col > 0 then
      let chars := line.toList
      let newLine := String.ofList (chars.take (col - 1) ++ chars.drop col)
      { ov with lines := ov.lines.set! row newLine, cursorCol := col - 1 }
    else if row > 0 then
      let prev := ov.lines[row - 1]!
      let merged := prev ++ line
      let lines := (ov.lines.set! (row - 1) merged)
      let lines := arrayEraseAt lines row
      { ov with lines := lines, cursorRow := row - 1, cursorCol := overlayLineLen prev }
    else
      ov)

def overlayDeleteCharAt (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let row := ov.cursorRow
    let col := ov.cursorCol
    let line := ov.lines[row]!
    let len := overlayLineLen line
    if col < len then
      let chars := line.toList
      let newLine := String.ofList (chars.take col ++ chars.drop (col + 1))
      { ov with lines := ov.lines.set! row newLine }
    else if row + 1 < ov.lines.size then
      let next := ov.lines[row + 1]!
      let merged := line ++ next
      let lines := (ov.lines.set! row merged)
      let lines := arrayEraseAt lines (row + 1)
      { ov with lines := lines }
    else
      ov)

def overlayInsertNewline (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let row := ov.cursorRow
    let col := ov.cursorCol
    let line := ov.lines[row]!
    let chars := line.toList
    let left := String.ofList (chars.take col)
    let right := String.ofList (chars.drop col)
    let lines := (ov.lines.set! row left)
    let lines := arrayInsertAt lines (row + 1) right
    { ov with lines := lines, cursorRow := row + 1, cursorCol := 0 })

def overlayOpenLineBelow (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let row := ov.cursorRow + 1
    let lines := arrayInsertAt ov.lines row ""
    { ov with lines := lines, cursorRow := row, cursorCol := 0 })

def overlayOpenLineAbove (s : EditorState) : EditorState :=
  updateOverlay s (fun ov =>
    let ov := overlayNormalize ov
    let row := ov.cursorRow
    let lines := arrayInsertAt ov.lines row ""
    { ov with lines := lines, cursorRow := row, cursorCol := 0 })

def shouldRenderMessageAsFloat (msg : String) : Bool :=
  let m := msg.trimAscii.toString
  if m.isEmpty then
    false
  else
    m.startsWith "Error" ||
    m.startsWith "Cannot" ||
    m.startsWith "Invalid" ||
    m.startsWith "Unknown" ||
    m.startsWith "No " ||
    m.startsWith "Empty " ||
    m.startsWith "Usage:" ||
    m.startsWith "failed" ||
    m.startsWith "Failed" ||
    m.contains "not found"

/-- Default key bindings. -/
def makeKeyMap (commands : CommandMap) : KeyMap := {
  normal := fun s k =>
  let rawCount (state : EditorState) : Nat :=
      match state.inputState.countBuffer.toNat? with
      | some n => n
      | none => 0

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

  let submitFloatingInput (state : EditorState) : IO EditorState := do
    match state.floatingInputCommand, state.floatingOverlay with
    | some cmdPrefix, some ov =>
      let input := (ov.lines[0]?.getD "").trimAscii.toString
      let cmd := s!"{cmdPrefix}{input}"
      let pre := {
        state with
          floatingOverlay := none
          floatingInputCommand := none
          mode := .normal
          inputState := {
            state.inputState with
              commandBuffer := cmd
              countBuffer := ""
              previousKey := none
              pendingKeys := ""
          }
      }
      let out ← ViE.Command.executeCommand commands pre
      return {
        out with
          mode := .normal
          inputState := {
            out.inputState with
              commandBuffer := ""
              countBuffer := ""
              previousKey := none
              pendingKeys := ""
          }
          dirty := true
      }
    | _, _ =>
      return {
        state with
          floatingOverlay := none
          floatingInputCommand := none
          dirty := true
      }

  let closeOverlay : EditorState :=
    { s with floatingOverlay := none, floatingInputCommand := none, dirty := true, message := "floating overlay cleared" }

  if s.floatingOverlay.isSome then
    if s.floatingInputCommand.isSome then
      match k with
      | Key.esc => pure { s with floatingOverlay := none, floatingInputCommand := none, mode := .normal, dirty := true, message := "" }
      | Key.enter => submitFloatingInput s
      | Key.char 'q' => pure { s with floatingOverlay := none, floatingInputCommand := none, mode := .normal, dirty := true, message := "" }
      | Key.left => pure (overlayMoveLeft s)
      | Key.right => pure (overlayMoveRight s)
      | Key.up => pure (overlayMoveUp s)
      | Key.down => pure (overlayMoveDown s)
      | Key.backspace => pure (overlayBackspace s)
      | Key.char c => pure (overlayInsertChar s c)
      | _ => pure s
    else
      match k with
      | Key.esc => pure closeOverlay
      | Key.enter => pure closeOverlay
      | Key.char 'q' => pure closeOverlay
      | Key.char ':' => pure $ s.setMode Mode.command
      | Key.char 'i' => pure { s with mode := .insert, dirty := true }
      | Key.char 'a' => pure { (overlayMoveRight s) with mode := .insert }
      | Key.char 'h' => pure (overlayMoveLeft s)
      | Key.char 'j' => pure (overlayMoveDown s)
      | Key.char 'k' => pure (overlayMoveUp s)
      | Key.char 'l' => pure (overlayMoveRight s)
      | Key.char '0' => pure (overlayMoveLineStart s)
      | Key.char '$' => pure (overlayMoveLineEnd s)
      | Key.char 'x' => pure (overlayDeleteCharAt s)
      | Key.char 'o' => pure { (overlayOpenLineBelow s) with mode := .insert }
      | Key.char 'O' => pure { (overlayOpenLineAbove s) with mode := .insert }
      | _ => pure s
  else
    if s.inputState.previousKey == some 'f' then
      match k with
      | Key.char c =>
        let s' := { s with inputState := { s.inputState with previousKey := none } }
        let n := if s'.getCount == 0 then 1 else s'.getCount
        pure $ clearInput (EditorState.findCharMotion s' c true false n true)
      | _ =>
        pure { s with inputState := { s.inputState with previousKey := none, countBuffer := "" } }
    else if s.inputState.previousKey == some 't' then
      match k with
      | Key.char c =>
        let s' := { s with inputState := { s.inputState with previousKey := none } }
        let n := if s'.getCount == 0 then 1 else s'.getCount
        pure $ clearInput (EditorState.findCharMotion s' c true true n true)
      | _ =>
        pure { s with inputState := { s.inputState with previousKey := none, countBuffer := "" } }
    else
    if shouldRenderMessageAsFloat s.message then
      match k with
      | Key.esc => pure { s with message := "", dirty := true }
      | Key.enter => pure { s with message := "", dirty := true }
      | _ => pure s
    else
    match k with
    | Key.esc =>
        pure { s with inputState := { s.inputState with countBuffer := "", previousKey := none } }
    | Key.char 'h' =>
        -- Check if in explorer buffer
        let buf := s.getActiveBuffer
        let isExplorer := s.explorers.any (fun (id, _) => id == buf.id)
        if isExplorer then
          let explorerOpt := s.explorers.find? (fun (id, _) => id == buf.id)
          match explorerOpt with
          | some (_, explorer) =>
            if explorer.mode == .files then
              let parentPath := match (System.FilePath.mk explorer.currentPath).parent with
                | some p => p.toString
                | none => "/"
              ViE.Feature.openExplorerWithPreview s parentPath explorer.previewWindowId explorer.previewBufferId
            else
              handleMotion s EditorState.moveCursorLeft
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
          searchState := none
          message := ""
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
          searchState := none
          message := ""
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
    | Key.char 'H' =>
      let n := rawCount s
      pure $ clearInput ((s.pushJumpPoint).moveToScreenTop n)
    | Key.char 'M' =>
      pure $ clearInput ((s.pushJumpPoint).moveToScreenMiddle)
    | Key.char 'L' =>
      let n := rawCount s
      pure $ clearInput ((s.pushJumpPoint).moveToScreenBottom n)
    | Key.char 'f' =>
      pure { s with inputState := { s.inputState with previousKey := some 'f' } }
    | Key.char 't' =>
      pure { s with inputState := { s.inputState with previousKey := some 't' } }
    | Key.char ';' =>
      pure $ clearInput (EditorState.repeatFindChar s false)
    | Key.char ',' =>
      pure $ clearInput (EditorState.repeatFindChar s true)
    | Key.char '%' =>
      pure $ clearInput ((s.pushJumpPoint).jumpMatchingBracket)
    | Key.char '*' =>
      pure $ clearInput (EditorState.searchWordUnderCursor s .forward)
    | Key.char '#' =>
      pure $ clearInput (EditorState.searchWordUnderCursor s .backward)

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
      pure $ clearInput (EditorState.jumpToColumn s ⟨n⟩)
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
    | Key.ctrl 'd' =>
      let n := rawCount s
      pure $ clearInput (EditorState.scrollHalfPageDown s n)
    | Key.ctrl 'u' =>
      let n := rawCount s
      pure $ clearInput (EditorState.scrollHalfPageUp s n)
    | Key.ctrl 'f' =>
      let n := rawCount s
      pure $ clearInput (EditorState.scrollPageDown s n)
    | Key.ctrl 'b' =>
      let n := rawCount s
      pure $ clearInput (EditorState.scrollPageUp s n)
    | Key.ctrl 'e' =>
      let n := rawCount s
      pure $ clearInput (EditorState.scrollWindowDown s n)
    | Key.ctrl 'y' =>
      let n := rawCount s
      pure $ clearInput (EditorState.scrollWindowUp s n)
    | Key.ctrl 'o' =>
      pure $ clearInput (EditorState.jumpBackInList s)
    | Key.char '\t' =>
      pure $ clearInput (EditorState.jumpForwardInList s)
    | Key.ctrl 'r' => pure $ s.redo
    | Key.ctrl 'l' => pure { s with dirty := true, message := "redraw" }
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
      let activeIsFloating := s'.getCurrentWorkspace.isFloatingWindow s'.getCurrentWorkspace.activeWindowId
      match c with
      | 'h' => pure $ switchWindow s' .left
      | 'j' => pure $ switchWindow s' .down
      | 'k' => pure $ switchWindow s' .up
      | 'l' => pure $ switchWindow s' .right
      | 'H' =>
        if activeIsFloating then
          pure $ nudgeActiveFloatingWindow s' .left
        else
          pure $ resizeWindow s' .left 0.05
      | 'J' =>
        if activeIsFloating then
          pure $ nudgeActiveFloatingWindow s' .down
        else
          pure $ resizeWindow s' .down 0.05
      | 'K' =>
        if activeIsFloating then
          pure $ nudgeActiveFloatingWindow s' .up
        else
          pure $ resizeWindow s' .up 0.05
      | 'L' =>
        if activeIsFloating then
          pure $ nudgeActiveFloatingWindow s' .right
        else
          pure $ resizeWindow s' .right 0.05
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

  insert := fun s k =>
    if s.floatingOverlay.isSome then
      if s.floatingInputCommand.isSome then
        let submitFloatingInput (state : EditorState) : IO EditorState := do
          match state.floatingInputCommand, state.floatingOverlay with
          | some cmdPrefix, some ov =>
            let input := (ov.lines[0]?.getD "").trimAscii.toString
            let cmd := s!"{cmdPrefix}{input}"
            let pre := {
              state with
                floatingOverlay := none
                floatingInputCommand := none
                mode := .normal
                inputState := {
                  state.inputState with
                    commandBuffer := cmd
                    countBuffer := ""
                    previousKey := none
                    pendingKeys := ""
                }
            }
            let out ← ViE.Command.executeCommand commands pre
            return {
              out with
                mode := .normal
                inputState := {
                  out.inputState with
                    commandBuffer := ""
                    countBuffer := ""
                    previousKey := none
                    pendingKeys := ""
                }
                dirty := true
            }
          | _, _ =>
            return {
              state with
                floatingOverlay := none
                floatingInputCommand := none
                mode := .normal
                dirty := true
            }
        match k with
        | Key.esc => pure { s with floatingOverlay := none, floatingInputCommand := none, mode := .normal, dirty := true, message := "" }
        | Key.backspace => pure (overlayBackspace s)
        | Key.char c => pure (overlayInsertChar s c)
        | Key.enter => submitFloatingInput s
        | Key.left => pure (overlayMoveLeft s)
        | Key.right => pure (overlayMoveRight s)
        | Key.up => pure (overlayMoveUp s)
        | Key.down => pure (overlayMoveDown s)
        | _ => pure s
      else
        match k with
        | Key.esc => pure { s with mode := .normal, dirty := true }
        | Key.backspace => pure (overlayBackspace s)
        | Key.char c => pure (overlayInsertChar s c)
        | Key.enter => pure (overlayInsertNewline s)
        | Key.left => pure (overlayMoveLeft s)
        | Key.right => pure (overlayMoveRight s)
        | Key.up => pure (overlayMoveUp s)
        | Key.down => pure (overlayMoveDown s)
        | _ => pure s
    else
      match k with
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
