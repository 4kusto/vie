import ViE.State
import ViE.Terminal
import ViE.Config
import ViE.Unicode
import ViE.Color

namespace ViE.UI
open ViE
/-- Pad a string on the left with spaces until it reaches the given width. -/
def leftPad (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else "".pushn ' ' (width - s.length) ++ s

/-- Take characters from substring until visual width limit is reached. -/
partial def takeVisual (s : Substring.Raw) (width : Nat) : String :=
  let rec loop (sub : Substring.Raw) (currW : Nat) (acc : String) : String :=
    if sub.isEmpty then acc
    else
      let c := sub.front
      let w := Unicode.charWidth c
      if currW + w <= width then
        loop (sub.drop 1) (currW + w) (acc ++ Unicode.getDisplayString c)
      else
        acc
  loop s 0 ""

/-- Render the current editor state to the terminal. -/
def render (state : EditorState) : IO EditorState := do
  if !state.dirty then return state
  -- Start building the frame buffer
  let mut buffer : Array String := #[]

  buffer := buffer.push Terminal.hideCursorStr
  buffer := buffer.push Terminal.homeCursorStr

  let (rows, cols) ← Terminal.getWindowSize

  let wg := state.getCurrentWorkgroup
  let getBuffer (st : EditorState) (id : Nat) : FileBuffer :=
    let wg := st.getCurrentWorkgroup
    wg.buffers.find? (fun b => b.id == id) |>.getD initialFileBuffer

  let rec renderLayout (l : Layout) (st : EditorState) (r c h w : Nat) : (Array String × EditorState) := Id.run do
    match l with
    | Layout.window id view =>
      let workH := if h > 0 then h - 1 else 0
      let buf := getBuffer st view.bufferId
      let mut currentSt := st
      let mut winBuf : Array String := #[]

      for i in [0:workH] do
        let lineIdx : Row := ⟨view.scrollRow.val + i⟩
        let screenRow := r + i

        -- Position cursor for this line
        winBuf := winBuf.push (Terminal.moveCursorStr screenRow c)

        if lineIdx.val < FileBuffer.lineCount buf then
           -- Check cache
           let cachedLine := buf.cache.find lineIdx
           let (displayLine, nextSt) := match cachedLine with
             | some s => (s, currentSt)
             | none =>
               if let some lineStr := getLineFromBuffer buf lineIdx then
                 let lnWidth := if st.config.showLineNumbers then 4 else 0
                 let availableWidth := if w > lnWidth then w - lnWidth else 0
                 let sub := lineStr.toRawSubstring.drop view.scrollCol.val
                 let dl := takeVisual sub availableWidth
                 -- Update cache in currentSt
                 let updatedBuf := { buf with cache := buf.cache.update lineIdx dl }
                 let s' := currentSt.updateCurrentWorkgroup fun wg =>
                   { wg with buffers := wg.buffers.map (fun (b : FileBuffer) => if b.id == buf.id then updatedBuf else b) }
                 (dl, s')
               else ("", currentSt)

           currentSt := nextSt
           if st.config.showLineNumbers then
             winBuf := winBuf.push s!"{leftPad (toString (lineIdx.val + 1)) 3} "

           let isVisual := st.mode == Mode.visual || st.mode == Mode.visualBlock
           let selRange := if isVisual then st.selectionStart else none

           match selRange with
           | none => winBuf := winBuf.push displayLine
           | some _ =>
             let mut styleActive := false
             let chars := displayLine.toList
             let mut idx := 0
             for ch in chars do
                let colVal := view.scrollCol.val + idx
                let isSelected := st.isInSelection lineIdx ⟨colVal⟩

                if isSelected && !styleActive then
                  winBuf := winBuf.push "\x1b[7m" -- Inverse video
                  styleActive := true
                else if !isSelected && styleActive then
                  winBuf := winBuf.push "\x1b[0m"
                  styleActive := false

                winBuf := winBuf.push ch.toString
                idx := idx + 1

             if styleActive then winBuf := winBuf.push "\x1b[0m"
        else
           winBuf := winBuf.push st.config.emptyLineMarker

        -- Clear the rest of the line
        winBuf := winBuf.push Terminal.clearLineStr

      let statusRow := r + workH
      winBuf := winBuf.push (Terminal.moveCursorStr statusRow c)
      let fileName := buf.filename.getD "[No Name]"
      let modeStr := if id == currentSt.getCurrentWorkgroup.activeWindowId then s!"-- {st.mode} --" else "--"
      let eolMark := if buf.missingEol then " [noeol]" else ""
      let statusStr := s!"{modeStr} {fileName}{eolMark} [W:{id} B:{view.bufferId}] [{wg.name}] {st.workspace.name}"
      winBuf := winBuf.push st.config.statusBarStyle
      winBuf := winBuf.push statusStr.trimAscii.toString
      winBuf := winBuf.push Terminal.clearLineStr
      winBuf := winBuf.push st.config.resetStyle

      (winBuf, currentSt)

    | Layout.hsplit left right ratio =>
      let leftW := (Float.ofNat w * ratio).toUInt64.toNat
      let (leftStr, st') := renderLayout left st r c h leftW

      -- Draw vertical separator
      let mut sepStr : Array String := #[]
      if w > leftW then
        let sepCol := c + leftW
        for i in [0:h] do
           sepStr := sepStr.push (Terminal.moveCursorStr (r + i) sepCol)
           sepStr := sepStr.push st.config.vSplitStr

      let (rightStr, st'') := renderLayout right st' r (c + leftW + 1) h (if w > leftW then w - leftW - 1 else 0)

      (leftStr ++ sepStr ++ rightStr, st'')

    | Layout.vsplit top bottom ratio =>
      let topH := (Float.ofNat h * ratio).toUInt64.toNat
      let (topStr, st') := renderLayout top st r c topH w

      -- Draw horizontal separator
      let mut sepStr : Array String := #[]
      if h > topH then
        let sepRow := r + topH
        sepStr := sepStr.push (Terminal.moveCursorStr sepRow c)
        for _ in [0:w] do
           sepStr := sepStr.push st.config.hSplitStr

      let (bottomStr, st'') := renderLayout bottom st' (r + topH + 1) c (if h > topH then h - topH - 1 else 0) w

      (topStr ++ sepStr ++ bottomStr, st'')

  let layoutH := rows - 1
  let (layoutStr, state) := renderLayout wg.layout state 0 0 layoutH cols
  buffer := buffer ++ layoutStr

  -- Global Status / Command Line
  buffer := buffer.push (Terminal.moveCursorStr (rows - 1) 0)
  let statusRight :=
    if state.mode == .command then s!":{state.inputState.commandBuffer}"
    else state.message
  buffer := buffer.push statusRight
  buffer := buffer.push Terminal.clearLineStr

  -- Set Physical Cursor
  let rec getCursorPos (l : Layout) (r c h w : Nat) : Option (Nat × Nat) :=
    match l with
    | Layout.window id view =>
      if id == wg.activeWindowId then
         let buf := getBuffer state view.bufferId
         let workH := if h > 0 then h - 1 else 0
         let colOffset := if state.config.showLineNumbers then 4 else 0
         let visualRow := view.cursor.row.val - view.scrollRow.val

         if visualRow >= 0 && visualRow < workH then
             let rIdx : Row := ⟨view.scrollRow.val + visualRow⟩
             if let some currentLineStr := getLineFromBuffer buf rIdx then
               let preCursor := (currentLineStr.toRawSubstring.drop view.scrollCol.val).take (view.cursor.col.val - view.scrollCol.val)
               let visualCol := ViE.Unicode.substringWidth preCursor

               if (visualCol + colOffset) < w then
                  some (r + visualRow, c + visualCol + colOffset)
               else none
             else none
         else none
      else none
    | Layout.hsplit left right ratio =>
      let leftW := (Float.ofNat w * ratio).toUInt64.toNat
      (getCursorPos left r c h leftW).orElse (fun _ => getCursorPos right r (c + leftW + 1) h (if w > leftW then w - leftW - 1 else 0))
    | Layout.vsplit top bottom ratio =>
      let topH := (Float.ofNat h * ratio).toUInt64.toNat
      (getCursorPos top r c topH w).orElse (fun _ => getCursorPos bottom (r + topH + 1) c (if h > topH then h - topH - 1 else 0) w)

  buffer := buffer.push (
    match getCursorPos wg.layout 0 0 layoutH cols with
    | some (pr, pc) => Terminal.moveCursorStr pr pc
    | none => "" -- Cursor hidden or out of view
  )

  if state.mode == .command then
     buffer := buffer.push (Terminal.moveCursorStr (rows - 1) (1 + state.inputState.commandBuffer.length))

  if state.mode == .visual || state.mode == .visualBlock then
    buffer := buffer.push Terminal.hideCursorStr
  else
    buffer := buffer.push Terminal.showCursorStr

  -- Output everything
  let finalStr := String.intercalate "" buffer.toList
  IO.print finalStr
  (← IO.getStdout).flush
  return state

end ViE.UI
