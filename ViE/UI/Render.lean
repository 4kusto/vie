import ViE.UI.Window
import ViE.UI.Overlay
import ViE.Terminal

namespace ViE.UI
open ViE

/-- Render the current editor state to the terminal. -/
def render (state : EditorState) : IO EditorState := do
  if !state.dirty then return state
  -- Start building the frame buffer
  let mut buffer : Array String := #[]

  buffer := buffer.push Terminal.hideCursorStr

  let (rows, cols) ← Terminal.getWindowSize

  let ws := state.getCurrentWorkspace

  let rec renderLayout (l : Layout) (st : EditorState) (r c h w : Nat) : (Array String × EditorState) := Id.run do
    match l with
    | Layout.window id view =>
      if st.getCurrentWorkspace.isFloatingWindow id then
        let mut blankBuf : Array String := #[]
        for i in [0:h] do
          blankBuf := blankBuf.push (Terminal.moveCursorStr (r + i) c)
          blankBuf := blankBuf.push ("".pushn ' ' w)
        return (blankBuf, st)
      renderWindow st id view { row := r, col := c, height := h, width := w }

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
  let baseLayout :=
    ws.getFloatingWindowIds.foldl (fun acc wid =>
      match acc with
      | some l => l.remove wid
      | none => none) (some ws.layout)
  if baseLayout.isNone then
    buffer := buffer.push Terminal.clearScreenStr
  buffer := buffer.push Terminal.homeCursorStr
  let (layoutStr, stateAfterLayout) :=
    match baseLayout with
    | some l => renderLayout l state 0 0 layoutH cols
    | none => (#[], state)
  buffer := buffer ++ layoutStr

  let wsAfterLayout := stateAfterLayout.getCurrentWorkspace
  let floatingViews := wsAfterLayout.getFloatingWindowIds.foldl (fun acc wid =>
    match wsAfterLayout.layout.findView wid with
    | some v => acc.push (wid, v)
    | none => acc) #[]
  let mut activeFloatingCursorPos : Option (Nat × Nat) := none
  for i in [0:floatingViews.size] do
    let (wid, view) := floatingViews[i]!
    match stateAfterLayout.getFloatingWindowBounds wid with
    | some (top, left, h, w) =>
      let borderFlags := stateAfterLayout.getFloatingWindowBorderFlags wid
      let (winBuf, cursorPos) := renderFloatingWindow stateAfterLayout view { row := top, col := left, height := h, width := w } borderFlags
      buffer := buffer ++ winBuf
      if wid == wsAfterLayout.activeWindowId then
        activeFloatingCursorPos := cursorPos
    | none => pure ()

  -- Global Status / Command Line
  buffer := buffer.push (Terminal.moveCursorStr (rows - 1) 0)
  let statusRight := renderStatusBar stateAfterLayout
  buffer := buffer.push statusRight
  buffer := buffer.push Terminal.clearLineStr

  let overlayToRender := stateAfterLayout.floatingOverlay.orElse (fun _ => messageOverlayForState stateAfterLayout)
  if let some overlay := overlayToRender then
    buffer := buffer ++ renderFloatingOverlay rows cols stateAfterLayout.config.tabStop overlay

  -- Set Physical Cursor
  let rec getCursorPos (l : Layout) (r c h w : Nat) : Option (Nat × Nat) :=
    match l with
    | Layout.window id view =>
      if id == wsAfterLayout.activeWindowId then
         let workH := if h > 0 then h - 1 else 0
         let colOffset := if stateAfterLayout.config.showLineNumbers then 4 else 0
         let visualRow := view.cursor.row.val - view.scrollRow.val

         if visualRow >= 0 && visualRow < workH then
             if view.cursor.col.val < view.scrollCol.val then
               none
             else
               let visualCol := view.cursor.col.val - view.scrollCol.val
               if (visualCol + colOffset) < w then
                  some (r + visualRow, c + visualCol + colOffset)
               else none
         else none
      else none
    | Layout.hsplit left right ratio =>
      let leftW := (Float.ofNat w * ratio).toUInt64.toNat
      (getCursorPos left r c h leftW).orElse (fun _ => getCursorPos right r (c + leftW + 1) h (if w > leftW then w - leftW - 1 else 0))
    | Layout.vsplit top bottom ratio =>
      let topH := (Float.ofNat h * ratio).toUInt64.toNat
      (getCursorPos top r c topH w).orElse (fun _ => getCursorPos bottom (r + topH + 1) c (if h > topH then h - topH - 1 else 0) w)

  let overlayCursorPos : Option (Nat × Nat) :=
    match stateAfterLayout.floatingOverlay with
    | none => none
    | some overlay =>
        match computeFloatingOverlayLayout rows cols stateAfterLayout.config.tabStop overlay with
        | none => none
        | some layout =>
            let lines := if overlay.lines.isEmpty then #[""] else overlay.lines
            let maxRow := lines.size - 1
            let rowIdx := min overlay.cursorRow maxRow
            let line := lines[rowIdx]!
            let lineW := Unicode.stringWidthWithTabStop line stateAfterLayout.config.tabStop
            let colIdx := min overlay.cursorCol lineW
            let visRow := min rowIdx (layout.contentRows - 1)
            let visCol := min colIdx layout.innerWidth
            some (layout.top + 1 + layout.titleRows + visRow, layout.left + 2 + visCol)

  if stateAfterLayout.floatingOverlay.isSome && stateAfterLayout.mode != .command &&
     stateAfterLayout.mode != .searchForward && stateAfterLayout.mode != .searchBackward then
    buffer := buffer.push (
      match overlayCursorPos with
      | some (pr, pc) => Terminal.moveCursorStr pr pc
      | none => ""
    )
  else if wsAfterLayout.isFloatingWindow wsAfterLayout.activeWindowId &&
      stateAfterLayout.mode != .command && stateAfterLayout.mode != .searchForward && stateAfterLayout.mode != .searchBackward then
    buffer := buffer.push (
      match activeFloatingCursorPos with
      | some (pr, pc) => Terminal.moveCursorStr pr pc
      | none => ""
    )
  else
    buffer := buffer.push (
      match getCursorPos (baseLayout.getD wsAfterLayout.layout) 0 0 layoutH cols with
      | some (pr, pc) => Terminal.moveCursorStr pr pc
      | none => ""
    )

  if stateAfterLayout.mode == .command then
     buffer := buffer.push (Terminal.moveCursorStr (rows - 1) (1 + stateAfterLayout.inputState.commandBuffer.length))
  if stateAfterLayout.mode == .searchForward || stateAfterLayout.mode == .searchBackward then
     buffer := buffer.push (Terminal.moveCursorStr (rows - 1) (1 + stateAfterLayout.inputState.commandBuffer.length))

  if stateAfterLayout.mode == .visual || stateAfterLayout.mode == .visualBlock then
    buffer := buffer.push Terminal.hideCursorStr
  else
    buffer := buffer.push Terminal.showCursorStr

  -- Output everything
  let finalStr := String.intercalate "" buffer.toList
  IO.print finalStr
  (← IO.getStdout).flush
  return stateAfterLayout

end ViE.UI
