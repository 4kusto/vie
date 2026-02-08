import ViE.UI.Primitives
import ViE.UI.Search
import ViE.Terminal

namespace ViE.UI
open ViE

def renderWindow (state : EditorState) (windowId : Nat) (view : ViewState) (rect : Rect) : (Array String × EditorState) := Id.run do
  let r := rect.row
  let c := rect.col
  let h := rect.height
  let w := rect.width
  let workH := if h > 0 then h - 1 else 0
  let buf0 := getWorkspaceBuffer state view.bufferId
  let mut currentSt := state
  let mut winBuf : Array String := #[]

  let prefetchMargin := 20
  let totalLines := FileBuffer.lineCount buf0
  let startRow := if view.scrollRow.val > prefetchMargin then view.scrollRow.val - prefetchMargin else 0
  let endRow := min totalLines (view.scrollRow.val + workH + prefetchMargin)
  currentSt := prefetchSearchLineMatches currentSt buf0 startRow endRow

  for i in [0:workH] do
    let lineIdx : Row := ⟨view.scrollRow.val + i⟩
    let screenRow := r + i
    winBuf := winBuf.push (Terminal.moveCursorStr screenRow c)

    let buf := getWorkspaceBuffer currentSt view.bufferId
    if lineIdx.val < FileBuffer.lineCount buf then
      let lnWidth := if state.config.showLineNumbers then 4 else 0
      let availableWidth := if w > lnWidth then w - lnWidth else 0

      let cachedLine := buf.cache.find lineIdx
      let cachedRaw := buf.cache.findRaw lineIdx
      let cachedIdx := buf.cache.findIndex lineIdx
      let lineStr := cachedRaw.getD (getLineFromBuffer buf lineIdx |>.getD "")
      let lineIndex := cachedIdx.getD (ViE.Unicode.buildDisplayByteIndexWithTabStop lineStr state.config.tabStop)
      let (displayLine, nextSt) :=
        match cachedLine with
        | some (s, cachedScrollCol, cachedWidth) =>
            if cachedScrollCol == view.scrollCol.val && cachedWidth == availableWidth then
              (s, currentSt)
            else
              match getLineFromBuffer buf lineIdx with
              | some lineStr =>
                  let sub := ViE.Unicode.dropByDisplayWidthWithTabStop lineStr.toRawSubstring state.config.tabStop view.scrollCol.val
                  let dl := ViE.Unicode.takeByDisplayWidthWithTabStop sub state.config.tabStop availableWidth
                  let cache := match cachedRaw, cachedIdx with
                    | some raw, some _ =>
                        if raw == lineStr then
                          buf.cache
                        else
                          (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndexWithTabStop lineStr state.config.tabStop))
                    | _, _ =>
                        (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndexWithTabStop lineStr state.config.tabStop))
                  let cache := (cache.update lineIdx dl view.scrollCol.val availableWidth).updateRaw lineIdx lineStr
                  let updatedBuf := { buf with cache := cache }
                  let s' := currentSt.updateCurrentWorkspace fun ws =>
                    { ws with buffers := ws.buffers.map (fun (b : FileBuffer) => if b.id == buf.id then updatedBuf else b) }
                  (dl, s')
              | none => ("", currentSt)
        | none =>
            if let some lineStr := getLineFromBuffer buf lineIdx then
              let sub := ViE.Unicode.dropByDisplayWidthWithTabStop lineStr.toRawSubstring state.config.tabStop view.scrollCol.val
              let dl := ViE.Unicode.takeByDisplayWidthWithTabStop sub state.config.tabStop availableWidth
              let cache := match cachedRaw, cachedIdx with
                | some raw, some _ =>
                    if raw == lineStr then
                      buf.cache
                    else
                      (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndexWithTabStop lineStr state.config.tabStop))
                | _, _ =>
                    (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndexWithTabStop lineStr state.config.tabStop))
              let cache := (cache.update lineIdx dl view.scrollCol.val availableWidth).updateRaw lineIdx lineStr
              let updatedBuf := { buf with cache := cache }
              let s' := currentSt.updateCurrentWorkspace fun ws =>
                { ws with buffers := ws.buffers.map (fun (b : FileBuffer) => if b.id == buf.id then updatedBuf else b) }
              (dl, s')
            else
              ("", currentSt)
      currentSt := nextSt
      if state.config.showLineNumbers then
        winBuf := winBuf.push s!"{leftPad (toString (lineIdx.val + 1)) 3} "

      let isVisual := state.mode == Mode.visual || state.mode == Mode.visualBlock
      let selRange := if isVisual then state.selectionStart else none
      let (searchMatches, searchSt) := getLineSearchMatches currentSt buf.id lineIdx lineStr
      currentSt := searchSt

      let needsStyled := selRange.isSome || !searchMatches.isEmpty
      if !needsStyled then
        winBuf := winBuf.push displayLine
      else
        let mut styleActive := false
        let chars := displayLine.toList
        let mut dispIdx := 0
        let cursorByte :=
          if lineIdx == view.cursor.row then
            some (ViE.Unicode.displayColToByteOffsetFromIndex lineIndex view.cursor.col.val)
          else
            none
        let activeMatch := activeMatchRange searchMatches cursorByte
        for ch in chars do
          let chW := Unicode.charWidth ch
          let colVal := view.scrollCol.val + dispIdx
          let byteStart := ViE.Unicode.displayColToByteOffsetFromIndex lineIndex colVal
          let byteEnd := ViE.Unicode.displayColToByteOffsetFromIndex lineIndex (colVal + chW)
          let isSelected :=
            state.isInSelection lineIdx ⟨colVal⟩ ||
            (chW > 1 && state.isInSelection lineIdx ⟨colVal + 1⟩)
          let isMatched :=
            searchMatches.any (fun m => overlapsByteRange m byteStart byteEnd)
          let isActiveMatched :=
            match activeMatch with
            | some m => overlapsByteRange m byteStart byteEnd
            | none => false

          if isSelected then
            if !styleActive then
              winBuf := winBuf.push "\x1b[7m"
              styleActive := true
          else if isMatched then
            if !styleActive then
              if isActiveMatched then
                winBuf := winBuf.push state.config.searchHighlightCursorStyle
              else
                winBuf := winBuf.push state.config.searchHighlightStyle
              styleActive := true
          else if styleActive then
            winBuf := winBuf.push "\x1b[0m"
            styleActive := false

          winBuf := winBuf.push ch.toString
          dispIdx := dispIdx + chW

        if styleActive then
          winBuf := winBuf.push "\x1b[0m"
    else
      winBuf := winBuf.push state.config.emptyLineMarker

    winBuf := winBuf.push Terminal.clearLineStr

  let statusRow := r + workH
  let statusBuf := getWorkspaceBuffer currentSt view.bufferId
  winBuf := winBuf.push (Terminal.moveCursorStr statusRow c)
  let fileName := statusBuf.filename.getD "[No Name]"
  let modeStr := if windowId == currentSt.getCurrentWorkspace.activeWindowId then s!"-- {state.mode} --" else "--"
  let eolMark := if statusBuf.missingEol then " [noeol]" else ""
  let statusStr := s!"{modeStr} {fileName}{eolMark} [W:{windowId} B:{view.bufferId}] [{state.getCurrentWorkgroup.name}] {state.getCurrentWorkspace.name}"
  winBuf := winBuf.push state.config.statusBarStyle
  winBuf := winBuf.push statusStr.trimAscii.toString
  winBuf := winBuf.push Terminal.clearLineStr
  winBuf := winBuf.push state.config.resetStyle
  (winBuf, currentSt)

def renderFloatingWindow
    (st : EditorState)
    (view : ViewState)
    (rect : Rect)
    (borderFlags : FloatingWindowBorderFlags)
    : (Array String × Option (Nat × Nat)) := Id.run do
  let top := rect.row
  let left := rect.col
  let h := rect.height
  let w := rect.width
  let topBorderH := if borderFlags.top then 1 else 0
  let rightBorderW := if borderFlags.right then 1 else 0
  let bottomBorderH := if borderFlags.bottom then 1 else 0
  let leftBorderW := if borderFlags.left then 1 else 0
  let topBottomBorderH := topBorderH + bottomBorderH
  let sideBorderW := leftBorderW + rightBorderW
  if h < topBottomBorderH + 1 || w < sideBorderW + 1 then
    return (#[], none)
  let buf := getWorkspaceBuffer st view.bufferId
  let innerW := if w > sideBorderW then w - sideBorderW else 1
  let innerH := if h > topBottomBorderH then h - topBottomBorderH else 1
  let lnWidth := if st.config.showLineNumbers then 4 else 0
  let textW := if innerW > lnWidth then innerW - lnWidth else 1
  let repeatToken (token : String) (n : Nat) : String :=
    String.intercalate "" (List.replicate n token)
  let hBorder := if st.config.hSplitStr.isEmpty then "-" else st.config.hSplitStr
  let vBorder := if st.config.vSplitStr.isEmpty then "|" else st.config.vSplitStr
  let leftBorder := if borderFlags.left then vBorder else ""
  let rightBorder := if borderFlags.right then vBorder else ""
  let border := repeatToken hBorder w
  let mut out : Array String := #[]
  out := out.push st.config.resetStyle
  if borderFlags.top then
    out := out.push (Terminal.moveCursorStr top left)
    out := out.push border
  let isVisual := st.mode == Mode.visual || st.mode == Mode.visualBlock
  let hasSelection := isVisual && st.selectionStart.isSome
  for i in [0:innerH] do
    let lineIdx : Row := ⟨view.scrollRow.val + i⟩
    let raw := if lineIdx.val < FileBuffer.lineCount buf then getLineFromBuffer buf lineIdx |>.getD "" else ""
    let sub := ViE.Unicode.dropByDisplayWidthWithTabStop raw.toRawSubstring st.config.tabStop view.scrollCol.val
    let plainShown := ViE.Unicode.takeByDisplayWidthWithTabStop sub st.config.tabStop textW
    let shownW := Unicode.stringWidthWithTabStop plainShown st.config.tabStop
    let shown :=
      if hasSelection then
        Id.run do
          let mut styled : Array String := #[]
          let mut styleActive := false
          let mut dispCol := view.scrollCol.val
          for ch in plainShown.toList do
            let chW := Unicode.charWidth ch
            let selected :=
              st.isInSelection lineIdx ⟨dispCol⟩ ||
              (chW > 1 && st.isInSelection lineIdx ⟨dispCol + 1⟩)
            if selected then
              if !styleActive then
                styled := styled.push "\x1b[7m"
                styleActive := true
            else if styleActive then
              styled := styled.push st.config.resetStyle
              styleActive := false
            styled := styled.push ch.toString
            dispCol := dispCol + chW
          if styleActive then
            styled := styled.push st.config.resetStyle
          return String.intercalate "" styled.toList
      else
        plainShown
    let padW := if shownW < textW then textW - shownW else 0
    let pad := "".pushn ' ' padW
    let withNo :=
      if st.config.showLineNumbers then
        s!"{leftPad (toString (lineIdx.val + 1)) 3} {shown}{pad}"
      else
        s!"{shown}{pad}"
    out := out.push (Terminal.moveCursorStr (top + topBorderH + i) left)
    out := out.push s!"{leftBorder}{withNo}{rightBorder}"
  if borderFlags.bottom then
    out := out.push (Terminal.moveCursorStr (top + h - 1) left)
    out := out.push border
  out := out.push st.config.resetStyle

  let cursorPos : Option (Nat × Nat) :=
    if view.cursor.row.val < view.scrollRow.val then
      none
    else
      let visRow := view.cursor.row.val - view.scrollRow.val
      if visRow < innerH then
        let visCol := if view.cursor.col.val >= view.scrollCol.val then view.cursor.col.val - view.scrollCol.val else 0
        let colOff := if st.config.showLineNumbers then 4 else 0
        let c := min (innerW - 1) (colOff + visCol)
        some (top + topBorderH + visRow, left + leftBorderW + c)
      else
        none
  return (out, cursorPos)

end ViE.UI
