import ViE.State
import ViE.Terminal
import ViE.Config
import ViE.Unicode
import ViE.Color

namespace ViE.UI
open ViE
/-- Find all occurrences of a byte pattern within a byte array. -/
partial def findAllMatchesBytes (haystack : ByteArray) (needle : ByteArray) : Array (Nat × Nat) :=
  let n := needle.size
  let h := haystack.size
  if n == 0 || h < n then
    #[]
  else
    let rec matchesAt (i j : Nat) : Bool :=
      if j == n then true
      else if haystack[i + j]! == needle[j]! then matchesAt i (j + 1) else false
    let rec loop (i : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
      if i + n > h then acc
      else
        let acc' := if matchesAt i 0 then acc.push (i, i + n) else acc
        loop (i + 1) acc'
    loop 0 #[]

def updateSearchLineCache (st : EditorState) (lineIdx : Row) (lineStr : String) (matchRanges : Array (Nat × Nat)) : EditorState :=
  match st.searchState with
  | none => st
  | some ss =>
      let lineMatches := ss.lineMatches.insert lineIdx (lineStr, matchRanges)
      let order :=
        if ss.lineOrder.contains lineIdx then
          ss.lineOrder
        else
          ss.lineOrder.push lineIdx
      let (lineMatches, order) :=
        if order.size > ss.lineCacheMax then
          let dropCount := order.size - ss.lineCacheMax
          let evicted := order.extract 0 dropCount
          let order := order.extract dropCount order.size
          let lineMatches := evicted.foldl (fun acc r => acc.erase r) lineMatches
          (lineMatches, order)
        else
          (lineMatches, order)
      { st with searchState := some { ss with lineMatches := lineMatches, lineOrder := order } }
/-- Pad a string on the left with spaces until it reaches the given width. -/
def leftPad (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else "".pushn ' ' (width - s.length) ++ s

/-- Take characters from substring until visual width limit is reached. -/
def takeVisual (s : Substring.Raw) (width : Nat) : String :=
  Unicode.takeByDisplayWidth s width

/-- Render the current editor state to the terminal. -/
def render (state : EditorState) : IO EditorState := do
  if !state.dirty then return state
  -- Start building the frame buffer
  let mut buffer : Array String := #[]

  buffer := buffer.push Terminal.hideCursorStr
  buffer := buffer.push Terminal.homeCursorStr

  let (rows, cols) ← Terminal.getWindowSize

  let ws := state.getCurrentWorkspace
  let getBuffer (st : EditorState) (id : Nat) : FileBuffer :=
    let ws := st.getCurrentWorkspace
    ws.buffers.find? (fun b => b.id == id) |>.getD initialFileBuffer

  let rec renderLayout (l : Layout) (st : EditorState) (r c h w : Nat) : (Array String × EditorState) := Id.run do
    match l with
    | Layout.window id view =>
      let prefetchSearchMatches (st : EditorState) (buf : FileBuffer) (startRow endRow : Nat) : EditorState :=
        match st.searchState with
        | none => st
        | some ss =>
            if ss.pattern.isEmpty then
              st
            else
              let totalLines := FileBuffer.lineCount buf
              let rec loop (row : Nat) (acc : EditorState) : EditorState :=
                if row >= endRow then
                  acc
                else if row >= totalLines then
                  acc
                else
                  let lineIdx : Row := ⟨row⟩
                  let lineStr := getLineFromBuffer buf lineIdx |>.getD ""
                  match acc.searchState with
                  | none => acc
                  | some ss2 =>
                      match ss2.lineMatches.find? lineIdx with
                      | some (cachedLine, _) =>
                          if cachedLine == lineStr then
                            loop (row + 1) acc
                          else
                            let matchRanges := findAllMatchesBytes lineStr.toUTF8 ss2.pattern.toUTF8
                            let acc' := updateSearchLineCache acc lineIdx lineStr matchRanges
                            loop (row + 1) acc'
                      | none =>
                          let matchRanges := findAllMatchesBytes lineStr.toUTF8 ss2.pattern.toUTF8
                          let acc' := updateSearchLineCache acc lineIdx lineStr matchRanges
                          loop (row + 1) acc'
              loop startRow st

      let workH := if h > 0 then h - 1 else 0
      let buf := getBuffer st view.bufferId
      let mut currentSt := st
      let mut winBuf : Array String := #[]

      let prefetchMargin := 20
      let totalLines := FileBuffer.lineCount buf
      let startRow := if view.scrollRow.val > prefetchMargin then view.scrollRow.val - prefetchMargin else 0
      let endRow := min totalLines (view.scrollRow.val + workH + prefetchMargin)
      currentSt := prefetchSearchMatches currentSt buf startRow endRow

      for i in [0:workH] do
        let lineIdx : Row := ⟨view.scrollRow.val + i⟩
        let screenRow := r + i

        -- Position cursor for this line
        winBuf := winBuf.push (Terminal.moveCursorStr screenRow c)

        if lineIdx.val < FileBuffer.lineCount buf then
           -- Check cache
           let lnWidth := if st.config.showLineNumbers then 4 else 0
           let availableWidth := if w > lnWidth then w - lnWidth else 0

           let cachedLine := buf.cache.find lineIdx
           let cachedRaw := buf.cache.findRaw lineIdx
           let cachedIdx := buf.cache.findIndex lineIdx
           let lineStr := cachedRaw.getD (getLineFromBuffer buf lineIdx |>.getD "")
           let lineIndex := cachedIdx.getD (ViE.Unicode.buildDisplayByteIndex lineStr)
           let (displayLine, nextSt) := match cachedLine with
             | some (s, cachedScrollCol, cachedWidth) =>
               if cachedScrollCol == view.scrollCol.val && cachedWidth == availableWidth then
                 (s, currentSt)
               else
                 -- Cache miss; fall through to recompute.
                 match getLineFromBuffer buf lineIdx with
                 | some lineStr =>
                   let sub := ViE.Unicode.dropByDisplayWidth lineStr.toRawSubstring view.scrollCol.val
                   let dl := takeVisual sub availableWidth
                   let cache := match cachedRaw, cachedIdx with
                     | some raw, some _ =>
                       if raw == lineStr then
                         buf.cache
                       else
                         (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndex lineStr))
                     | _, _ =>
                       (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndex lineStr))
                   let cache := (cache.update lineIdx dl view.scrollCol.val availableWidth).updateRaw lineIdx lineStr
                   let updatedBuf := { buf with cache := cache }
                   let s' := currentSt.updateCurrentWorkspace fun ws =>
                     { ws with buffers := ws.buffers.map (fun (b : FileBuffer) => if b.id == buf.id then updatedBuf else b) }
                   (dl, s')
                 | none => ("", currentSt)
             | none =>
               if let some lineStr := getLineFromBuffer buf lineIdx then
                 let sub := ViE.Unicode.dropByDisplayWidth lineStr.toRawSubstring view.scrollCol.val
                 let dl := takeVisual sub availableWidth
                 let cache := match cachedRaw, cachedIdx with
                   | some raw, some _ =>
                     if raw == lineStr then
                       buf.cache
                     else
                       (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndex lineStr))
                   | _, _ =>
                     (buf.cache.updateIndex lineIdx (ViE.Unicode.buildDisplayByteIndex lineStr))
                 -- Update cache in currentSt
                 let cache := (cache.update lineIdx dl view.scrollCol.val availableWidth).updateRaw lineIdx lineStr
                 let updatedBuf := { buf with cache := cache }
                 let s' := currentSt.updateCurrentWorkspace fun ws =>
                   { ws with buffers := ws.buffers.map (fun (b : FileBuffer) => if b.id == buf.id then updatedBuf else b) }
                 (dl, s')
               else ("", currentSt)

           currentSt := nextSt
           if st.config.showLineNumbers then
             winBuf := winBuf.push s!"{leftPad (toString (lineIdx.val + 1)) 3} "

           let isVisual := st.mode == Mode.visual || st.mode == Mode.visualBlock
           let selRange := if isVisual then st.selectionStart else none
           let (searchMatches, searchSt) :=
             match st.searchState with
             | some ss =>
                if ss.pattern.isEmpty then
                  (#[], currentSt)
                else
                  match ss.lineMatches.find? lineIdx with
                  | some (cachedLine, cachedMatches) =>
                      if cachedLine == lineStr then
                        (cachedMatches, currentSt)
                      else
                        let matchRanges := findAllMatchesBytes lineStr.toUTF8 ss.pattern.toUTF8
                        let st' := updateSearchLineCache currentSt lineIdx lineStr matchRanges
                        (matchRanges, st')
                  | none =>
                      let matchRanges := findAllMatchesBytes lineStr.toUTF8 ss.pattern.toUTF8
                      let st' := updateSearchLineCache currentSt lineIdx lineStr matchRanges
                      (matchRanges, st')
             | none => (#[], currentSt)
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
             for ch in chars do
                let w := Unicode.charWidth ch
                let colVal := view.scrollCol.val + dispIdx
                let byteStart := ViE.Unicode.displayColToByteOffsetFromIndex lineIndex colVal
                let byteEnd := ViE.Unicode.displayColToByteOffsetFromIndex lineIndex (colVal + w)
                let isSelected :=
                  st.isInSelection lineIdx ⟨colVal⟩ ||
                  (w > 1 && st.isInSelection lineIdx ⟨colVal + 1⟩)
                let isMatched :=
                  searchMatches.any (fun (s, e) => byteStart < e && byteEnd > s)
                let isCursorMatch :=
                  match cursorByte with
                  | some cb => searchMatches.any (fun (s, e) => s <= cb && cb < e)
                  | none => false

                if isSelected then
                  if !styleActive then
                    winBuf := winBuf.push "\x1b[7m" -- Inverse video
                    styleActive := true
                else if isMatched then
                  if !styleActive then
                    if isCursorMatch then
                      winBuf := winBuf.push st.config.searchHighlightCursorStyle
                    else
                      winBuf := winBuf.push st.config.searchHighlightStyle
                    styleActive := true
                else if styleActive then
                  winBuf := winBuf.push "\x1b[0m"
                  styleActive := false

                winBuf := winBuf.push ch.toString
                dispIdx := dispIdx + w

             if styleActive then winBuf := winBuf.push "\x1b[0m"
        else
           winBuf := winBuf.push st.config.emptyLineMarker

        -- Clear the rest of the line
        winBuf := winBuf.push Terminal.clearLineStr

      let statusRow := r + workH
      winBuf := winBuf.push (Terminal.moveCursorStr statusRow c)
      let fileName := buf.filename.getD "[No Name]"
      let modeStr := if id == currentSt.getCurrentWorkspace.activeWindowId then s!"-- {st.mode} --" else "--"
      let eolMark := if buf.missingEol then " [noeol]" else ""
      let statusStr := s!"{modeStr} {fileName}{eolMark} [W:{id} B:{view.bufferId}] [{st.getCurrentWorkgroup.name}] {st.getCurrentWorkspace.name}"
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
  let (layoutStr, state) := renderLayout ws.layout state 0 0 layoutH cols
  buffer := buffer ++ layoutStr

  -- Global Status / Command Line
  buffer := buffer.push (Terminal.moveCursorStr (rows - 1) 0)
  let statusRight :=
    if state.mode == .command then s!":{state.inputState.commandBuffer}"
    else if state.mode == .searchForward then s!"/{state.inputState.commandBuffer}"
    else if state.mode == .searchBackward then s!"?{state.inputState.commandBuffer}"
    else state.message
  buffer := buffer.push statusRight
  buffer := buffer.push Terminal.clearLineStr

  -- Set Physical Cursor
  let rec getCursorPos (l : Layout) (r c h w : Nat) : Option (Nat × Nat) :=
    match l with
    | Layout.window id view =>
      if id == ws.activeWindowId then
--         let buf := getBuffer state view.bufferId
         let workH := if h > 0 then h - 1 else 0
         let colOffset := if state.config.showLineNumbers then 4 else 0
         let visualRow := view.cursor.row.val - view.scrollRow.val

         if visualRow >= 0 && visualRow < workH then
--             let rIdx : Row := ⟨view.scrollRow.val + visualRow⟩
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

  buffer := buffer.push (
    match getCursorPos ws.layout 0 0 layoutH cols with
    | some (pr, pc) => Terminal.moveCursorStr pr pc
    | none => "" -- Cursor hidden or out of view
  )

  if state.mode == .command then
     buffer := buffer.push (Terminal.moveCursorStr (rows - 1) (1 + state.inputState.commandBuffer.length))
  if state.mode == .searchForward || state.mode == .searchBackward then
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
