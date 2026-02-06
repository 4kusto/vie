import ViE.State.Config
import ViE.State.Layout
import ViE.State.Movement
import ViE.Types
import ViE.Buffer.Content
import ViE.Unicode

namespace ViE

def EditorState.startVisualMode (s : EditorState) : EditorState :=
  let s' := s.clampCursor
  { s' with mode := .visual, selectionStart := some s'.getCursor, message := "-- VISUAL --" }

def EditorState.startVisualBlockMode (s : EditorState) : EditorState :=
  let s' := s.clampCursor
  { s' with mode := .visualBlock, selectionStart := some s'.getCursor, message := "-- VISUAL BLOCK --" }

def EditorState.exitVisualMode (s : EditorState) : EditorState :=
  { s with mode := .normal, selectionStart := none, message := "" }

def normalizeRange (p1 p2 : Point) : (Point × Point) :=
  if p1.row < p2.row || (p1.row == p2.row && p1.col <= p2.col) then (p1, p2) else (p2, p1)

def EditorState.isInSelection (s : EditorState) (row : Row) (col : Col) : Bool :=
  match s.selectionStart with
  | none => false
  | some startPt =>
    if s.mode == .visualBlock then
       let cursor := s.getCursor
       let minRow := min startPt.row cursor.row
       let maxRow := max startPt.row cursor.row
       let minCol := min startPt.col cursor.col
       let maxCol := max startPt.col cursor.col
       row >= minRow && row <= maxRow && col >= minCol && col <= maxCol
    else if s.mode == .visual then
       let (p1, p2) := normalizeRange startPt s.getCursor
       if row < p1.row || row > p2.row then false
       else if row > p1.row && row < p2.row then true
       else if p1.row == p2.row then col >= p1.col && col <= p2.col
       else if row == p1.row then col >= p1.col
       else if row == p2.row then col <= p2.col
       else false
    else
       false

def EditorState.getSelectedText (s : EditorState) : String :=
  match s.selectionStart with
  | none => ""
  | some startPt =>
    let buffer := s.getActiveBuffer
    if s.mode == .visualBlock then
      let cursor := s.getCursor
      let minRow := (min startPt.row cursor.row).val
      let maxRow := (max startPt.row cursor.row).val
      let minCol := (min startPt.col cursor.col).val
      let maxCol := (max startPt.col cursor.col).val

      let lines := (List.range (maxRow - minRow + 1)).map fun i =>
        let r := minRow + i
        let line := ViE.getLineFromBuffer buffer ⟨r⟩ |>.getD ""
        let sub := ViE.Unicode.dropByDisplayWidth line.toRawSubstring minCol
        ViE.Unicode.takeByDisplayWidth sub (maxCol - minCol + 1)
      String.intercalate "\n" lines
    else
      let (p1, p2) := normalizeRange startPt s.getCursor
      let startOff := ViE.getOffsetFromPointInBuffer buffer p1.row.val p1.col.val |>.getD 0
      let lineStr := ViE.getLineFromBuffer buffer p2.row |>.getD ""
      let endCol := if p2.col.val < ViE.Unicode.stringWidth lineStr then
        ViE.Unicode.nextDisplayCol lineStr p2.col.val
      else
        p2.col.val
      let endOff := ViE.getOffsetFromPointInBuffer buffer p2.row.val endCol |>.getD buffer.table.tree.length
      PieceTree.getSubstring buffer.table.tree startOff (endOff - startOff) buffer.table

def EditorState.yankSelection (s : EditorState) : EditorState :=
  let text := s.getSelectedText
  let reg : Register :=
    if s.mode == .visualBlock then
      let lines := if text.isEmpty then [] else text.splitOn "\n"
      let width := lines.foldl (fun m l => max m (ViE.Unicode.stringWidth l)) 0
      {
        kind := .blockwise
        text := text
        blockLines := lines
        blockWidth := width
      }
    else
      {
        kind := .charwise
        text := text
        blockLines := []
        blockWidth := 0
      }
  { s.exitVisualMode with clipboard := some reg, message := s!"Yanked selection" }

def EditorState.deleteSelection (s : EditorState) : EditorState :=
  match s.selectionStart with
  | none => s
  | some startPt =>
    if s.mode == .visualBlock then
      let text := s.getSelectedText
      let lines := if text.isEmpty then [] else text.splitOn "\n"
      let width := lines.foldl (fun m l => max m (ViE.Unicode.stringWidth l)) 0
      let reg : Register := {
        kind := .blockwise
        text := text
        blockLines := lines
        blockWidth := width
      }
      let cursor := s.getCursor
      let minRow := (min startPt.row cursor.row).val
      let maxRow := (max startPt.row cursor.row).val
      let minCol := (min startPt.col cursor.col).val
      let maxCol := (max startPt.col cursor.col).val

      let s' := (List.range (maxRow - minRow + 1)).foldl (init := s) fun st i =>
        let r := minRow + i
        st.updateActiveBuffer fun buffer =>
          match buffer.table.getLineRange r with
          | some (lineStart, lineLen) =>
            let start := ViE.getOffsetFromPointInBuffer buffer r minCol |>.getD (lineStart + lineLen)
            let endCol := maxCol + 1
            let endOff := ViE.getOffsetFromPointInBuffer buffer r endCol |>.getD (lineStart + lineLen)
            let len := if endOff > start then endOff - start else 0
            if len > 0 then
              { buffer with table := buffer.table.delete start len start, dirty := true }
            else buffer
          | none => buffer
      { s'.exitVisualMode with clipboard := some reg } |>.setCursor { row := ⟨minRow⟩, col := ⟨minCol⟩ }
    else
      let text := s.getSelectedText
      let reg : Register := {
        kind := .charwise
        text := text
        blockLines := []
        blockWidth := 0
      }
      let (p1, p2) := normalizeRange startPt s.getCursor
      let s' := s.updateActiveBuffer fun buffer =>
        let startOff := ViE.getOffsetFromPointInBuffer buffer p1.row.val p1.col.val |>.getD 0
        let lineStr := ViE.getLineFromBuffer buffer p2.row |>.getD ""
        let endCol := if p2.col.val < ViE.Unicode.stringWidth lineStr then
          ViE.Unicode.nextDisplayCol lineStr p2.col.val
        else
          p2.col.val
        let endOff := ViE.getOffsetFromPointInBuffer buffer p2.row.val endCol |>.getD buffer.table.tree.length
        { buffer with table := buffer.table.delete startOff (endOff - startOff) startOff, dirty := true }
      { s'.exitVisualMode with clipboard := some reg } |>.setCursor p1

end ViE
