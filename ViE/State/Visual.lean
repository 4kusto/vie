import ViE.State.Config
import ViE.State.Layout
import ViE.State.Movement
import ViE.Types
import ViE.Buffer.Content

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

def EditorState.isInSelection (s : EditorState) (row col : Nat) : Bool :=
  match s.selectionStart with
  | none => false
  | some startPt =>
    if s.mode == .visualBlock then
       let cursor := s.getCursor
       let minRow := min startPt.row cursor.row
       let maxRow := max startPt.row cursor.row
       let minCol := min startPt.col cursor.col
       let maxCol := max startPt.col cursor.col
       row >= minRow.val && row <= maxRow.val && col >= minCol.val && col <= maxCol.val
    else if s.mode == .visual then
       let (p1, p2) := normalizeRange startPt s.getCursor
       if row < p1.row.val || row > p2.row.val then false
       else if row > p1.row.val && row < p2.row.val then true
       else if p1.row.val == p2.row.val then col >= p1.col.val && col <= p2.col.val
       else if row == p1.row.val then col >= p1.col.val
       else if row == p2.row.val then col <= p2.col.val
       else false
    else
       false

def EditorState.getSelectedText (s : EditorState) : TextBuffer :=
  match s.selectionStart with
  | none => #[]
  | some startPt =>
    if s.mode == .visualBlock then
      let cursor := s.getCursor
      let minRow := min startPt.row cursor.row
      let maxRow := max startPt.row cursor.row
      let minCol := min startPt.col cursor.col
      let maxCol := max startPt.col cursor.col
      let content := s.activeBufferContent
      (List.range (maxRow.val - minRow.val + 1)).toArray.map fun i =>
        let row := minRow.val + i
        let line := getLine content row |>.getD ""
        let chars := line.toList
        stringToLine (String.ofList (chars.drop minCol.val |>.take (maxCol.val - minCol.val + 1)))
    else
      let (p1, p2) := normalizeRange startPt s.getCursor
      let content := s.activeBufferContent
      if p1.row == p2.row then
        let line := getLine content p1.row.val |>.getD ""
        let chars := line.toList
        #[stringToLine (String.ofList (chars.drop p1.col.val |>.take (p2.col.val - p1.col.val + 1)))]
      else
        let firstLine := getLine content p1.row.val |>.getD ""
        let lastLine := getLine content p2.row.val |>.getD ""
        let midLines := arrayDrop (arrayTake content p2.row.val) (p1.row.val + 1)
        let firstPart := stringToLine (String.ofList (firstLine.toList.drop p1.col.val))
        let lastPart := stringToLine (String.ofList (lastLine.toList.take (p2.col.val + 1)))
        arrayConcat [#[firstPart], midLines, #[lastPart]]


def EditorState.yankSelection (s : EditorState) : EditorState :=
  let text := s.getSelectedText
  { s.exitVisualMode with clipboard := some text, message := s!"Yanked {text.size} lines" }

def EditorState.deleteSelection (s : EditorState) : EditorState :=
  match s.selectionStart with
  | none => s
  | some startPt =>
    if s.mode == .visualBlock then
      let cursor := s.getCursor
      let minRow := min startPt.row cursor.row
      let maxRow := max startPt.row cursor.row
      let minCol := min startPt.col cursor.col
      let maxCol := max startPt.col cursor.col
      let s' := s.updateActiveBufferContent fun buffer =>
         buffer.mapIdx fun i lineArr =>
           let line := lineToString lineArr
           if i >= minRow.val && i <= maxRow.val then
             let chars := line.toList
             if minCol.val < chars.length then
               let before := chars.take minCol.val
               let after := chars.drop (maxCol.val + 1)
               stringToLine (String.ofList (before ++ after))
             else
               lineArr
           else
             lineArr
      (s'.setCursor (Point.make minRow.val minCol.val)).exitVisualMode
    else
      let (p1, p2) := normalizeRange startPt s.getCursor
      let s' := s.updateActiveBufferContent fun buffer =>
        if p1.row == p2.row then
          modifyLine buffer p1.row.val fun line =>
            let chars := line.toList
            let before := chars.take p1.col.val
            let after := chars.drop (p2.col.val + 1)
            String.ofList (before ++ after)
        else
          let beforeLines := arrayTake buffer p1.row.val
          let afterLines := arrayDrop buffer (p2.row.val + 1)
          let firstLine := getLine buffer p1.row.val |>.getD ""
          let lastLine := getLine buffer p2.row.val |>.getD ""
          let newJoinedLine := stringToLine (String.ofList (firstLine.toList.take p1.col.val ++ lastLine.toList.drop (p2.col.val + 1)))
          arrayConcat [beforeLines, #[newJoinedLine], afterLines]
      (s'.setCursor p1).exitVisualMode

end ViE
