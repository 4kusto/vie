import ViE.State.Config
import ViE.State.Layout
import ViE.Types
import ViE.Buffer.Content

namespace ViE

def EditorState.getCursor (s : EditorState) : Point :=
  let wg := s.getCurrentWorkgroup
  match wg.layout.findView wg.activeWindowId with
  | some view => view.cursor
  | none => Point.zero

def EditorState.setCursor (s : EditorState) (p : Point) : EditorState :=
  s.updateActiveView fun v => { v with cursor := p }

def EditorState.setScroll (s : EditorState) (row : Row) (col : Col) : EditorState :=
  s.updateActiveView fun v => { v with scrollRow := row, scrollCol := col }


def EditorState.moveCursorLeft (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  -- let currentLine := getLine s.activeBufferContent cursor.row.val |>.getD ""
  if cursor.col.val > 0 then
     s.setCursor (Point.make cursor.row.val (cursor.col.val - 1))
  else
     s

def EditorState.moveCursorRight (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  let limit := getLineLengthFromBuffer buffer cursor.row.val |>.getD 0

  if cursor.col.val < limit then
     s.setCursor (Point.make cursor.row.val (cursor.col.val + 1))
  else
     s

def EditorState.moveCursorUp (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  if cursor.row.val > 0 then
    let newRow := cursor.row.val - 1
    let lineLen := getLineLengthFromBuffer s.getActiveBuffer newRow |>.getD 0
    s.setCursor (Point.make newRow (min cursor.col.val lineLen))
  else
    s

def EditorState.moveCursorDown (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  if cursor.row.val < buffer.lineCount - 1 then
    let newRow := cursor.row.val + 1
    let lineLen := getLineLengthFromBuffer buffer newRow |>.getD 0
    s.setCursor (Point.make newRow (min cursor.col.val lineLen))
  else
    s

def EditorState.clearInputState (s : EditorState) : EditorState :=
  { s with inputState := { s.inputState with countBuffer := "", previousKey := none } }

def EditorState.moveCursorLeftN (s : EditorState) (n : Nat) : EditorState :=
  n.repeat (fun s => s.moveCursorLeft) s

def EditorState.moveCursorRightN (s : EditorState) (n : Nat) : EditorState :=
  n.repeat (fun s => s.moveCursorRight) s

def EditorState.moveCursorUpN (s : EditorState) (n : Nat) : EditorState :=
  n.repeat (fun s => s.moveCursorUp) s

def EditorState.moveCursorDownN (s : EditorState) (n : Nat) : EditorState :=
  n.repeat (fun s => s.moveCursorDown) s


def EditorState.getCount (s : EditorState) : Nat :=
  match s.inputState.countBuffer.toNat? with
  | some n => n
  | none => 1

def EditorState.jumpToColumn (s : EditorState) (col : Nat) : EditorState :=
  let cursor := s.getCursor
  let len := getLineLengthFromBuffer s.getActiveBuffer cursor.row.val |>.getD 0
  let newCol := min (col - 1) len -- 1-indexed to 0-indexed, clamped
  let s' := s.setCursor (Point.make cursor.row.val newCol)
  { s' with inputState := { s'.inputState with countBuffer := "" } }

def EditorState.jumpToLine (s : EditorState) (line : Nat) : EditorState :=
  let buffer := s.getActiveBuffer
  let maxLine := buffer.lineCount
  let newRow := if line == 0 then 0 else min (line - 1) (maxLine - 1)
  let lineLen := getLineLengthFromBuffer buffer newRow |>.getD 0
  let cursor := s.getCursor
  let newCol := min cursor.col.val lineLen
  let s' := s.setCursor (Point.make newRow newCol)
  { s' with inputState := { s'.inputState with countBuffer := "" } }


def EditorState.moveToLineStart (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  s.setCursor { cursor with col := 0 }

def EditorState.moveToLineEnd (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let len := getLineLengthFromBuffer s.getActiveBuffer cursor.row.val |>.getD 0
  s.setCursor (Point.make cursor.row.val len)

def EditorState.clampCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let len := getLineLengthFromBuffer s.getActiveBuffer cursor.row.val |>.getD 0
  if cursor.col.val > len then
    s.setCursor (Point.make cursor.row.val len)
  else
    s

end ViE
