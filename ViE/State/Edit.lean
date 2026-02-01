import ViE.State.Config
import ViE.State.Layout
import ViE.State.Movement
import ViE.Types
import ViE.Buffer.Content

namespace ViE

def EditorState.setMode (s : EditorState) (m : Mode) : EditorState :=
  { s with mode := m }

def EditorState.insertChar (s : EditorState) (c : Char) : EditorState :=
  let cursor := s.getCursor
  let row := cursor.row.val
  let col := cursor.col.val
  let s' := s.updateActiveBuffer fun buffer =>
    modifyLineInBuffer buffer row fun line =>
      let chars := line.toList
      let newChars := (chars.take col) ++ [c] ++ (chars.drop col)
      String.ofList newChars

  s'.setCursor (Point.make row (col + 1))

def EditorState.insertNewline (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let row := cursor.row.val
  let col := cursor.col.val
  let currentLine := getLine s.activeBufferContent row |>.getD ""
  let chars := currentLine.toList
  let beforeSplit := String.ofList (chars.take col)
  let afterSplit := String.ofList (chars.drop col)

  let s' := s.updateActiveBufferContent fun buffer =>
    let beforeLines := arrayTake buffer row
    let afterLines := arrayDrop buffer (row + 1)
    arrayConcat [beforeLines, #[stringToLine beforeSplit, stringToLine afterSplit], afterLines]

  s'.setCursor (Point.make (row + 1) 0)

def EditorState.deleteBeforeCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let row := cursor.row.val
  let col := cursor.col.val
  if col > 0 then
    -- Delete char before cursor
    let s' := s.updateActiveBufferContent fun buffer =>
      modifyLine buffer row fun line =>
        let chars := line.toList
        let newChars := (chars.take (col - 1)) ++ (chars.drop col)
        String.ofList newChars
    s'.setCursor (Point.make row (col - 1))
  else if row > 0 then
    -- At start of line: join with previous line
    let prevRow := row - 1
    let prevLine := getLine s.activeBufferContent prevRow |>.getD ""
    let currentLine := getLine s.activeBufferContent row |>.getD ""
    let mergedLine := prevLine ++ currentLine
    let newCol := prevLine.length

    let s' := s.updateActiveBufferContent fun buffer =>
      let beforeLines := arrayTake buffer prevRow
      let afterLines := arrayDrop buffer (row + 1)
      arrayConcat [beforeLines, #[stringToLine mergedLine], afterLines]

    s'.setCursor (Point.make prevRow newCol)
  else
    s


def deleteLine (buffer : TextBuffer) (row : Nat) : TextBuffer :=
  let before := arrayTake buffer row
  let after := arrayDrop buffer (row + 1)
  if before.isEmpty && after.isEmpty then
    emptyTextBuffer -- Minimum one empty line
  else
    before ++ after

def EditorState.deleteCurrentLine (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let s' := s.updateActiveBufferContent fun (buffer : TextBuffer) => deleteLine buffer cursor.row.val
  let newBuffer := s'.activeBufferContent
  let newRow := min cursor.row.val (newBuffer.size.pred)
  let currentLineLen := (getLine newBuffer newRow).map String.length |>.getD 0
  let newCol := min cursor.col.val currentLineLen
  let s'' := s'.setCursor (Point.make newRow newCol)
  { s'' with
    inputState := { s''.inputState with previousKey := none },
    message := "Deleted line"
  }


def EditorState.insertLineBelow (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let s' := s.updateActiveBufferContent fun buffer =>
    let before := arrayTake buffer (cursor.row.val + 1)
    let after := arrayDrop buffer (cursor.row.val + 1)
    arrayConcat [before, #[#[]], after]
  s'.setCursor (Point.make (cursor.row.val + 1) 0)

def EditorState.insertLineAbove (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let s' := s.updateActiveBufferContent fun buffer =>
    let before := arrayTake buffer cursor.row.val
    let after := arrayDrop buffer cursor.row.val
    arrayConcat [before, #[#[]], after]
  s'.setCursor (Point.make cursor.row.val 0)

def EditorState.yankCurrentLine (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let line := getLine s.activeBufferContent cursor.row.val |>.getD ""
  { s with clipboard := some #[stringToLine line], message := "Yanked 1 line" }

def EditorState.pasteBelow (s : EditorState) : EditorState :=
  match s.clipboard with
  | none => { s with message := "Clipboard empty" }
  | some lines =>
    let cursor := s.getCursor
    let s' := s.updateActiveBufferContent fun buffer =>
      let before := arrayTake buffer (cursor.row.val + 1)
      let after := arrayDrop buffer (cursor.row.val + 1)
      arrayConcat [before, lines, after]
    s'.setCursor (Point.make (cursor.row.val + lines.size) 0)

def EditorState.pasteAbove (s : EditorState) : EditorState :=
  match s.clipboard with
  | none => { s with message := "Clipboard empty" }
  | some lines =>
    let cursor := s.getCursor
    let s' := s.updateActiveBufferContent fun buffer =>
      let before := arrayTake buffer cursor.row.val
      let after := arrayDrop buffer cursor.row.val
      arrayConcat [before, lines, after]
    s'.setCursor (Point.make cursor.row.val 0)

end ViE
