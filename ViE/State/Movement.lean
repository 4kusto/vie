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
  if cursor.col.val > 0 then
     s.setCursor { cursor with col := ⟨cursor.col.val - 1⟩ }
  else
     s

def EditorState.moveCursorRight (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  let limit := ViE.getLineLengthFromBuffer buffer cursor.row |>.getD 0

  if cursor.col.val < limit then
     s.setCursor { cursor with col := ⟨cursor.col.val + 1⟩ }
  else
     s

def EditorState.moveCursorUp (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  if cursor.row.val > 0 then
    let newRow : Row := ⟨cursor.row.val - 1⟩
    let lineLen := ViE.getLineLengthFromBuffer s.getActiveBuffer newRow |>.getD 0
    s.setCursor { cursor with row := newRow, col := ⟨min cursor.col.val lineLen⟩ }
  else
    s

def EditorState.moveCursorDown (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  if cursor.row.val < buffer.lineCount - 1 then
    let newRow : Row := ⟨cursor.row.val + 1⟩
    let lineLen := ViE.getLineLengthFromBuffer buffer newRow |>.getD 0
    s.setCursor { cursor with row := newRow, col := ⟨min cursor.col.val lineLen⟩ }
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
  let len := ViE.getLineLengthFromBuffer s.getActiveBuffer cursor.row |>.getD 0
  let newCol : Col := ⟨min (col - 1) len⟩ -- 1-indexed to 0-indexed, clamped
  let s' := s.setCursor { cursor with col := newCol }
  { s' with inputState := { s'.inputState with countBuffer := "" } }

def EditorState.jumpToLine (s : EditorState) (line : Nat) : EditorState :=
  let buffer := s.getActiveBuffer
  let maxLine := buffer.lineCount
  let newRowVal := if line == 0 then 0 else min (line - 1) (maxLine - 1)
  let newRow : Row := ⟨newRowVal⟩
  let lineLen := ViE.getLineLengthFromBuffer buffer newRow |>.getD 0
  let cursor := s.getCursor
  let newCol : Col := ⟨min cursor.col.val lineLen⟩
  let s' := s.setCursor { cursor with row := newRow, col := newCol }
  { s' with inputState := { s'.inputState with countBuffer := "" } }


def EditorState.moveToLineStart (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  s.setCursor { cursor with col := 0 }

def EditorState.moveToLineEnd (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let len := ViE.getLineLengthFromBuffer s.getActiveBuffer cursor.row |>.getD 0
  s.setCursor { cursor with col := ⟨len⟩ }

def EditorState.clampCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let len := ViE.getLineLengthFromBuffer s.getActiveBuffer cursor.row |>.getD 0
  match s.mode with
  | Mode.insert =>
    if cursor.col.val > len then
      s.setCursor { cursor with col := ⟨len⟩ }
    else
      s
  | _ => -- Normal, Visual etc.
    if len == 0 then
      s.setCursor { cursor with col := ⟨0⟩ }
    else if cursor.col.val >= len then
      s.setCursor { cursor with col := ⟨len - 1⟩ }
    else
      s


def isKeyword (c : Char) : Bool :=
  c.isAlphanum || c == '_'

mutual
  partial def findNextForward (buffer : FileBuffer) (row : Row) (col : Col) (started : Bool) : Row × Col :=
    let lineLen := ViE.getLineLengthFromBuffer buffer row |>.getD 0
    if lineLen == 0 then
       (row, 0) -- Stop at empty line
    else if col.val >= lineLen then
       -- End of line, wrap to next line
       if row.val + 1 < FileBuffer.lineCount buffer then
         let nextRow := row.succ
         let nextLen := ViE.getLineLengthFromBuffer buffer nextRow |>.getD 0
         if nextLen == 0 then
            (nextRow, 0) -- Stop at empty line
         else
            findNextForward buffer nextRow 0 true
       else
         (row, col) -- End of file
    else
      let lineStr := ViE.getLineFromBuffer buffer row |>.getD ""
      let c := List.getD lineStr.toList col.val ' '
      let isKw := isKeyword c
      let isSpace := c.isWhitespace
      if !started then
        if isSpace then
           findNextForward buffer row col.succ true
        else
           findNextWordEndForward buffer row col.succ isKw
      else
         if isSpace then
            findNextForward buffer row col.succ started
         else
            (row, col) -- Found start of next word



  partial def findNextWordEndForward (buffer : FileBuffer) (row : Row) (col : Col) (wasTv : Bool) : Row × Col :=
       let lineLen := ViE.getLineLengthFromBuffer buffer row |>.getD 0
       if col.val >= lineLen then
          if row.val + 1 < FileBuffer.lineCount buffer then
            findNextForward buffer row.succ 0 true
          else
            (row, col)
       else
          let lineStr := ViE.getLineFromBuffer buffer row |>.getD ""
          let c := List.getD lineStr.toList col.val ' '
          let isKw := isKeyword c
          let isSpace := c.isWhitespace
          if isSpace then
             findNextForward buffer row col.succ true
          else if isKw != wasTv then
             (row, col)
          else
             findNextWordEndForward buffer row col.succ wasTv
end

/-- Move forward to start of next word (w) -/
def EditorState.moveWordForward (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let currLineLen := ViE.getLineLengthFromBuffer buffer cursor.row |>.getD 0
  let (r, c) := if currLineLen == 0 then
                   if cursor.row.val + 1 < FileBuffer.lineCount buffer then
                      findNextForward buffer cursor.row.succ 0 true
                   else
                      (cursor.row, 0)
                else
                   let lineStr := ViE.getLineFromBuffer buffer cursor.row |>.getD ""
                   if cursor.col.val < currLineLen then
                      let ch := List.getD lineStr.toList cursor.col.val ' '
                      let isKw := isKeyword ch
                      let isSpace := ch.isWhitespace
                      if isSpace then
                         findNextForward buffer cursor.row cursor.col.succ true
                      else
                         findNextWordEndForward buffer cursor.row cursor.col.succ isKw
                   else
                      if cursor.row.val + 1 < FileBuffer.lineCount buffer then
                         findNextForward buffer cursor.row.succ 0 true
                      else
                         (cursor.row, ⟨currLineLen⟩)

  let finalLineLen := ViE.getLineLengthFromBuffer buffer r |>.getD 0
  let finalColVal := if r.val + 1 >= FileBuffer.lineCount buffer && c.val >= finalLineLen && finalLineLen > 0 && s.mode != Mode.insert then
                        finalLineLen - 1
                     else
                        min c.val finalLineLen
  s.setCursor { row := r, col := ⟨finalColVal⟩ }



mutual
    partial def findPrevStart (buffer : FileBuffer) (row : Row) (col : Col) : Row × Col :=
        let lineStr := ViE.getLineFromBuffer buffer row |>.getD ""
        let c := List.getD lineStr.toList col.val ' '
        if c.isWhitespace then
           if col.val == 0 then
              if row.val > 0 then
                 let prevRow := row.pred
                 let prevLen := ViE.getLineLengthFromBuffer buffer prevRow |>.getD 0
                 if prevLen > 0 then findPrevStart buffer prevRow ⟨prevLen - 1⟩ else (prevRow, 0)
              else (0, 0)
           else
              findPrevStart buffer row col.pred
        else
           let isKw := isKeyword c
           consumeWordBackward buffer row col isKw


    partial def consumeWordBackward (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) : Row × Col :=
        let lineStr := ViE.getLineFromBuffer buffer row |>.getD ""
        let c := List.getD lineStr.toList col.val ' '
        let isKw := isKeyword c
        if c.isWhitespace || isKw != wantKw then
           (row, col.succ)
        else
           if col.val == 0 then (row, 0)
           else consumeWordBackward buffer row col.pred wantKw

end

/-- Move backward to start of previous word (b) -/
def EditorState.moveWordBackward (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  if cursor.row.val == 0 && cursor.col.val == 0 then s
  else
      let lineLen := ViE.getLineLengthFromBuffer buffer cursor.row |>.getD 0
      let startCol : Col := if cursor.col.val >= lineLen then ⟨lineLen⟩ else cursor.col
      let (r, c) :=
         if startCol.val == 0 then
            if cursor.row.val > 0 then
               let prevRow := cursor.row.pred
               let prevLen := ViE.getLineLengthFromBuffer buffer prevRow |>.getD 0
               if prevLen > 0 then
                  findPrevStart buffer prevRow ⟨prevLen - 1⟩
               else
                  (prevRow, 0)
            else (0, 0)
         else
            findPrevStart buffer cursor.row startCol.pred
      s.setCursor { row := r, col := c }


mutual
    partial def findNextEnd (buffer : FileBuffer) (row : Row) (col : Col) : Row × Col :=
    let lineLen := ViE.getLineLengthFromBuffer buffer row |>.getD 0
    if col.val >= lineLen then
       if row.val + 1 < FileBuffer.lineCount buffer then
         findNextEnd buffer row.succ 0
       else
         (row, col)
    else
       let lineStr := ViE.getLineFromBuffer buffer row |>.getD ""
       let c := List.getD lineStr.toList col.val ' '
       if c.isWhitespace then
          findNextEnd buffer row col.succ
       else
          let isKw := isKeyword c
          consumeWordToEnd buffer row col isKw

     partial def consumeWordToEnd (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) : Row × Col :=
        let lineLen := ViE.getLineLengthFromBuffer buffer row |>.getD 0
        if col.val + 1 >= lineLen then
           (row, col)
        else
           let lineStr := ViE.getLineFromBuffer buffer row |>.getD ""
           let nextC := List.getD lineStr.toList (col.val + 1) ' '
           let nextKw := isKeyword nextC
           if nextC.isWhitespace || nextKw != wantKw then
              (row, col)
           else
              consumeWordToEnd buffer row col.succ wantKw
end

/-- Move to end of word (e) -/
def EditorState.moveWordEnd (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let currLineLen := ViE.getLineLengthFromBuffer buffer cursor.row |>.getD 0

  let startCol : Col := cursor.col.succ
  let (r, c) :=
      if startCol.val >= currLineLen then
         if cursor.row.val + 1 < FileBuffer.lineCount buffer then
            findNextEnd buffer cursor.row.succ 0
         else
            (cursor.row, ⟨currLineLen⟩)
      else
         findNextEnd buffer cursor.row startCol

  s.setCursor { row := r, col := c }


end ViE
