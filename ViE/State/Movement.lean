import ViE.State.Config
import ViE.State.Layout
import ViE.Types
import ViE.Buffer.Content
import ViE.Unicode

namespace ViE

def EditorState.getCursor (s : EditorState) : Point :=
  let ws := s.getCurrentWorkspace
  match ws.layout.findView ws.activeWindowId with
  | some view => view.cursor
  | none => Point.zero

def EditorState.setCursor (s : EditorState) (p : Point) : EditorState :=
  s.updateActiveView fun v => { v with cursor := p }

def EditorState.setScroll (s : EditorState) (row : Row) (col : Col) : EditorState :=
  s.updateActiveView fun v => { v with scrollRow := row, scrollCol := col }

def lineString (buffer : FileBuffer) (row : Row) : String :=
  ViE.getLineFromBuffer buffer row |>.getD ""

def lineDisplayWidth (buffer : FileBuffer) (row : Row) : Nat :=
  ViE.getLineLengthFromBuffer buffer row |>.getD 0

def charAtDisplayCol (lineStr : String) (col : Col) : Char :=
  let idx := ViE.Unicode.displayColToCharIndex lineStr col.val
  List.getD lineStr.toList idx ' '

def nextCol (buffer : FileBuffer) (row : Row) (col : Col) : Col :=
  let lineStr := lineString buffer row
  ⟨ViE.Unicode.nextDisplayCol lineStr col.val⟩

def prevCol (buffer : FileBuffer) (row : Row) (col : Col) : Col :=
  let lineStr := lineString buffer row
  ⟨ViE.Unicode.prevDisplayCol lineStr col.val⟩

def EditorState.moveCursorLeft (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  if cursor.col.val > 0 then
     let newCol := prevCol s.getActiveBuffer cursor.row cursor.col
     s.setCursor { cursor with col := newCol }
  else
     s

def EditorState.moveCursorRight (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  let limit := lineDisplayWidth buffer cursor.row
  let newCol := nextCol buffer cursor.row cursor.col

  if cursor.col.val < limit && newCol.val != cursor.col.val then
     s.setCursor { cursor with col := newCol }
  else
     s

def EditorState.moveCursorUp (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  if cursor.row.val > 0 then
    let newRow : Row := ⟨cursor.row.val - 1⟩
    let lineLen := lineDisplayWidth s.getActiveBuffer newRow
    s.setCursor { cursor with row := newRow, col := ⟨min cursor.col.val lineLen⟩ }
  else
    s

def EditorState.moveCursorDown (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  if cursor.row.val < buffer.lineCount - 1 then
    let newRow : Row := ⟨cursor.row.val + 1⟩
    let lineLen := lineDisplayWidth buffer newRow
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
  let len := lineDisplayWidth s.getActiveBuffer cursor.row
  let newCol : Col := ⟨min (col - 1) len⟩ -- 1-indexed to 0-indexed, clamped
  let s' := s.setCursor { cursor with col := newCol }
  { s' with inputState := { s'.inputState with countBuffer := "" } }

def EditorState.jumpToLine (s : EditorState) (line : Nat) : EditorState :=
  let buffer := s.getActiveBuffer
  let maxLine := buffer.lineCount
  let newRowVal := if line == 0 then 0 else min (line - 1) (maxLine - 1)
  let newRow : Row := ⟨newRowVal⟩
  let lineLen := lineDisplayWidth buffer newRow
  let cursor := s.getCursor
  let newCol : Col := ⟨min cursor.col.val lineLen⟩
  let s' := s.setCursor { cursor with row := newRow, col := newCol }
  { s' with inputState := { s'.inputState with countBuffer := "" } }


def EditorState.moveToLineStart (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  s.setCursor { cursor with col := 0 }

def EditorState.moveToLineEnd (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let len := lineDisplayWidth s.getActiveBuffer cursor.row
  s.setCursor { cursor with col := ⟨len⟩ }

def EditorState.clampCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let len := lineDisplayWidth s.getActiveBuffer cursor.row
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
    let lineLen := lineDisplayWidth buffer row
    if lineLen == 0 then
       (row, 0) -- Stop at empty line
    else if col.val >= lineLen then
       -- End of line, wrap to next line
       if row.val + 1 < FileBuffer.lineCount buffer then
         let nextRow := row.succ
         let nextLen := lineDisplayWidth buffer nextRow
         if nextLen == 0 then
            (nextRow, 0) -- Stop at empty line
         else
            findNextForward buffer nextRow 0 true
       else
         (row, col) -- End of file
    else
      let lineStr := lineString buffer row
      let c := charAtDisplayCol lineStr col
      let isKw := isKeyword c
      let isSpace := c.isWhitespace
      if !started then
        if isSpace then
           findNextForward buffer row (nextCol buffer row col) true
        else
           findNextWordEndForward buffer row (nextCol buffer row col) isKw
      else
         if isSpace then
            findNextForward buffer row (nextCol buffer row col) started
         else
            (row, col) -- Found start of next word



  partial def findNextWordEndForward (buffer : FileBuffer) (row : Row) (col : Col) (wasTv : Bool) : Row × Col :=
       let lineLen := lineDisplayWidth buffer row
       if col.val >= lineLen then
          if row.val + 1 < FileBuffer.lineCount buffer then
            findNextForward buffer row.succ 0 true
          else
            (row, col)
       else
          let lineStr := lineString buffer row
          let c := charAtDisplayCol lineStr col
          let isKw := isKeyword c
          let isSpace := c.isWhitespace
          if isSpace then
             findNextForward buffer row (nextCol buffer row col) true
          else if isKw != wasTv then
             (row, col)
          else
             findNextWordEndForward buffer row (nextCol buffer row col) wasTv
end

/-- Move forward to start of next word (w) -/
def EditorState.moveWordForward (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let currLineLen := lineDisplayWidth buffer cursor.row
  let (r, c) := if currLineLen == 0 then
                   if cursor.row.val + 1 < FileBuffer.lineCount buffer then
                      findNextForward buffer cursor.row.succ 0 true
                   else
                      (cursor.row, 0)
                else
                   let lineStr := lineString buffer cursor.row
                   if cursor.col.val < currLineLen then
                      let ch := charAtDisplayCol lineStr cursor.col
                      let isKw := isKeyword ch
                      let isSpace := ch.isWhitespace
                      if isSpace then
                         findNextForward buffer cursor.row (nextCol buffer cursor.row cursor.col) true
                      else
                         findNextWordEndForward buffer cursor.row (nextCol buffer cursor.row cursor.col) isKw
                   else
                      if cursor.row.val + 1 < FileBuffer.lineCount buffer then
                         findNextForward buffer cursor.row.succ 0 true
                      else
                         (cursor.row, ⟨currLineLen⟩)

  let finalLineLen := lineDisplayWidth buffer r
  let finalColVal := if r.val + 1 >= FileBuffer.lineCount buffer && c.val >= finalLineLen && finalLineLen > 0 && s.mode != Mode.insert then
                        finalLineLen - 1
                     else
                        min c.val finalLineLen
  s.setCursor { row := r, col := ⟨finalColVal⟩ }



mutual
  partial def findPrevStart (buffer : FileBuffer) (row : Row) (col : Col) : Row × Col :=
        let lineStr := lineString buffer row
        let c := charAtDisplayCol lineStr col
        if c.isWhitespace then
           if col.val == 0 then
              if row.val > 0 then
                 let prevRow := row.pred
                 let prevLen := lineDisplayWidth buffer prevRow
                 if prevLen > 0 then findPrevStart buffer prevRow ⟨prevLen - 1⟩ else (prevRow, 0)
              else (0, 0)
           else
              findPrevStart buffer row (prevCol buffer row col)
        else
           let isKw := isKeyword c
           consumeWordBackward buffer row col isKw


    partial def consumeWordBackward (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) : Row × Col :=
        let lineStr := lineString buffer row
        let c := charAtDisplayCol lineStr col
        let isKw := isKeyword c
        if c.isWhitespace || isKw != wantKw then
           (row, nextCol buffer row col)
        else
           if col.val == 0 then (row, 0)
           else consumeWordBackward buffer row (prevCol buffer row col) wantKw

end

/-- Move backward to start of previous word (b) -/
def EditorState.moveWordBackward (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  if cursor.row.val == 0 && cursor.col.val == 0 then s
  else
      let lineLen := lineDisplayWidth buffer cursor.row
      let startCol : Col := if cursor.col.val >= lineLen then ⟨lineLen⟩ else cursor.col
      let (r, c) :=
         if startCol.val == 0 then
            if cursor.row.val > 0 then
               let prevRow := cursor.row.pred
               let prevLen := lineDisplayWidth buffer prevRow
               if prevLen > 0 then
                  findPrevStart buffer prevRow ⟨prevLen - 1⟩
               else
                  (prevRow, 0)
            else (0, 0)
         else
            findPrevStart buffer cursor.row (prevCol buffer cursor.row startCol)
      s.setCursor { row := r, col := c }


mutual
  partial def findNextEnd (buffer : FileBuffer) (row : Row) (col : Col) : Row × Col :=
    let lineLen := lineDisplayWidth buffer row
    if col.val >= lineLen then
       if row.val + 1 < FileBuffer.lineCount buffer then
         findNextEnd buffer row.succ 0
       else
         (row, col)
    else
       let lineStr := lineString buffer row
       let c := charAtDisplayCol lineStr col
       if c.isWhitespace then
          findNextEnd buffer row (nextCol buffer row col)
       else
          let isKw := isKeyword c
          consumeWordToEnd buffer row col isKw

     partial def consumeWordToEnd (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) : Row × Col :=
        let lineLen := lineDisplayWidth buffer row
        let nextColVal := (nextCol buffer row col).val
        if nextColVal >= lineLen then
           (row, col)
        else
           let lineStr := lineString buffer row
           let nextC := charAtDisplayCol lineStr (nextCol buffer row col)
           let nextKw := isKeyword nextC
           if nextC.isWhitespace || nextKw != wantKw then
              (row, col)
           else
              consumeWordToEnd buffer row (nextCol buffer row col) wantKw
end

/-- Move to end of word (e) -/
def EditorState.moveWordEnd (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let currLineLen := lineDisplayWidth buffer cursor.row

  let startCol : Col := nextCol buffer cursor.row cursor.col
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
