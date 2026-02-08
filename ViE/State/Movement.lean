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

def lineDisplayWidth (tabStop : Nat) (buffer : FileBuffer) (row : Row) : Nat :=
  ViE.getLineLengthFromBufferWithTabStop buffer row tabStop |>.getD 0

def charAtDisplayCol (tabStop : Nat) (lineStr : String) (col : Col) : Char :=
  let idx := ViE.Unicode.displayColToCharIndexWithTabStop lineStr tabStop col.val
  List.getD lineStr.toList idx ' '

def nextCol (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) : Col :=
  let lineStr := lineString buffer row
  ⟨ViE.Unicode.nextDisplayColWithTabStop lineStr tabStop col.val⟩

def prevCol (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) : Col :=
  let lineStr := lineString buffer row
  ⟨ViE.Unicode.prevDisplayColWithTabStop lineStr tabStop col.val⟩

def EditorState.moveCursorLeft (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  if cursor.col.val > 0 then
     let newCol := prevCol tabStop s.getActiveBuffer cursor.row cursor.col
     s.setCursor { cursor with col := newCol }
  else
     s

def EditorState.moveCursorRight (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  let limit := lineDisplayWidth tabStop buffer cursor.row
  let newCol := nextCol tabStop buffer cursor.row cursor.col

  if cursor.col.val < limit && newCol.val != cursor.col.val then
     s.setCursor { cursor with col := newCol }
  else
     s

def EditorState.moveCursorUp (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  if cursor.row.val > 0 then
    let newRow : Row := ⟨cursor.row.val - 1⟩
    let lineLen := lineDisplayWidth tabStop s.getActiveBuffer newRow
    s.setCursor { cursor with row := newRow, col := ⟨min cursor.col.val lineLen⟩ }
  else
    s

def EditorState.moveCursorDown (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  let buffer := s.getActiveBuffer
  if cursor.row.val < buffer.lineCount - 1 then
    let newRow : Row := ⟨cursor.row.val + 1⟩
    let lineLen := lineDisplayWidth tabStop buffer newRow
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
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  let len := lineDisplayWidth tabStop s.getActiveBuffer cursor.row
  let newCol : Col := ⟨min (col - 1) len⟩ -- 1-indexed to 0-indexed, clamped
  let s' := s.setCursor { cursor with col := newCol }
  { s' with inputState := { s'.inputState with countBuffer := "" } }

def EditorState.jumpToLine (s : EditorState) (line : Nat) : EditorState :=
  let tabStop := s.config.tabStop
  let buffer := s.getActiveBuffer
  let maxLine := buffer.lineCount
  let newRowVal := if line == 0 then 0 else min (line - 1) (maxLine - 1)
  let newRow : Row := ⟨newRowVal⟩
  let lineLen := lineDisplayWidth tabStop buffer newRow
  let cursor := s.getCursor
  let newCol : Col := ⟨min cursor.col.val lineLen⟩
  let s' := s.setCursor { cursor with row := newRow, col := newCol }
  { s' with inputState := { s'.inputState with countBuffer := "" } }


def EditorState.moveToLineStart (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  s.setCursor { cursor with col := 0 }

def EditorState.moveToLineEnd (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  let len := lineDisplayWidth tabStop s.getActiveBuffer cursor.row
  s.setCursor { cursor with col := ⟨len⟩ }

def EditorState.clampCursor (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  let len := lineDisplayWidth tabStop s.getActiveBuffer cursor.row
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

/-- Upper bound used to guarantee termination for word-movement scans. -/
def wordMoveFuel (buffer : FileBuffer) : Nat :=
  max 1 (buffer.table.length + FileBuffer.lineCount buffer + 1)

mutual
  def findNextForwardCore (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (started : Bool) (fuel : Nat) : Row × Col :=
    match fuel with
    | 0 => (row, col)
    | fuel + 1 =>
      let lineLen := lineDisplayWidth tabStop buffer row
      if lineLen == 0 then
         (row, 0) -- Stop at empty line
      else if col.val >= lineLen then
         -- End of line, wrap to next line
         if row.val + 1 < FileBuffer.lineCount buffer then
           let nextRow := row.succ
           let nextLen := lineDisplayWidth tabStop buffer nextRow
           if nextLen == 0 then
              (nextRow, 0) -- Stop at empty line
           else
              findNextForwardCore tabStop buffer nextRow 0 true fuel
         else
           (row, col) -- End of file
      else
        let lineStr := lineString buffer row
        let c := charAtDisplayCol tabStop lineStr col
        let isKw := isKeyword c
        let isSpace := c.isWhitespace
        if !started then
          if isSpace then
             findNextForwardCore tabStop buffer row (nextCol tabStop buffer row col) true fuel
          else
             findNextWordEndForwardCore tabStop buffer row (nextCol tabStop buffer row col) isKw fuel
        else
           if isSpace then
              findNextForwardCore tabStop buffer row (nextCol tabStop buffer row col) started fuel
           else
              (row, col) -- Found start of next word

  def findNextWordEndForwardCore (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (wasTv : Bool) (fuel : Nat) : Row × Col :=
    match fuel with
    | 0 => (row, col)
    | fuel + 1 =>
      let lineLen := lineDisplayWidth tabStop buffer row
      if col.val >= lineLen then
        if row.val + 1 < FileBuffer.lineCount buffer then
          findNextForwardCore tabStop buffer row.succ 0 true fuel
        else
          (row, col)
      else
        let lineStr := lineString buffer row
        let c := charAtDisplayCol tabStop lineStr col
        let isKw := isKeyword c
        let isSpace := c.isWhitespace
        if isSpace then
           findNextForwardCore tabStop buffer row (nextCol tabStop buffer row col) true fuel
        else if isKw != wasTv then
           (row, col)
        else
           findNextWordEndForwardCore tabStop buffer row (nextCol tabStop buffer row col) wasTv fuel
end

def findNextForward (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (started : Bool) : Row × Col :=
  findNextForwardCore tabStop buffer row col started (wordMoveFuel buffer)

def findNextWordEndForward (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (wasTv : Bool) : Row × Col :=
  findNextWordEndForwardCore tabStop buffer row col wasTv (wordMoveFuel buffer)

/-- Move forward to start of next word (w) -/
def EditorState.moveWordForward (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let currLineLen := lineDisplayWidth tabStop buffer cursor.row
  let (r, c) := if currLineLen == 0 then
                   if cursor.row.val + 1 < FileBuffer.lineCount buffer then
                      findNextForward tabStop buffer cursor.row.succ 0 true
                   else
                      (cursor.row, 0)
                else
                   let lineStr := lineString buffer cursor.row
                   if cursor.col.val < currLineLen then
                      let ch := charAtDisplayCol tabStop lineStr cursor.col
                      let isKw := isKeyword ch
                      let isSpace := ch.isWhitespace
                      if isSpace then
                         findNextForward tabStop buffer cursor.row (nextCol tabStop buffer cursor.row cursor.col) true
                      else
                         findNextWordEndForward tabStop buffer cursor.row (nextCol tabStop buffer cursor.row cursor.col) isKw
                   else
                      if cursor.row.val + 1 < FileBuffer.lineCount buffer then
                         findNextForward tabStop buffer cursor.row.succ 0 true
                      else
                         (cursor.row, ⟨currLineLen⟩)

  let finalLineLen := lineDisplayWidth tabStop buffer r
  let finalColVal := if r.val + 1 >= FileBuffer.lineCount buffer && c.val >= finalLineLen && finalLineLen > 0 && s.mode != Mode.insert then
                        finalLineLen - 1
                     else
                        min c.val finalLineLen
  s.setCursor { row := r, col := ⟨finalColVal⟩ }



mutual
  def findPrevStartCore (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (fuel : Nat) : Row × Col :=
    match fuel with
    | 0 => (row, col)
    | fuel + 1 =>
      let lineStr := lineString buffer row
      let c := charAtDisplayCol tabStop lineStr col
      if c.isWhitespace then
         if col.val == 0 then
            if row.val > 0 then
               let prevRow := row.pred
               let prevLen := lineDisplayWidth tabStop buffer prevRow
               if prevLen > 0 then findPrevStartCore tabStop buffer prevRow ⟨prevLen - 1⟩ fuel else (prevRow, 0)
            else (0, 0)
         else
            findPrevStartCore tabStop buffer row (prevCol tabStop buffer row col) fuel
      else
         let isKw := isKeyword c
         consumeWordBackwardCore tabStop buffer row col isKw fuel

  def consumeWordBackwardCore (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) (fuel : Nat) : Row × Col :=
    match fuel with
    | 0 => (row, col)
    | fuel + 1 =>
      let lineStr := lineString buffer row
      let c := charAtDisplayCol tabStop lineStr col
      let isKw := isKeyword c
      if c.isWhitespace || isKw != wantKw then
         (row, nextCol tabStop buffer row col)
      else
         if col.val == 0 then (row, 0)
         else consumeWordBackwardCore tabStop buffer row (prevCol tabStop buffer row col) wantKw fuel
end

def findPrevStart (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) : Row × Col :=
  findPrevStartCore tabStop buffer row col (wordMoveFuel buffer)

def consumeWordBackward (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) : Row × Col :=
  consumeWordBackwardCore tabStop buffer row col wantKw (wordMoveFuel buffer)

/-- Move backward to start of previous word (b) -/
def EditorState.moveWordBackward (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  if cursor.row.val == 0 && cursor.col.val == 0 then s
  else
      let lineLen := lineDisplayWidth tabStop buffer cursor.row
      let startCol : Col := if cursor.col.val >= lineLen then ⟨lineLen⟩ else cursor.col
      let (r, c) :=
         if startCol.val == 0 then
            if cursor.row.val > 0 then
               let prevRow := cursor.row.pred
               let prevLen := lineDisplayWidth tabStop buffer prevRow
               if prevLen > 0 then
                  findPrevStart tabStop buffer prevRow ⟨prevLen - 1⟩
               else
                  (prevRow, 0)
            else (0, 0)
         else
            findPrevStart tabStop buffer cursor.row (prevCol tabStop buffer cursor.row startCol)
      s.setCursor { row := r, col := c }


mutual
  def findNextEndCore (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (fuel : Nat) : Row × Col :=
    match fuel with
    | 0 => (row, col)
    | fuel + 1 =>
      let lineLen := lineDisplayWidth tabStop buffer row
      if col.val >= lineLen then
         if row.val + 1 < FileBuffer.lineCount buffer then
           findNextEndCore tabStop buffer row.succ 0 fuel
         else
           (row, col)
      else
         let lineStr := lineString buffer row
         let c := charAtDisplayCol tabStop lineStr col
         if c.isWhitespace then
            findNextEndCore tabStop buffer row (nextCol tabStop buffer row col) fuel
         else
            let isKw := isKeyword c
            consumeWordToEndCore tabStop buffer row col isKw fuel

  def consumeWordToEndCore (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) (fuel : Nat) : Row × Col :=
    match fuel with
    | 0 => (row, col)
    | fuel + 1 =>
      let lineLen := lineDisplayWidth tabStop buffer row
      let nextColVal := (nextCol tabStop buffer row col).val
      if nextColVal >= lineLen then
         (row, col)
      else
         let lineStr := lineString buffer row
         let nextC := charAtDisplayCol tabStop lineStr (nextCol tabStop buffer row col)
         let nextKw := isKeyword nextC
         if nextC.isWhitespace || nextKw != wantKw then
            (row, col)
         else
            consumeWordToEndCore tabStop buffer row (nextCol tabStop buffer row col) wantKw fuel
end

def findNextEnd (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) : Row × Col :=
  findNextEndCore tabStop buffer row col (wordMoveFuel buffer)

def consumeWordToEnd (tabStop : Nat) (buffer : FileBuffer) (row : Row) (col : Col) (wantKw : Bool) : Row × Col :=
  consumeWordToEndCore tabStop buffer row col wantKw (wordMoveFuel buffer)

/-- Move to end of word (e) -/
def EditorState.moveWordEnd (s : EditorState) : EditorState :=
  let tabStop := s.config.tabStop
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let currLineLen := lineDisplayWidth tabStop buffer cursor.row

  let startCol : Col := nextCol tabStop buffer cursor.row cursor.col
  let (r, c) :=
      if startCol.val >= currLineLen then
         if cursor.row.val + 1 < FileBuffer.lineCount buffer then
            findNextEnd tabStop buffer cursor.row.succ 0
         else
            (cursor.row, ⟨currLineLen⟩)
      else
         findNextEnd tabStop buffer cursor.row startCol

  s.setCursor { row := r, col := c }


end ViE
