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

def EditorState.jumpToColumn (s : EditorState) (col : Col) : EditorState :=
  let tabStop := s.config.tabStop
  let cursor := s.getCursor
  let len := lineDisplayWidth tabStop s.getActiveBuffer cursor.row
  let newCol : Col := ⟨min (col.val - 1) len⟩ -- 1-indexed to 0-indexed, clamped
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

def jumpListLimit : Nat := 256

def visibleContentRows (s : EditorState) : Nat :=
  let (h, _) := s.getActiveWindowScrollBounds
  if h > 1 then h - 1 else 1

def maxScrollableTop (buffer : FileBuffer) (rowsInView : Nat) : Nat :=
  if buffer.lineCount > rowsInView then buffer.lineCount - rowsInView else 0

def clampPointToActiveBuffer (s : EditorState) (p : Point) : Point :=
  let buffer := s.getActiveBuffer
  if buffer.lineCount == 0 then
    Point.zero
  else
    let rowVal := min p.row.val (buffer.lineCount - 1)
    let tabStop := s.config.tabStop
    let lineLen := lineDisplayWidth tabStop buffer ⟨rowVal⟩
    let colVal := min p.col.val lineLen
    { row := ⟨rowVal⟩, col := ⟨colVal⟩ }

def EditorState.pushJumpPoint (s : EditorState) : EditorState :=
  let p := s.getCursor
  match s.jumpBack with
  | head :: _ =>
      if head == p then
        s
      else
        { s with jumpBack := (p :: s.jumpBack).take jumpListLimit, jumpForward := [] }
  | [] =>
      { s with jumpBack := [p], jumpForward := [] }

def EditorState.jumpBackInList (s : EditorState) : EditorState :=
  match s.jumpBack with
  | [] => { s with message := "Jump list empty" }
  | p :: rest =>
      let current := s.getCursor
      let target := clampPointToActiveBuffer s p
      let s' := s.setCursor target
      { s' with
        jumpBack := rest
        jumpForward := (current :: s.jumpForward).take jumpListLimit
      }

def EditorState.jumpForwardInList (s : EditorState) : EditorState :=
  match s.jumpForward with
  | [] => { s with message := "Jump list empty" }
  | p :: rest =>
      let current := s.getCursor
      let target := clampPointToActiveBuffer s p
      let s' := s.setCursor target
      { s' with
        jumpForward := rest
        jumpBack := (current :: s.jumpBack).take jumpListLimit
      }

def EditorState.scrollDownRows (s : EditorState) (rows : Nat) : EditorState :=
  let buffer := s.getActiveBuffer
  if buffer.lineCount == 0 then
    s
  else
    let tabStop := s.config.tabStop
    let (sRow, sCol) := s.getScroll
    let cursor := s.getCursor
    let rowsInView := visibleContentRows s
    let maxTop := maxScrollableTop buffer rowsInView
    let newTop := min (sRow.val + rows) maxTop
    let visRow := if cursor.row.val >= sRow.val then cursor.row.val - sRow.val else 0
    let newRowVal := min (newTop + visRow) (buffer.lineCount - 1)
    let newLen := lineDisplayWidth tabStop buffer ⟨newRowVal⟩
    let newColVal := min cursor.col.val newLen
    (s.setScroll ⟨newTop⟩ sCol).setCursor { row := ⟨newRowVal⟩, col := ⟨newColVal⟩ }

def EditorState.scrollUpRows (s : EditorState) (rows : Nat) : EditorState :=
  let buffer := s.getActiveBuffer
  if buffer.lineCount == 0 then
    s
  else
    let tabStop := s.config.tabStop
    let (sRow, sCol) := s.getScroll
    let cursor := s.getCursor
    let newTop := if rows > sRow.val then 0 else sRow.val - rows
    let visRow := if cursor.row.val >= sRow.val then cursor.row.val - sRow.val else 0
    let newRowVal := min (newTop + visRow) (buffer.lineCount - 1)
    let newLen := lineDisplayWidth tabStop buffer ⟨newRowVal⟩
    let newColVal := min cursor.col.val newLen
    (s.setScroll ⟨newTop⟩ sCol).setCursor { row := ⟨newRowVal⟩, col := ⟨newColVal⟩ }

def halfPageRows (s : EditorState) : Nat :=
  max 1 ((visibleContentRows s) / 2)

def fullPageRows (s : EditorState) : Nat :=
  max 1 (visibleContentRows s)

def EditorState.scrollHalfPageDown (s : EditorState) (count : Nat := 0) : EditorState :=
  let rows := if count == 0 then halfPageRows s else count
  s.scrollDownRows rows

def EditorState.scrollHalfPageUp (s : EditorState) (count : Nat := 0) : EditorState :=
  let rows := if count == 0 then halfPageRows s else count
  s.scrollUpRows rows

def EditorState.scrollPageDown (s : EditorState) (count : Nat := 0) : EditorState :=
  let rows := if count == 0 then fullPageRows s else count
  s.scrollDownRows rows

def EditorState.scrollPageUp (s : EditorState) (count : Nat := 0) : EditorState :=
  let rows := if count == 0 then fullPageRows s else count
  s.scrollUpRows rows

def EditorState.scrollWindowDown (s : EditorState) (count : Nat := 1) : EditorState :=
  let rows := if count == 0 then 1 else count
  s.scrollDownRows rows

def EditorState.scrollWindowUp (s : EditorState) (count : Nat := 1) : EditorState :=
  let rows := if count == 0 then 1 else count
  s.scrollUpRows rows

def firstNonBlankColWithTabStop (line : String) (tabStop : Nat) : Nat :=
  let rec loop (cs : List Char) (col : Nat) : Nat :=
    match cs with
    | [] => 0
    | c :: rest =>
      if c == ' ' || c == '\t' then
        loop rest (col + ViE.Unicode.charWidthAt tabStop col c)
      else
        col
  loop line.toList 0

def EditorState.moveToScreenTop (s : EditorState) (count : Nat := 0) : EditorState :=
  let buffer := s.getActiveBuffer
  if buffer.lineCount == 0 then
    s
  else
    let n := if count == 0 then 1 else count
    let rowsInView := visibleContentRows s
    let offset := min (n - 1) (rowsInView - 1)
    let (sRow, _) := s.getScroll
    let rowVal := min (sRow.val + offset) (buffer.lineCount - 1)
    let tabStop := s.config.tabStop
    let lineStr := lineString buffer ⟨rowVal⟩
    let colVal := firstNonBlankColWithTabStop lineStr tabStop
    s.setCursor { row := ⟨rowVal⟩, col := ⟨colVal⟩ }

def EditorState.moveToScreenMiddle (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  if buffer.lineCount == 0 then
    s
  else
    let rowsInView := visibleContentRows s
    let offset := rowsInView / 2
    let (sRow, _) := s.getScroll
    let rowVal := min (sRow.val + offset) (buffer.lineCount - 1)
    let tabStop := s.config.tabStop
    let lineStr := lineString buffer ⟨rowVal⟩
    let colVal := firstNonBlankColWithTabStop lineStr tabStop
    s.setCursor { row := ⟨rowVal⟩, col := ⟨colVal⟩ }

def EditorState.moveToScreenBottom (s : EditorState) (count : Nat := 0) : EditorState :=
  let buffer := s.getActiveBuffer
  if buffer.lineCount == 0 then
    s
  else
    let n := if count == 0 then 1 else count
    let rowsInView := visibleContentRows s
    let fromBottom := min (n - 1) (rowsInView - 1)
    let offset := (rowsInView - 1) - fromBottom
    let (sRow, _) := s.getScroll
    let rowVal := min (sRow.val + offset) (buffer.lineCount - 1)
    let tabStop := s.config.tabStop
    let lineStr := lineString buffer ⟨rowVal⟩
    let colVal := firstNonBlankColWithTabStop lineStr tabStop
    s.setCursor { row := ⟨rowVal⟩, col := ⟨colVal⟩ }

private def findCharForwardOnLineCore
    (tabStop : Nat) (lineStr : String) (lineLen : Nat) (col : Nat) (target : Char) (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if col >= lineLen then
        none
      else
        let c := charAtDisplayCol tabStop lineStr ⟨col⟩
        if c == target then
          some col
        else
          let next := ViE.Unicode.nextDisplayColWithTabStop lineStr tabStop col
          if next <= col then none else findCharForwardOnLineCore tabStop lineStr lineLen next target fuel

private def findCharBackwardOnLineCore
    (tabStop : Nat) (lineStr : String) (col : Nat) (target : Char) (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let c := charAtDisplayCol tabStop lineStr ⟨col⟩
      if c == target then
        some col
      else if col == 0 then
        none
      else
        let prev := ViE.Unicode.prevDisplayColWithTabStop lineStr tabStop col
        if prev >= col then none else findCharBackwardOnLineCore tabStop lineStr prev target fuel

def EditorState.findCharMotion (s : EditorState) (target : Char) (forward : Bool) (till : Bool)
    (count : Nat := 1) (updateLast : Bool := true) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let tabStop := s.config.tabStop
  let lineStr := lineString buffer cursor.row
  let lineLen := lineDisplayWidth tabStop buffer cursor.row
  if lineLen == 0 then
    s
  else
    let n := if count == 0 then 1 else count
    let rec findNth (fromCol : Nat) (remaining : Nat) (fuel : Nat) : Option Nat :=
      match remaining with
      | 0 => some fromCol
      | rem + 1 =>
          if fuel == 0 then
            none
          else
            let found :=
              if forward then
                let start := ViE.Unicode.nextDisplayColWithTabStop lineStr tabStop fromCol
                if start >= lineLen then none
                else findCharForwardOnLineCore tabStop lineStr lineLen start target (lineLen + 1)
              else
                if fromCol == 0 then none
                else
                  let start := ViE.Unicode.prevDisplayColWithTabStop lineStr tabStop fromCol
                  if start >= lineLen then none
                  else findCharBackwardOnLineCore tabStop lineStr start target (lineLen + 1)
            match found with
            | none => none
            | some hit =>
                if rem == 0 then
                  some hit
                else
                  findNth hit rem fuel.pred
      termination_by remaining + fuel
    match findNth cursor.col.val n (lineLen + n + 1) with
    | none => { s with message := s!"Pattern not found: {target}" }
    | some hit =>
        let hitCol :=
          if till then
            if forward then
              ViE.Unicode.prevDisplayColWithTabStop lineStr tabStop hit
            else
              ViE.Unicode.nextDisplayColWithTabStop lineStr tabStop hit
          else
            hit
        let hitCol := min hitCol lineLen
        let s' := s.setCursor { cursor with col := ⟨hitCol⟩ }
        if updateLast then
          {
            s' with
              inputState := {
                s'.inputState with
                  lastFindChar := some target
                  lastFindForward := forward
                  lastFindTill := till
              }
          }
        else
          s'

def EditorState.repeatFindChar (s : EditorState) (reverse : Bool := false) : EditorState :=
  match s.inputState.lastFindChar with
  | none => { s with message := "No previous find command" }
  | some target =>
      let baseForward := s.inputState.lastFindForward
      let forward := if reverse then !baseForward else baseForward
      let count :=
        if s.inputState.lastFindTill && !reverse then 2 else 1
      s.findCharMotion target forward s.inputState.lastFindTill count false

def EditorState.wordUnderCursor (s : EditorState) : Option String :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let tabStop := s.config.tabStop
  let lineStr := lineString buffer cursor.row
  let lineLen := lineDisplayWidth tabStop buffer cursor.row
  let isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'
  if lineLen == 0 || cursor.col.val >= lineLen then
    none
  else
    let curChar := charAtDisplayCol tabStop lineStr cursor.col
    if !isWordChar curChar then
      none
    else
      let rec expandLeft (col : Col) (fuel : Nat) : Col :=
        match fuel with
        | 0 => col
        | fuel + 1 =>
            if col.val == 0 then
              col
            else
              let prev := prevCol tabStop buffer cursor.row col
              let c := charAtDisplayCol tabStop lineStr prev
              if isWordChar c then expandLeft prev fuel else col
      let rec expandRightExclusive (col : Col) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => col.val
        | fuel + 1 =>
            let next := nextCol tabStop buffer cursor.row col
            if next.val >= lineLen then
              lineLen
            else
              let c := charAtDisplayCol tabStop lineStr next
              if isWordChar c then
                expandRightExclusive next fuel
              else
                next.val
      let start := expandLeft cursor.col (lineLen + 1)
      let endExclusive := expandRightExclusive cursor.col (lineLen + 1)
      if endExclusive <= start.val then
        none
      else
        let sub := ViE.Unicode.dropByDisplayWidthWithTabStop lineStr.toRawSubstring tabStop start.val
        some (ViE.Unicode.takeByDisplayWidthWithTabStop sub tabStop (endExclusive - start.val))

def EditorState.jumpMatchingBracket (s : EditorState) : EditorState :=
  let buffer := s.getActiveBuffer
  let cursor := s.getCursor
  let tabStop := s.config.tabStop
  let lineLen := lineDisplayWidth tabStop buffer cursor.row
  if lineLen == 0 || cursor.col.val >= lineLen then
    { s with message := "No bracket under cursor" }
  else
    let here := charAtDisplayCol tabStop (lineString buffer cursor.row) cursor.col
    let info : Option (UInt8 × UInt8 × Bool) :=
      match here with
      | '(' => some (UInt8.ofNat 40, UInt8.ofNat 41, true)
      | '[' => some (UInt8.ofNat 91, UInt8.ofNat 93, true)
      | '{' => some (UInt8.ofNat 123, UInt8.ofNat 125, true)
      | ')' => some (UInt8.ofNat 40, UInt8.ofNat 41, false)
      | ']' => some (UInt8.ofNat 91, UInt8.ofNat 93, false)
      | '}' => some (UInt8.ofNat 123, UInt8.ofNat 125, false)
      | _ => none
    match info with
    | none => { s with message := "No bracket under cursor" }
    | some (openB, closeB, forward) =>
        let off := ViE.getOffsetFromPointInBufferWithTabStop buffer cursor.row cursor.col tabStop |>.getD 0
        let bytes := buffer.table.toString.toUTF8
        if off >= bytes.size then
          { s with message := "No bracket match" }
        else
          let rec scanForward (i : Nat) (depth : Nat) (fuel : Nat) : Option Nat :=
            match fuel with
            | 0 => none
            | fuel + 1 =>
                if i >= bytes.size then
                  none
                else
                  let b := bytes[i]!
                  let depth :=
                    if b == openB then depth + 1
                    else if b == closeB then depth - 1
                    else depth
                  if depth == 0 then some i else scanForward (i + 1) depth fuel
            termination_by fuel
          let rec scanBackward (i : Nat) (depth : Nat) (fuel : Nat) : Option Nat :=
            match fuel with
            | 0 => none
            | fuel + 1 =>
                if i == 0 then
                  none
                else
                  let j := i - 1
                  let b := bytes[j]!
                  let depth :=
                    if b == closeB then depth + 1
                    else if b == openB then depth - 1
                    else depth
                  if depth == 0 then some j else scanBackward j depth fuel
            termination_by fuel
          let hit :=
            if forward then
              scanForward (off + 1) 1 (bytes.size + 1)
            else
              scanBackward off 1 (bytes.size + 1)
          match hit with
          | none => { s with message := "No bracket match" }
          | some j =>
              let p := ViE.getPointFromOffsetInBufferWithTabStop buffer j tabStop
              s.setCursor p


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
