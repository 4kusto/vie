import ViE.State.Config
import ViE.State.Layout
import ViE.State.Movement
import ViE.Types
import ViE.Buffer.Content
import ViE.Data.PieceTable
import ViE.Unicode

namespace ViE

def EditorState.setMode (s : EditorState) (m : Mode) : EditorState :=
  { s with mode := m }

def EditorState.insertChar (s : EditorState) (c : Char) : EditorState :=
  let cursor := s.getCursor
  -- Use direct PieceTable insert for atomic undo
  let s' := s.updateActiveBuffer fun buffer =>
    match ViE.getOffsetFromPointInBuffer buffer cursor.row.val cursor.col.val with
    | some offset => { buffer with table := buffer.table.insert offset (c.toString) offset
                                   dirty := true }
    | none => buffer

  let delta := ViE.Unicode.charWidth c
  s'.setCursor { cursor with col := ⟨cursor.col.val + delta⟩ }

def EditorState.insertNewline (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  -- Use direct PieceTable insert for atomic undo
  let s' := s.updateActiveBuffer fun buffer =>
    match ViE.getOffsetFromPointInBuffer buffer cursor.row.val cursor.col.val with
    | some offset => { buffer with table := buffer.table.insert offset "\n" offset
                                   dirty := true }
    | none => buffer

  s'.setCursor { row := ⟨cursor.row.val + 1⟩, col := 0 }

def EditorState.deleteBeforeCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  if cursor.col.val > 0 then
    -- Delete char before cursor
    let buffer := s.getActiveBuffer
    let prevC := prevCol buffer cursor.row cursor.col
    let s' := s.updateActiveBuffer fun buffer =>
       match ViE.getOffsetFromPointInBuffer buffer cursor.row.val prevC.val,
             ViE.getOffsetFromPointInBuffer buffer cursor.row.val cursor.col.val with
       | some startOff, some endOff =>
            let len := endOff - startOff
            if len > 0 then
              { buffer with table := buffer.table.delete startOff len endOff
                            dirty := true }
            else buffer
       | _, _ => buffer

    s'.setCursor { cursor with col := prevC }
  else if cursor.row.val > 0 then
    -- Join with previous line (delete previous newline)
    let prevRow : Row := ⟨cursor.row.val - 1⟩

    let s' := s.updateActiveBuffer fun buffer =>
       -- Verify we are deleting the newline at the end of prevRow.
       match buffer.table.getLineRange prevRow.val with
       | some (start, len) =>
          -- Newline is at start + len. Length of newline is 1 (for \n).
          { buffer with table := buffer.table.delete (start + len) 1 (start + len)
                        dirty := true }
       | none => buffer

    -- Cursor moves to end of previous line
    let newLen := ViE.getLineLengthFromBuffer s'.getActiveBuffer prevRow |>.getD 0
    s'.setCursor { row := prevRow, col := ⟨newLen⟩ }
  else
    s

def EditorState.deleteCharAfterCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  -- Check if valid char at cursor
  let buffer := s.getActiveBuffer
  let lineLen := lineDisplayWidth buffer cursor.row
  let nextC := nextCol buffer cursor.row cursor.col
  let deletedText :=
    match ViE.getOffsetFromPointInBuffer buffer cursor.row.val cursor.col.val,
          ViE.getOffsetFromPointInBuffer buffer cursor.row.val nextC.val with
    | some startOff, some endOff =>
        if cursor.col.val < lineLen && endOff > startOff then
          PieceTree.getSubstring buffer.table.tree startOff (endOff - startOff) buffer.table
        else
          ""
    | _, _ => ""
  let s' := s.updateActiveBuffer fun buffer =>
    match ViE.getOffsetFromPointInBuffer buffer cursor.row.val cursor.col.val,
          ViE.getOffsetFromPointInBuffer buffer cursor.row.val nextC.val with
    | some startOff, some endOff =>
        -- Ensure we don't delete newline if at end of line (unless J behavior, but x usually doesn't join lines)
        if cursor.col.val < lineLen && endOff > startOff then
          { buffer with table := buffer.table.delete startOff (endOff - startOff) startOff
                        dirty := true }
        else
          buffer
    | _, _ => buffer

  -- Cursor stays at same position unless it was last char
  let s'' :=
    if deletedText.isEmpty then
      s'
    else
      let reg : Register := {
        kind := .charwise
        text := deletedText
        blockLines := []
        blockWidth := 0
      }
      { s' with clipboard := some reg }
  let newBuffer := s''.getActiveBuffer
  let newLen := lineDisplayWidth newBuffer cursor.row
  if newLen > 0 && cursor.col.val >= newLen then
     let lineStr := lineString newBuffer cursor.row
     let newCol := ViE.Unicode.prevDisplayCol lineStr newLen
     s''.setCursor { cursor with col := ⟨newCol⟩ }
  else
     s''





def EditorState.deleteCurrentLine (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let line := ViE.getLineFromBuffer s.getActiveBuffer cursor.row |>.getD ""
  let content := if line.endsWith "\n" then line else line ++ "\n"
  let reg : Register := {
    kind := .linewise
    text := content
    blockLines := []
    blockWidth := 0
  }
  let s' := s.updateActiveBuffer fun buffer =>
    match buffer.table.getLineRange cursor.row.val with
    | some (start, len) =>
       let deleteLen := if cursor.row.val < FileBuffer.lineCount buffer - 1 then len + 1 else len
       -- Restore cursor at start of line
       { buffer with table := buffer.table.delete start deleteLen start
                     dirty := true }
    | none => buffer

  -- Reset cursor logic
  let newBuffer := s'.getActiveBuffer
  let newRowVal := min cursor.row.val (newBuffer.lineCount.pred)
  let newRow : Row := ⟨newRowVal⟩
  let currentLineLen := ViE.getLineLengthFromBuffer newBuffer newRow |>.getD 0
  let newCol := min cursor.col.val currentLineLen
  let s'' := s'.setCursor { row := newRow, col := ⟨newCol⟩ }
  { s'' with
    inputState := { s''.inputState with previousKey := none },
    clipboard := some reg,
    message := "Deleted line"
  }


def EditorState.deleteRange (s : EditorState) (p1 p2 : Point) : EditorState :=
  let buffer := s.getActiveBuffer
  let (startOffOpt, endOffOpt) :=
    match ViE.getOffsetFromPointInBuffer buffer p1.row.val p1.col.val,
          ViE.getOffsetFromPointInBuffer buffer p2.row.val p2.col.val with
    | some off1, some off2 => (some (min off1 off2), some (max off1 off2))
    | _, _ => (none, none)
  let deletedText :=
    match (startOffOpt, endOffOpt) with
    | (some startOff, some endOff) =>
        if endOff > startOff then
          PieceTree.getSubstring buffer.table.tree startOff (endOff - startOff) buffer.table
        else
          ""
    | _ => ""
  let s' := s.updateActiveBuffer fun buffer =>
     match (startOffOpt, endOffOpt) with
     | (some startOff, some endOff) =>
         let len := endOff - startOff
         if len > 0 then
            { buffer with table := buffer.table.delete startOff len startOff
                          dirty := true }
         else buffer
     | _ => buffer

  -- Move cursor to start of deleted range
  let newStart := if p1.row < p2.row || (p1.row == p2.row && p1.col < p2.col) then p1 else p2
  let s'' := s'.setCursor newStart
  let s''' :=
    if deletedText.isEmpty then
      s''
    else
      let reg : Register := {
        kind := .charwise
        text := deletedText
        blockLines := []
        blockWidth := 0
      }
      { s'' with clipboard := some reg }
  { s''' with inputState := { s'''.inputState with previousKey := none } }


def EditorState.changeWord (s : EditorState) : EditorState :=
  let n := if s.getCount == 0 then 1 else s.getCount
  let start := s.getCursor

  -- Apply 'moveWordEnd' n times (recursive helper)
  let rec applyMotionN (st : EditorState) (count : Nat) : EditorState :=
    match count with
    | 0 => st
    | k + 1 => applyMotionN (st.moveWordEnd) k

  let endState := applyMotionN s n
  let endP := endState.getCursor

  -- Inclusive deletion logic for 'e' motion behavior
  let buffer := s.getActiveBuffer
  let lineLen := lineDisplayWidth buffer endP.row
  let lineStr := lineString buffer endP.row
  let targetCol := if endP.col.val < lineLen then ViE.Unicode.nextDisplayCol lineStr endP.col.val else lineLen
  let targetP := { endP with col := ⟨targetCol⟩ }

  (s.deleteRange start targetP).setMode Mode.insert

def EditorState.insertLineBelow (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let s' := s.updateActiveBuffer fun buffer =>
    match buffer.table.getLineRange cursor.row.val with
    | some (start, len) =>
       { buffer with table := buffer.table.insert (start + len) "\n" (start + len)
                     dirty := true }
    | none => buffer
  s'.setCursor { row := ⟨cursor.row.val + 1⟩, col := 0 }

def EditorState.insertLineAbove (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let s' := s.updateActiveBuffer fun buffer =>
    match buffer.table.getLineRange cursor.row.val with
    | some (start, _) =>
       { buffer with table := buffer.table.insert start "\n" start
                     dirty := true }
    | none => buffer
  s'.setCursor { cursor with col := 0 }

def EditorState.yankCurrentLine (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  let line := ViE.getLineFromBuffer s.getActiveBuffer cursor.row |>.getD ""
  let content := if line.endsWith "\n" then line else line ++ "\n"
  let reg : Register := {
    kind := .linewise
    text := content
    blockLines := []
    blockWidth := 0
  }
  { s with clipboard := some reg, message := "Yanked 1 line" }

def EditorState.ensureLineCount (s : EditorState) (count : Nat) : EditorState :=
  s.updateActiveBuffer fun buffer =>
    let lineCount := buffer.table.lineCount
    if count <= lineCount then
      buffer
    else
      let missing := count - lineCount
      let newlines := String.ofList (List.replicate missing '\n')
      let len := buffer.table.tree.length
      { buffer with table := buffer.table.insert len newlines len, dirty := true }

def EditorState.pasteCharwise (s : EditorState) (text : String) (after : Bool) : EditorState :=
  let cursor := s.getCursor
  let line := ViE.getLineFromBuffer s.getActiveBuffer cursor.row |>.getD ""
  let lineWidth := ViE.Unicode.stringWidth line
  let targetCol :=
    if after then
      if cursor.col.val < lineWidth then
        ViE.Unicode.nextDisplayCol line cursor.col.val
      else
        cursor.col.val
    else
      cursor.col.val
  let s' := s.updateActiveBuffer fun buffer =>
    match ViE.getOffsetFromPointInBuffer buffer cursor.row.val targetCol with
    | some offset => { buffer with table := buffer.table.insert offset text offset, dirty := true }
    | none => buffer
  let lines := text.splitOn "\n"
  let lastLine := lines.getLastD ""
  let lastWidth := ViE.Unicode.stringWidth lastLine
  let rowDelta := if lines.length > 0 then lines.length - 1 else 0
  let newRow := cursor.row.val + rowDelta
  let newCol :=
    if lines.length <= 1 then
      if lastWidth == 0 then targetCol else targetCol + lastWidth - 1
    else
      if lastWidth == 0 then 0 else lastWidth - 1
  s'.setCursor { row := ⟨newRow⟩, col := ⟨newCol⟩ }

def firstNonBlankCol (line : String) : Nat :=
  let rec loop (cs : List Char) (col : Nat) : Nat :=
    match cs with
    | [] => 0
    | c :: rest =>
      if c == ' ' || c == '\t' then
        loop rest (col + ViE.Unicode.charWidth c)
      else
        col
  loop line.toList 0

def EditorState.pasteLinewise (s : EditorState) (text : String) (below : Bool) : EditorState :=
  let cursor := s.getCursor
  let row := if below then cursor.row.val + 1 else cursor.row.val
  let s' := s.updateActiveBuffer fun buffer =>
    -- Determine insert offset.
    -- Try start of target line. If EOF, append.
    let (offset, textToInsert) := match ViE.getOffsetFromPointInBuffer buffer row 0 with
                  | some off => (off, text)
                  | none =>
                      let len := buffer.table.tree.length
                      if len > 0 then
                         if !PieceTable.endsWithNewline buffer.table then
                             (len, "\n" ++ text)
                         else
                             (len, text)
                      else (0, text)
    let pt := buffer.table.commit
    { buffer with table := pt.insert offset textToInsert offset, dirty := true }
  let newRow := if below then cursor.row.val + 1 else cursor.row.val
  let lineStr := ViE.getLineFromBuffer s'.getActiveBuffer ⟨newRow⟩ |>.getD ""
  let col := firstNonBlankCol lineStr
  s'.setCursor { row := ⟨newRow⟩, col := ⟨col⟩ }

def EditorState.pasteBlockwise (s : EditorState) (reg : Register) (after : Bool) : EditorState :=
  let cursor := s.getCursor
  let line := ViE.getLineFromBuffer s.getActiveBuffer cursor.row |>.getD ""
  let lineWidth := ViE.Unicode.stringWidth line
  let baseCol :=
    if after then
      if cursor.col.val < lineWidth then
        ViE.Unicode.nextDisplayCol line cursor.col.val
      else
        cursor.col.val
    else
      cursor.col.val
  let lines :=
    if reg.blockLines.isEmpty then
      if reg.text.isEmpty then [] else reg.text.splitOn "\n"
    else
      reg.blockLines
  let targetLineCount := cursor.row.val + lines.length
  let s1 := s.ensureLineCount targetLineCount
  let s2 := s1.updateActiveBuffer fun buffer =>
    let rec apply (buf : FileBuffer) (idx : Nat) (ls : List String) : FileBuffer :=
      match ls with
      | [] => buf
      | l :: rest =>
        let row := cursor.row.val + idx
        let lineStr := ViE.getLineFromBuffer buf ⟨row⟩ |>.getD ""
        let lineW := ViE.Unicode.stringWidth lineStr
        let targetCol := baseCol
        let (buf1, offset) :=
          if targetCol > lineW then
            let pad := targetCol - lineW
            let padStr := String.ofList (List.replicate pad ' ')
            let insertOff := ViE.getOffsetFromPointInBuffer buf row lineW |>.getD (buf.table.tree.length)
            let buf' := { buf with table := buf.table.insert insertOff padStr insertOff, dirty := true }
            let off' := ViE.getOffsetFromPointInBuffer buf' row targetCol |>.getD insertOff
            (buf', off')
          else
            let off := ViE.getOffsetFromPointInBuffer buf row targetCol |>.getD 0
            (buf, off)
        let buf2 := { buf1 with table := buf1.table.insert offset l offset, dirty := true }
        apply buf2 (idx + 1) rest
    apply buffer 0 lines
  s2.setCursor { row := cursor.row, col := ⟨baseCol⟩ }

def EditorState.pasteBelow (s : EditorState) : EditorState :=
  match s.clipboard with
  | none => { s with message := "Clipboard empty" }
  | some reg =>
    match reg.kind with
    | .linewise => s.pasteLinewise reg.text true
    | .charwise => s.pasteCharwise reg.text true
    | .blockwise => s.pasteBlockwise reg true

def EditorState.pasteAbove (s : EditorState) : EditorState :=
  match s.clipboard with
  | none => { s with message := "Clipboard empty" }
  | some reg =>
    match reg.kind with
    | .linewise => s.pasteLinewise reg.text false
    | .charwise => s.pasteCharwise reg.text false
    | .blockwise => s.pasteBlockwise reg false

def EditorState.undo (s : EditorState) : EditorState :=
  -- Capture current cursor offset (if valid) for redo
  let buf := s.getActiveBuffer
  let cursor := s.getCursor
  let currentOffset := match ViE.getOffsetFromPointInBuffer buf cursor.row.val cursor.col.val with
                       | some off => off
                       | none => 0

  let (newTable, cursorOpt) := buf.table.undo currentOffset
  let s' := s.updateActiveBuffer fun _ => { buf with table := newTable, dirty := true }

  match cursorOpt with
  | some off =>
      let (r, c) := newTable.getPointFromOffset off
      let s'' := s'.setCursor { row := ⟨r⟩, col := ⟨c⟩ }
      { s'' with message := "Undo" }
  | none => { s' with message := "Already at oldest change" }

def EditorState.redo (s : EditorState) : EditorState :=
  -- Capture current cursor offset
  let buf := s.getActiveBuffer
  let cursor := s.getCursor
  let currentOffset := match ViE.getOffsetFromPointInBuffer buf cursor.row.val cursor.col.val with
                       | some off => off
                       | none => 0

  let (newTable, cursorOpt) := buf.table.redo currentOffset
  let s' := s.updateActiveBuffer fun _ => { buf with table := newTable, dirty := true }

  match cursorOpt with
  | some off =>
      let (r, c) := newTable.getPointFromOffset off
      let s'' := s'.setCursor { row := ⟨r⟩, col := ⟨c⟩ }
      { s'' with message := "Redo" }
  | none => { s' with message := "Already at newest change" }

def EditorState.commitEdit (s : EditorState) : EditorState :=
  s.updateActiveBuffer fun buffer =>
    { buffer with table := buffer.table.commit }


/-- Vim Operators -/

def EditorState.deleteWord (s : EditorState) : EditorState :=
  let p1 := s.getCursor
  let s' := s.moveWordForward
  let p2 := s'.getCursor
  s.deleteRange p1 p2


end ViE
