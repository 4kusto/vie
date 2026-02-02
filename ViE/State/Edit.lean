import ViE.State.Config
import ViE.State.Layout
import ViE.State.Movement
import ViE.Types
import ViE.Buffer.Content
import ViE.Data.PieceTable

namespace ViE

def EditorState.setMode (s : EditorState) (m : Mode) : EditorState :=
  { s with mode := m }

def EditorState.insertChar (s : EditorState) (c : Char) : EditorState :=
  let cursor := s.getCursor
  -- Use direct PieceTable insert for atomic undo
  let s' := s.updateActiveBuffer fun buffer =>
    match buffer.table.getOffsetFromPoint cursor.row.val cursor.col.val with
    | some offset => { buffer with table := buffer.table.insert offset (c.toString) offset
                                   dirty := true }
    | none => buffer

  s'.setCursor { cursor with col := ⟨cursor.col.val + 1⟩ }

def EditorState.insertNewline (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  -- Use direct PieceTable insert for atomic undo
  let s' := s.updateActiveBuffer fun buffer =>
    match buffer.table.getOffsetFromPoint cursor.row.val cursor.col.val with
    | some offset => { buffer with table := buffer.table.insert offset "\n" offset
                                   dirty := true }
    | none => buffer

  s'.setCursor { row := ⟨cursor.row.val + 1⟩, col := 0 }

def EditorState.deleteBeforeCursor (s : EditorState) : EditorState :=
  let cursor := s.getCursor
  if cursor.col.val > 0 then
    -- Delete char before cursor
    let s' := s.updateActiveBuffer fun buffer =>
       match buffer.table.getOffsetFromPoint cursor.row.val (cursor.col.val - 1) with
       | some offset =>
            { buffer with table := buffer.table.delete offset 1 (offset + 1)
                          dirty := true }
       | none => buffer

    s'.setCursor { cursor with col := ⟨cursor.col.val - 1⟩ }
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
  let s' := s.updateActiveBuffer fun buffer =>
    match buffer.table.getOffsetFromPoint cursor.row.val cursor.col.val with
    | some offset =>
        -- Ensure we don't delete newline if at end of line (unless J behavior, but x usually doesn't join lines)
        match buffer.table.getLineRange cursor.row.val with
        | some (_, len) =>
           if cursor.col.val < len then
              { buffer with table := buffer.table.delete offset 1 offset
                            dirty := true }
           else
              buffer
        | none => buffer
     | none => buffer

  -- Cursor stays at same position unless it was last char
  let newBuffer := s'.getActiveBuffer
  let newLen := ViE.getLineLengthFromBuffer newBuffer cursor.row |>.getD 0
  if newLen > 0 && cursor.col.val >= newLen then
     s'.setCursor { cursor with col := ⟨newLen - 1⟩ }
  else
     s'





def EditorState.deleteCurrentLine (s : EditorState) : EditorState :=
  let cursor := s.getCursor
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
    message := "Deleted line"
  }


def EditorState.deleteRange (s : EditorState) (p1 p2 : Point) : EditorState :=
  let s' := s.updateActiveBuffer fun buffer =>
     match buffer.table.getOffsetFromPoint p1.row.val p1.col.val,
           buffer.table.getOffsetFromPoint p2.row.val p2.col.val with
     | some off1, some off2 =>
         let startOff := min off1 off2
         let endOff := max off1 off2
         let len := endOff - startOff
         if len > 0 then
            { buffer with table := buffer.table.delete startOff len startOff
                          dirty := true }
         else buffer
     | _, _ => buffer

  -- Move cursor to start of deleted range
  let newStart := if p1.row < p2.row || (p1.row == p2.row && p1.col < p2.col) then p1 else p2
  let s'' := s'.setCursor newStart
  { s'' with inputState := { s''.inputState with previousKey := none } }


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
  let lineLen := ViE.getLineLengthFromBuffer buffer endP.row |>.getD 0
  let targetCol := if endP.col.val + 1 <= lineLen then endP.col.val + 1 else lineLen
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
  { s with clipboard := (some content : Option String), message := "Yanked 1 line" }

def EditorState.pasteBelow (s : EditorState) : EditorState :=
  match s.clipboard with
  | none => { s with message := "Clipboard empty" }
  | some text =>
    let cursor := s.getCursor
    let s' := s.updateActiveBuffer fun buffer =>
      -- Determine insert offset.
      -- Try start of next line. If EOF, append.
      let (offset, textToInsert) := match buffer.table.getOffsetFromPoint (cursor.row.val + 1) 0 with
                    | some off => (off, text)
                    | none =>
                        let len := buffer.table.tree.length
                        if len > 0 then
                           -- Check if buffer ends with newline to avoid merging
                           -- (Optimization: ideally check last char directly)
                           if !PieceTable.endsWithNewline buffer.table then
                               (len, "\n" ++ text)
                           else
                               (len, text)
                        else (0, text)

      -- For paste, undo should restore cursor to insertion point
      let pt := buffer.table.commit
      { buffer with table := pt.insert offset textToInsert offset
                    dirty := true }

    s'.setCursor { row := ⟨cursor.row.val + 1⟩, col := 0 }

def EditorState.pasteAbove (s : EditorState) : EditorState :=
  match s.clipboard with
  | none => { s with message := "Clipboard empty" }
  | some text =>
    let cursor := s.getCursor
    let s' := s.updateActiveBuffer fun buffer =>
      let offset := match buffer.table.getOffsetFromPoint cursor.row.val 0 with
                     | some off => off
                     | none => 0
       let pt := buffer.table.commit
       let textStr : String := text
       { buffer with table := pt.insert offset textStr offset
                     dirty := true }
    s'.setCursor { cursor with col := 0 }

def EditorState.undo (s : EditorState) : EditorState :=
  -- Capture current cursor offset (if valid) for redo
  let buf := s.getActiveBuffer
  let cursor := s.getCursor
  let currentOffset := match buf.table.getOffsetFromPoint cursor.row.val cursor.col.val with
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
  let currentOffset := match buf.table.getOffsetFromPoint cursor.row.val cursor.col.val with
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
