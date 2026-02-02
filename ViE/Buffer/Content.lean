import Lean
import ViE.Types
import ViE.Basic
import ViE.Data.PieceTable

namespace ViE



/-- Get a line from FileBuffer (delegates to PieceTable) -/
def getLineFromBuffer (buffer : FileBuffer) (n : Row) : Option String :=
  buffer.table.getLine n.val

/-- Get line length from FileBuffer (delegates to PieceTable) -/
def getLineLengthFromBuffer (buffer : FileBuffer) (n : Row) : Option Nat :=
  buffer.table.getLineLength n.val

namespace Buffer

/-- Convert FileBuffer to TextBuffer (compatibility function) -/
def fileBufferToTextBuffer (buf : FileBuffer) : TextBuffer :=
  let lineCount := FileBuffer.lineCount buf
  if lineCount > 0 then
    -- Map each line index to its string content
    (List.range lineCount).toArray.map fun i =>
      match getLineFromBuffer buf ⟨i⟩ with
      | some str => stringToLine str
      | none => #[]
  else
    -- Empty buffer - return single empty line
    #[#[]]

/-- Create/Update FileBuffer from TextBuffer (flattening is expensive, avoided if possible) -/
def fileBufferFromTextBuffer (id : Nat) (filename : Option String) (content : TextBuffer) : FileBuffer :=
  let fullString := String.intercalate "\n" (content.toList.map lineToString)
  let table := PieceTable.fromString fullString
  {
    id := id
    filename := filename
    dirty := true -- Assume dirty if created from manual content
    table := table
    missingEol := false -- Default
    cache := { lineMap := Lean.RBMap.empty }
  }

/-- Update FileBuffer from TextBuffer (compatibility function) -/
def fileBufferUpdateFromTextBuffer (buf : FileBuffer) (newContent : TextBuffer) : FileBuffer :=
  let newBuf := fileBufferFromTextBuffer buf.id buf.filename newContent
  { newBuf with dirty := true }

end Buffer

/-- Modify a line in FileBuffer using PieceTable operations -/
def modifyLineInBuffer (buffer : FileBuffer) (row : Row) (f : String → String) : FileBuffer :=
  match buffer.table.getLineRange row.val with
  | some (startOffset, length) =>
     match buffer.table.getLine row.val with
     | some oldLine =>
        let newLine := f oldLine
        -- Edit: Delete old line content, insert new content.
        -- We preserve the newline character if it exists (getLineRange excludes it).
        let table' := buffer.table.delete startOffset length startOffset
        let table'' := table'.insert startOffset newLine startOffset
        { buffer with
          table := table''
          dirty := true
        }
     | none => buffer -- Should check range first, but safe fallback
  | none => buffer -- Line not found


end ViE
