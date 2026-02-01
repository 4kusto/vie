import ViE.Types
import ViE.Basic
import ViE.Data.PieceTable

namespace ViE

open ViE.PieceTable

/-- Get a line from FileBuffer (delegates to PieceTable) -/
def getLineFromBuffer (buffer : FileBuffer) (n : Nat) : Option String :=
  buffer.table.getLine n

/-- Get line length from FileBuffer (delegates to PieceTable) -/
def getLineLengthFromBuffer (buffer : FileBuffer) (n : Nat) : Option Nat :=
  buffer.table.getLineLength n

namespace Buffer

/-- Convert FileBuffer to TextBuffer (compatibility function) -/
def fileBufferToTextBuffer (buf : FileBuffer) : TextBuffer :=
  let lineCount := FileBuffer.lineCount buf
  if lineCount > 0 then
    -- Map each line index to its string content
    (List.range lineCount).toArray.map fun i =>
      match getLineFromBuffer buf i with
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
  }

/-- Update FileBuffer from TextBuffer (compatibility function) -/
def fileBufferUpdateFromTextBuffer (buf : FileBuffer) (newContent : TextBuffer) : FileBuffer :=
  let newBuf := fileBufferFromTextBuffer buf.id buf.filename newContent
  { newBuf with dirty := true }

end Buffer

/-- Modify a line in FileBuffer using PieceTable operations -/
def modifyLineInBuffer (buffer : FileBuffer) (row : Nat) (f : String → String) : FileBuffer :=
  match buffer.table.getLineRange row with
  | some (startOffset, length) =>
     match buffer.table.getLine row with
     | some oldLine =>
        let newLine := f oldLine
        -- Edit: Delete old line content, insert new content.
        -- We preserve the newline character if it exists (getLineRange excludes it).
        let table' := buffer.table.delete startOffset length
        let table'' := table'.insert startOffset newLine
        { buffer with
          table := table''
          dirty := true
        }
     | none => buffer -- Should check range first, but safe fallback
  | none => buffer -- Line not found

end ViE
