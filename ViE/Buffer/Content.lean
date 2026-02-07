import Lean
import ViE.Types
import ViE.Basic
import ViE.Data.PieceTable
import ViE.Unicode

namespace ViE



/-- Get a line from FileBuffer (delegates to PieceTable) -/
def getLineFromBuffer (buffer : FileBuffer) (n : Row) : Option String :=
  match buffer.cache.findRaw n with
  | some s => some s
  | none => buffer.table.getLine n.val

/-- Get byte offset from Row/Col (display column) using per-line index cache if available. -/
def getOffsetFromPointInBuffer (buffer : FileBuffer) (row col : Nat) : Option Nat :=
  match buffer.table.getLineRange row with
  | some (startOff, len) =>
      let line := getLineFromBuffer buffer ⟨row⟩ |>.getD ""
      let byteOff := match buffer.cache.findIndex ⟨row⟩ with
        | some idx => ViE.Unicode.displayColToByteOffsetFromIndex idx col
        | none => ViE.Unicode.displayColToByteOffset line col
      let clamped := if byteOff <= len then byteOff else len
      some (startOff + clamped)
  | none => none

/-- Get line length from FileBuffer (delegates to PieceTable) -/
def getLineLengthFromBuffer (buffer : FileBuffer) (n : Row) : Option Nat :=
  match getLineFromBuffer buffer n with
  | some line => some (ViE.Unicode.stringWidth line)
  | none => none

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
    cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
  }

/-- Create/Update FileBuffer from TextBuffer with bloom config. -/
def fileBufferFromTextBufferWithConfig (id : Nat) (filename : Option String) (content : TextBuffer) (buildLeafBits : Bool) : FileBuffer :=
  let fullString := String.intercalate "\n" (content.toList.map lineToString)
  let table := PieceTable.fromString fullString buildLeafBits
  {
    id := id
    filename := filename
    dirty := true -- Assume dirty if created from manual content
    table := table
    missingEol := false -- Default
    cache := { lineMap := Lean.RBMap.empty, rawLineMap := Lean.RBMap.empty, lineIndexMap := Lean.RBMap.empty }
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
     match getLineFromBuffer buffer row with
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
