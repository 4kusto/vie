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

/-- Get byte offset from Row/Col (display column) with configurable tab stop. -/
def getOffsetFromPointInBufferWithTabStop (buffer : FileBuffer) (row : Row) (col : Col) (tabStop : Nat) : Option Nat :=
  match buffer.table.getLineRange row.val with
  | some (startOff, len) =>
      let line := getLineFromBuffer buffer row |>.getD ""
      let byteOff := ViE.Unicode.displayColToByteOffsetWithTabStop line tabStop col.val
      let clamped := if byteOff <= len then byteOff else len
      some (startOff + clamped)
  | none => none

/-- Get line length from FileBuffer with configurable tab stop. -/
def getLineLengthFromBufferWithTabStop (buffer : FileBuffer) (n : Row) (tabStop : Nat) : Option Nat :=
  match getLineFromBuffer buffer n with
  | some line => some (ViE.Unicode.stringWidthWithTabStop line tabStop)
  | none => none

/-- Convert byte offset to Row/Col (display column) with configurable tab stop. -/
def getPointFromOffsetInBufferWithTabStop (buffer : FileBuffer) (offset tabStop : Nat) : Point :=
  let (rowNat, _) := buffer.table.getPointFromOffset offset
  match buffer.table.getLineRange rowNat with
  | some (startOff, len) =>
      let rel := if offset >= startOff then min (offset - startOff) len else 0
      let sub := ViE.PieceTree.getSubstring buffer.table.tree startOff rel buffer.table
      let col := ViE.Unicode.stringWidthWithTabStop sub tabStop
      Point.fromNat rowNat col
  | none =>
      Point.fromNat rowNat 0

/-- Get byte offset from Row/Col (display column) using default tab stop. -/
def getOffsetFromPointInBuffer (buffer : FileBuffer) (row : Row) (col : Col) : Option Nat :=
  getOffsetFromPointInBufferWithTabStop buffer row col 4

/-- Get line length from FileBuffer (delegates to PieceTable) using default tab stop. -/
def getLineLengthFromBuffer (buffer : FileBuffer) (n : Row) : Option Nat :=
  getLineLengthFromBufferWithTabStop buffer n 4

/-- Convert byte offset to Row/Col (display column) using default tab stop. -/
def getPointFromOffsetInBuffer (buffer : FileBuffer) (offset : Nat) : Point :=
  getPointFromOffsetInBufferWithTabStop buffer offset 4

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
