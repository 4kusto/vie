import ViE.Types

namespace ViE

/-- Convert String to Line (Array Char) -/
def stringToLine (s : String) : Line :=
  s.toList.toArray

/-- Convert Line (Array Char) to String -/
def lineToString (line : Line) : String :=
  String.ofList line.toList

/-- Empty buffer with one empty line -/
def emptyTextBuffer : TextBuffer :=
  #[#[]]

/-- Helper to safely get a line as String. -/
def getLine (buffer : TextBuffer) (n : Nat) : Option String :=
  if h : n < buffer.size then
    some (lineToString buffer[n])
  else
    none

/-- Helper to update a specific line in the buffer. -/
def modifyLine (buffer : TextBuffer) (row : Nat) (f : String → String) : TextBuffer :=
  if h : row < buffer.size then
    let oldLine := buffer[row]
    let newLine := stringToLine (f (lineToString oldLine))
    buffer.set! row newLine
  else
    buffer

/-- Set a line directly (String version for compatibility) -/
def setLine (buffer : TextBuffer) (row : Nat) (content : String) : TextBuffer :=
  buffer.set! row (stringToLine content)

/-- Take first n elements from Array -/
def arrayTake {α : Type _} (arr : Array α) (n : Nat) : Array α :=
  arr.extract 0 n

/-- Drop first n elements from Array -/
def arrayDrop {α : Type _} (arr : Array α) (n : Nat) : Array α :=
  arr.extract n arr.size

/-- Concatenate multiple arrays -/
def arrayConcat {α : Type _} (arrays : List (Array α)) : Array α :=
  arrays.foldl (· ++ ·) #[]

end ViE
