import ViE.Buffer.Content
import ViE.Types
import ViE.Data.PieceTable

open ViE


namespace Test.Buffer

def assert (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    throw (IO.userError s!"Assertion failed: {msg}")

def test : IO Unit := do
  IO.println "Starting Buffer Test..."

  -- 1. Test fromString and getLine
  let text := "Hello\nWorld"
  let pt := PieceTable.fromString text
  let buf : FileBuffer := { initialFileBuffer with table := pt }

  -- Check lines
  match getLineFromBuffer buf 0 with
  | some l => assert "Line 0 is Hello" (l == "Hello")
  | none => assert "Line 0 missing" false

  match getLineFromBuffer buf 1 with
  | some l => assert "Line 1 is World" (l == "World")
  | none => assert "Line 1 missing" false

  match getLineFromBuffer buf 2 with
  | some _ => assert "Line 2 should be missing" false
  | none => assert "Line 2 correctly missing" true

  -- 2. Test FileBuffer <-> TextBuffer conversion
  let tb : TextBuffer := #[ #['A', 'B'], #['C'] ] -- "AB\nC"
  let buf2 := ViE.Buffer.fileBufferFromTextBuffer 1 (some "test.txt") tb

  assert "Buffer created from TextBuffer id" (buf2.id == 1)
  assert "Buffer created from TextBuffer filename" (buf2.filename == some "test.txt")

  let tb2 := ViE.Buffer.fileBufferToTextBuffer buf2
  assert "Roundtrip TextBuffer size" (tb2.size == 2)
  if tb2.size == 2 then
    let l0 := tb2[0]!
    let l1 := tb2[1]!
    assert "Roundtrip Line 0" (String.ofList l0.toList == "AB")
    assert "Roundtrip Line 1" (String.ofList l1.toList == "C")

  IO.println "BufferTest passed!"

end Test.Buffer
