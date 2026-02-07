import ViE.State.Config
import ViE.State.Layout
import ViE.Data.PieceTable
import Test.Utils

open ViE

namespace Test.MissingEol

open Test.Utils

def testMissingEol : IO Unit := do
  IO.println "testMissingEol..."
  let s := ViE.initialState
  let s := s.updateActiveBuffer fun buffer =>
    { buffer with table := PieceTable.fromString "abc\n", dirty := true }
  let buf := s.getActiveBuffer
  assert "missingEol false with trailing newline" (!buf.missingEol)

  let len := buf.table.length
  let s := s.updateActiveBuffer fun buffer =>
    { buffer with table := buffer.table.delete (len - 1) 1 (len - 1), dirty := true }
  let buf2 := s.getActiveBuffer
  assert "missingEol true after deleting newline" buf2.missingEol

  let s := ViE.initialState
  let s := s.updateActiveBuffer fun buffer =>
    { buffer with table := PieceTable.fromString "abc", dirty := true }
  let buf3 := s.getActiveBuffer
  assert "missingEol true without newline" buf3.missingEol

  let len2 := buf3.table.length
  let s := s.updateActiveBuffer fun buffer =>
    { buffer with table := buffer.table.insert len2 "\n" len2, dirty := true }
  let buf4 := s.getActiveBuffer
  assert "missingEol false after adding newline" (!buf4.missingEol)


def test : IO Unit := do
  IO.println "Starting MissingEol Test..."
  testMissingEol
  IO.println "MissingEol Test passed!"

end Test.MissingEol
