import ViE.Data.PieceTable
import ViETest.Utils

open ViE

namespace ViETest.PieceTable.Appended

open ViETest.Utils

def testAppends : IO Unit := do
  IO.println "testAppends..."
  let pt := PieceTable.fromString "Line1\n"

  -- Append Line 2
  let pt1 := pt.insert pt.length "Line2\n" pt.length
  assertEqual "Append 1" "Line1\nLine2\n" pt1.toString

  -- Append Line 3
  let pt2 := pt1.insert pt1.length "Line3" pt1.length
  assertEqual "Append 2" "Line1\nLine2\nLine3" pt2.toString

def test : IO Unit := do
  IO.println "Starting PieceTable Appended ViETest..."
  testAppends
  IO.println "PieceTable Appended Test passed!"

end ViETest.PieceTable.Appended
