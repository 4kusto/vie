import ViE.Data.PieceTable
import Test.Utils

open ViE

namespace Test.PieceTable.Stress

open Test.Utils

/-- Naive string manipulation for verification -/
def naiveInsert (s : String) (idx : Nat) (content : String) : String :=
  let lst := s.toList
  let pre := lst.take idx
  let post := lst.drop idx
  String.ofList (pre ++ content.toList ++ post)

def naiveDelete (s : String) (idx : Nat) (len : Nat) : String :=
  let lst := s.toList
  let pre := lst.take idx
  let post := lst.drop (idx + len)
  String.ofList (pre ++ post)

def testConsistency : IO Unit := do
  IO.println "testConsistency (Small Stress)..."
  let mut pt := PieceTable.fromString ""
  let mut mirror := ""

  -- 1. Insert Hello
  pt := pt.insert 0 "Hello" 0
  mirror := naiveInsert mirror 0 "Hello"
  assertEqual "Step 1" mirror pt.toString

  -- 2. Insert World
  pt := pt.insert 5 " World" 5
  mirror := naiveInsert mirror 5 " World"
  assertEqual "Step 2" mirror pt.toString

  -- 3. Delete space at 5
  -- "Hello World" -> "HelloWorld"
  pt := pt.delete 5 1 5
  mirror := naiveDelete mirror 5 1
  assertEqual "Step 3" mirror pt.toString

  -- 4. Insert comma at 5
  -- "HelloWorld" -> "Hello,World"
  pt := pt.insert 5 "," 5
  mirror := naiveInsert mirror 5 ","
  assertEqual "Step 4" mirror pt.toString

def test : IO Unit := do
  IO.println "Starting PieceTable Stress Test..."
  testConsistency
  IO.println "PieceTable Stress Test passed!"

end Test.PieceTable.Stress
