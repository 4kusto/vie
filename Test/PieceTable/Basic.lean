import ViE.Data.PieceTable
import Test.Utils

open ViE

namespace Test.PieceTable.Basic

open Test.Utils

def testInsert : IO Unit := do
  IO.println "testInsert..."
  let pt := PieceTable.fromString "Hello"
  -- Insert at end
  let pt1 := pt.insert 5 " World" 5
  assertEqual "Insert at end" "Hello World" pt1.toString

  -- Insert at middle
  let pt2 := pt1.insert 5 "," 5
  assertEqual "Insert at middle" "Hello, World" pt2.toString

  -- Insert at start
  let pt3 := pt2.insert 0 "Say: " 0
  assertEqual "Insert at start" "Say: Hello, World" pt3.toString

def testDelete : IO Unit := do
  IO.println "testDelete..."
  let pt := PieceTable.fromString "Hello, World!"

  -- Delete "World" (offset 7, len 5)
  let pt1 := pt.delete 7 5 7
  assertEqual "Delete middle" "Hello, !" pt1.toString

  -- Delete start
  let pt2 := pt1.delete 0 7 0
  assertEqual "Delete start" "!" pt2.toString

  -- Delete end
  let pt3 := pt2.delete 0 1 0
  assertEqual "Delete end" "" pt3.toString

def test : IO Unit := do
  IO.println "Starting PieceTable Basic Test..."
  testInsert
  testDelete
  IO.println "PieceTable Basic Test passed!"

end Test.PieceTable.Basic
