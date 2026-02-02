import ViE.Data.PieceTable
import Test.Utils

open ViE

namespace Test.PieceTable.UndoRedo

open Test.Utils

def testUndoRedo : IO Unit := do
  IO.println "testUndoRedo..."
  let pt := PieceTable.fromString ""
  -- Insert "A" at 0
  let pt1 := pt.insert 0 "A" 0
  -- Insert "B" at 0 (Prepend) -> "BA"
  let pt2 := pt1.insert 0 "B" 0
  assertEqual "Initial state" "BA" pt2.toString

  -- Undo B (restores to "A")
  let (pt3, _) := pt2.undo 0
  assertEqual "After Undo 1" "A" pt3.toString

  -- Undo A
  let (pt4, _) := pt3.undo 0
  assertEqual "After Undo 2" "" pt4.toString

  -- Redo A
  let (pt5, _) := pt4.redo 0
  assertEqual "After Redo 1" "A" pt5.toString

  -- Redo B
  let (pt6, _) := pt5.redo 0
  assertEqual "After Redo 2" "BA" pt6.toString

def testComplexUndo : IO Unit := do
  IO.println "testComplexUndo..."
  let pt := PieceTable.fromString "Base"
  let pt1 := pt.insert 4 "1" 4 -- Base1
  let pt1 := pt1.commit -- Prevent merge
  let pt2 := pt1.insert 5 "2" 5 -- Base12
  let pt3 := pt2.delete 5 1 5 -- Base1
  let pt4 := pt3.insert 5 "3" 5 -- Base13

  assertEqual "State before undo" "Base13" pt4.toString

  -- Undo insert "3" -> Base1
  let (u1, _) := pt4.undo 0
  assertEqual "Undo 3" "Base1" u1.toString

  -- Undo delete "2" -> Base12
  let (u2, _) := u1.undo 0
  assertEqual "Undo delete 2" "Base12" u2.toString

  -- Undo insert "2" -> Base1
  let (u3, _) := u2.undo 0
  assertEqual "Undo insert 2" "Base1" u3.toString

  -- Undo insert "1" -> Base
  let (u4, _) := u3.undo 0
  assertEqual "Undo insert 1" "Base" u4.toString


def test : IO Unit := do
  IO.println "Starting PieceTable Undo/Redo Test..."
  testUndoRedo
  testComplexUndo
  IO.println "PieceTable Undo/Redo Test passed!"

end Test.PieceTable.UndoRedo
