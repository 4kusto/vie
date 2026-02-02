import ViE.Data.PieceTable

open ViE

namespace Test.Undo

def assert (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    throw (IO.userError s!"Assertion failed: {msg}")

def test : IO Unit := do
  IO.println "Starting Undo/Redo Test..."

  -- 1. Create initial buffer
  let initialText := "Hello, World!"
  let pt0 := PieceTable.fromString initialText
  assert "Initial text correct" (pt0.toString == initialText)
  assert "Initial undo stack empty" (pt0.undoStack.isEmpty)

  -- 2. Insert " New" at end
  -- "Hello, World! New"
  let pt1 := pt0.insert 13 " New" 13
  assert "Text after insert" (pt1.toString == "Hello, World! New")
  assert "Undo stack has 1 item" (pt1.undoStack.length == 1)

  -- 3. Delete ", World"
  -- "Hello! New"
  -- "Hello, World!" -> offset 5, delete 7 (", World")
  let pt2 := pt1.delete 5 7 5
  assert "Text after delete" (pt2.toString == "Hello! New")
  assert "Undo stack has 2 items" (pt2.undoStack.length == 2)

  -- 4. Undo Modify (Delete)
  -- Should revert to "Hello, World! New"
  let (pt3, _) := pt2.undo 0
  assert "Text after undo delete" (pt3.toString == "Hello, World! New")
  assert "Undo stack has 1 item" (pt3.undoStack.length == 1)
  assert "Redo stack has 1 item" (pt3.redoStack.length == 1)

  -- 5. Undo Insert
  -- Should revert to "Hello, World!"
  let (pt4, _) := pt3.undo 0
  assert "Text after undo insert" (pt4.toString == "Hello, World!")
  assert "Undo stack has 0 items" (pt4.undoStack.isEmpty)
  assert "Redo stack has 2 items" (pt4.redoStack.length == 2)

  -- 6. Redo Insert
  -- Should go to "Hello, World! New"
  let (pt5, _) := pt4.redo 0
  assert "Text after redo insert" (pt5.toString == "Hello, World! New")
  assert "Undo stack has 1 item" (pt5.undoStack.length == 1)
  assert "Redo stack has 1 item" (pt5.redoStack.length == 1)

  -- 7. Redo Delete
  -- Should go to "Hello! New"
  let (pt6, _) := pt5.redo 0
  assert "Text after redo delete" (pt6.toString == "Hello! New")
  assert "Undo stack has 2 items" (pt6.undoStack.length == 2)
  assert "Redo stack empty" (pt6.redoStack.isEmpty)

  -- 8. Test Redo clearing on new edit
  let (pt7, _) := pt6.undo 0 -- "Hello, World! New"
  -- Insert " Again" at end -> "Hello, World! New Again"
  let pt8 := pt7.insert 17 " Again" 17
  assert "Text after new insert" (pt8.toString == "Hello, World! New Again")
  assert "Redo stack cleared" (pt8.redoStack.isEmpty)

  -- 9. Test Optimization (Grouping)
  -- Force break merge chain from previous step to ensure " 1" starts a new group
  let pt8_clean := { pt8 with lastInsert := none }
  let pt9 := pt8_clean.insert 23 " 1" 23 -- "Hello, World! New Again 1"
  let pt10 := pt9.insert 25 "2" 25 -- "Hello, World! New Again 12"
  let pt11 := pt10.insert 26 "3" 26 -- "Hello, World! New Again 123"

  assert "Text after group insert" (pt11.toString == "Hello, World! New Again 123")
  -- Should have only 1 new undo item for " 123" because they overlap
  -- pt8 had some undo stack. pt9 added 1. pt10 merged. pt11 merged.
  -- So pt11.undoStack.length should be pt8.undoStack.length + 1
  assert "Undo stack grouped" (pt11.undoStack.length == pt8.undoStack.length + 1)

  let (pt12, _) := pt11.undo 0
  assert "Undo removes group" (pt12.toString == "Hello, World! New Again")

  -- 10. Test Limit
  -- Force a small limit
  let ptLimit := { pt12 with undoLimit := 2 }
  let ptL1 := (ptLimit.insert 0 "A" 0) -- Stack: 1
  let ptL2 := (ptL1.insert 0 "B" 0) -- Stack: 2

  -- Previous insert was "A" at 0. LastInsert = (0 + 1, addOffset + 1).
  -- Current insert at 0. 0 != 1. So NOT contiguous. Correct.
  let ptL3 := (ptL2.insert 0 "C" 0) -- Stack: 3 -> capped to 2

  assert "Undo limit respected" (ptL3.undoStack.length == 2)
  -- The oldest undo (for "A") should be dropped. The remaining undos are "C" -> "B", and "B" -> "A".
  -- So undoing twice should start with "CBA..." -> "BA..." -> "A..."
  let (u1, _) := ptL3.undo 0
  let (u2, _) := u1.undo 0
  assert "Oldest undo dropped" (u2.toString == "AHello, World! New Again")

  assert "Oldest undo dropped" (u2.toString == "AHello, World! New Again")

  -- 11. Test Paste Undo Grouping (Reproduction)
  -- Scenario: Paste "P1" then Paste "P2". They should NOT merge if we signal a break,
  -- OR if we consider pastes as distinct operations that shouldn't auto-merge like typing.
  -- Currently PieceTable merges ANY contiguous insert.
  let ptBase := PieceTable.fromString ""
  let ptP1 := ptBase.insert 0 "P1" 0 -- Simulate Paste 1
  -- Simulate EditorState.paste calling commit before next insert
  let ptP1_committed := ptP1.commit
  let ptP2 := ptP1_committed.insert 2 "P2" 2 -- Simulate Paste 2 (contiguous)

  assert "Text is P1P2" (ptP2.toString == "P1P2")
  -- Expectation: 2 undo items (one for P1, one for P2).
  -- Bug: they merge into 1 item because offset 2 == lastInsert end.
  if ptP2.undoStack.length == 1 then
     IO.println "[FAIL] Paste operations merged (expected 2 undo items)"
     assert "Paste should not merge" false
  else
     IO.println "[PASS] Paste operations distinct (2 undo items)"

  IO.println "TestUndo passed!"

end Test.Undo
