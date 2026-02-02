import ViE.Data.PieceTable

namespace Test.PasteReproduction

def test : IO Unit := do
  IO.println "--- Test 1: Paste below last line (no trailing newline) ---"
  let pt := ViE.PieceTable.fromString "line 1"
  IO.println s!"Initial: [{pt.toString}]"

  -- Yank line 1 (manually simulating EditorState.yankCurrentLine)
  let line1 := pt.getLine 0 |>.getD ""
  let yanked := if line1.endsWith "\n" then line1 else line1 ++ "\n"
  IO.println s!"Yanked: [{yanked}]"

  -- Paste below line 0 (simulating EditorState.pasteBelow)
  let (off, text) := match pt.getOffsetFromPoint 1 0 with
    | some o => (o, yanked)
    | none =>
        let len := pt.length
        if len > 0 then
           if !pt.endsWithNewline then (len, "\n" ++ yanked) else (len, yanked)
        else (0, yanked)

  let pt2 := pt.insert off text off
  IO.println s!"After paste:\n[{pt2.toString}]"
  IO.println s!"Line count: {pt2.lineCount}"
  for i in [:pt2.lineCount] do
    IO.println s!"Line {i}: [{pt2.getLine i |>.getD "NONE"}]"

  IO.println "\n--- Test 2: Paste below last line (with trailing newline) ---"
  let ptB := ViE.PieceTable.fromString "line 1\n"
  IO.println s!"Initial: [{ptB.toString}]"
  let line1B := ptB.getLine 0 |>.getD ""
  let yankedB := if line1B.endsWith "\n" then line1B else line1B ++ "\n"
  let (offB, textB) := match ptB.getOffsetFromPoint 1 0 with
    | some o => (o, yankedB)
    | none =>
        let len := ptB.length
        if len > 0 then
           if !ptB.endsWithNewline then (len, "\n" ++ yankedB) else (len, yankedB)
        else (0, yankedB)
  let ptB2 := ptB.insert offB textB offB
  IO.println s!"After paste:\n[{ptB2.toString}]"
  IO.println s!"Line count: {ptB2.lineCount}"
  for i in [:ptB2.lineCount] do
    IO.println s!"Line {i}: [{ptB2.getLine i |>.getD "NONE"}]"
