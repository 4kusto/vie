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

def newlineCount (s : String) : Nat :=
  s.foldl (fun n c => if c == '\n' then n + 1 else n) 0

def expectedLineCountFromText (s : String) : Nat :=
  let breaks := newlineCount s
  breaks + 1

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

def testLengthAndLineCountConsistency : IO Unit := do
  IO.println "testLengthAndLineCountConsistency..."
  let mut pt := PieceTable.fromString ""
  for i in [0:1200] do
    let len := pt.length
    let pos := if len == 0 then 0 else (i * 17 + 3) % (len + 1)
    if i % 5 == 0 then
      let txt := if i % 2 == 0 then "\n" else s!"x{i}"
      pt := pt.insert pos txt pos
    else if i % 7 == 0 then
      let delLen := if len == 0 then 0 else min ((i % 4) + 1) (len - (pos % len))
      pt := pt.delete (if len == 0 then 0 else pos % len) delLen 0
    else
      let txt := if i % 3 == 0 then "a\n" else "b"
      pt := pt.insert pos txt pos

    let rendered := pt.toString
    let renderedBytes := rendered.toUTF8.size
    if renderedBytes != pt.length then
      throw <| IO.userError s!"Length mismatch at step {i}: tree={pt.length} rendered={renderedBytes}"

    let expectedLines := expectedLineCountFromText rendered
    if pt.lineCount != expectedLines then
      throw <| IO.userError s!"Line count mismatch at step {i}: tree={pt.lineCount} expected={expectedLines}"

    let h := PieceTree.height pt.tree
    if h > 64 then
      throw <| IO.userError s!"Tree height unexpectedly large at step {i}: height={h}"

  IO.println "[PASS] length/line count remain consistent under mixed edits"

def testYankPasteClearing : IO Unit := do
  IO.println "testYankPasteClearing (yy+p reproduction)..."
  -- Simulate: insert 25 'i' chars + newline, then yy+p 4000 times
  let initLine := String.ofList (List.replicate 25 'i') ++ "\n"
  let lineBytes := initLine.toUTF8.size  -- 26 bytes
  let mut pt := PieceTable.fromString initLine
  let mut cursorLine : Nat := 0

  for step in [0:4000] do
    -- 1. yy: read current line content via getLineRange + getBytes (like real editor)
    let range := PieceTree.getLineRange pt.tree cursorLine pt
    match range with
    | none =>
        throw <| IO.userError s!"[YankPaste] getLineRange returned none at step {step}, line {cursorLine}"
    | some (off, len) =>
        let yankedBytes := PieceTree.getBytes pt.tree off len pt
        if yankedBytes.size == 0 then
          throw <| IO.userError s!"[YankPaste] Empty yank at step {step}, line {cursorLine}, off={off} len={len}"

        -- 2. p: paste below current line.
        -- Insert after end of current line (off + len + 1 for newline)
        let insertOffset := off + len + 1
        let insertOffset := min insertOffset pt.length
        let yankStr := (String.fromUTF8! yankedBytes) ++ "\n"
        pt := pt.insert insertOffset yankStr insertOffset

        -- 3. Move cursor to pasted line
        cursorLine := cursorLine + 1

    -- 4. Verify tree length
    let expectedLen := lineBytes * (step + 2)
    let actualLen := pt.length
    if actualLen != expectedLen then
      throw <| IO.userError s!"[YankPaste] Length mismatch at step {step}: expected={expectedLen} actual={actualLen}"

    -- 5. Full consistency check every 500 steps
    if step % 500 == 0 then
      let rendered := pt.toString.toUTF8.size
      if rendered != expectedLen then
        throw <| IO.userError s!"[YankPaste] Rendered mismatch at step {step}: expected={expectedLen} rendered={rendered}"
      IO.println s!"  step {step}: length={actualLen} lines={PieceTree.lineBreaks pt.tree} height={PieceTree.height pt.tree} OK"

  IO.println "[PASS] yank+paste 4000 iterations with getLineRange consistent"

def test : IO Unit := do
  IO.println "Starting PieceTable Stress Test..."
  testConsistency
  testLengthAndLineCountConsistency
  testYankPasteClearing
  IO.println "PieceTable Stress Test passed!"

end Test.PieceTable.Stress
