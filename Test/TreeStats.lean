import ViE.Data.PieceTable

def main : IO Unit := do
  let iterations := 50000
  let mut pt := ViE.PieceTable.fromString "Initial content\n"

  IO.println s!"Performing {iterations} insertions..."
  for i in [0:iterations] do
    pt := pt.insert pt.tree.length s!"line {i}\n" pt.tree.length
    if i % 1000 == 0 then
      IO.println s!"Iteration {i}..."

  let tree := pt.tree
  match tree with
  | .empty => IO.println "Tree is empty"
  | .leaf ps _ => IO.println s!"Tree is a single leaf with {ps.size} pieces"
  | .internal cs s =>
    IO.println s!"Tree is internal with {cs.size} children at root"
    IO.println s!"Tree height: {s.height}"

    -- Check if children are also flat
    let mut maxChildSize := 0
    for c in cs do
      match c with
      | .internal cs2 _ => maxChildSize := max maxChildSize cs2.size
      | .leaf ps _ => maxChildSize := max maxChildSize ps.size
      | .empty => continue
    IO.println s!"Max child size at level 1: {maxChildSize}"

  if iterations > 0 then
    let start := ← IO.monoMsNow
    let _ := pt.getLineRange (iterations - 1)
    let endT := ← IO.monoMsNow
    IO.println s!"Time to getLineRange for last line: {endT - start}ms"
