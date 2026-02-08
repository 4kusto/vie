import ViE.Data.PieceTable
import Test.Utils

namespace Test.TreeStats

open ViE
open Test.Utils

def buildWorkload (iterations : Nat) : PieceTable := Id.run do
  let mut pt := PieceTable.fromString "Initial content\n"
  for i in [0:iterations] do
    pt := pt.insert pt.tree.length s!"line {i}\n" pt.tree.length
  return pt

mutual
  def countNodes (t : PieceTree) : Nat :=
    match t with
    | .empty => 0
    | .leaf _ _ _ => 1
    | .internal cs _ _ => 1 + countNodesList cs.toList

  def countNodesList (ts : List PieceTree) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => countNodes t + countNodesList rest
end

mutual
  def countLeaves (t : PieceTree) : Nat :=
    match t with
    | .empty => 0
    | .leaf _ _ _ => 1
    | .internal cs _ _ => countLeavesList cs.toList

  def countLeavesList (ts : List PieceTree) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => countLeaves t + countLeavesList rest
end

mutual
  def maxLeafPieces (t : PieceTree) : Nat :=
    match t with
    | .empty => 0
    | .leaf ps _ _ => ps.size
    | .internal cs _ _ => maxLeafPiecesList cs.toList

  def maxLeafPiecesList (ts : List PieceTree) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => max (maxLeafPieces t) (maxLeafPiecesList rest)
end

mutual
  def maxInternalChildren (t : PieceTree) : Nat :=
    match t with
    | .empty => 0
    | .leaf _ _ _ => 0
    | .internal cs _ _ =>
        max cs.size (maxInternalChildrenList cs.toList)

  def maxInternalChildrenList (ts : List PieceTree) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => max (maxInternalChildren t) (maxInternalChildrenList rest)
end

def parseIterations (args : List String) : Nat :=
  let args :=
    match args with
    | "--" :: rest => rest
    | _ => args
  match args with
  | a :: _ =>
      match a.toNat? with
      | some n => n
      | none => 5000
  | [] => 5000

def report (pt : PieceTable) (iterations : Nat) : IO Unit := do
  let tree := pt.tree
  let h := PieceTree.height tree
  let nodes := countNodes tree
  let leaves := countLeaves tree
  let maxLeaf := maxLeafPieces tree
  let maxChildren := maxInternalChildren tree
  IO.println s!"iterations={iterations}"
  IO.println s!"bytes={PieceTree.length tree} lines={PieceTree.lineBreaks tree} height={h}"
  IO.println s!"nodes={nodes} leaves={leaves} maxLeafPieces={maxLeaf} maxChildren={maxChildren}"

  match tree with
  | .empty => IO.println "root=empty"
  | .leaf ps _ _ => IO.println s!"root=leaf pieces={ps.size}"
  | .internal cs _ _ => IO.println s!"root=internal children={cs.size}"

  if iterations > 0 then
    let start := ← IO.monoMsNow
    let _ := pt.getLineRange (iterations - 1)
    let stop := ← IO.monoMsNow
    IO.println s!"getLineRange(last)={stop - start}ms"

def test : IO Unit := do
  IO.println "Starting TreeStats Test..."
  let iterations := 3000
  let pt := buildWorkload iterations
  let t := pt.tree
  let bytes := PieceTree.length t
  let textBytes := pt.toString.toUTF8.size
  let isNonEmpty :=
    match t with
    | .empty => false
    | _ => true

  assertEqual "tree length equals rendered bytes" textBytes bytes
  assert "tree is non-empty" isNonEmpty
  assert "tree height is at least 2 after workload" (PieceTree.height t >= 2)
  assert "leaf piece count stays within node capacity" (maxLeafPieces t <= NodeCapacity)
  assert "internal children stay within node capacity" (maxInternalChildren t <= NodeCapacity)
  assert "line range for last inserted line exists" ((pt.getLineRange (iterations - 1)).isSome)
  IO.println "TreeStats Test passed!"

def main (args : List String) : IO Unit := do
  let iterations := parseIterations args
  let pt := buildWorkload iterations
  report pt iterations

end Test.TreeStats
