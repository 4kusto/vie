import ViE.Data.PieceTable
import Test.Utils

open ViE

namespace Test.PieceTable.Search

open Test.Utils

def makeBoundaryTable : PieceTable :=
  let n := ViE.NodeCapacity + 1
  let startIdx := n / 2 - 1
  let chars := Id.run do
    let mut cs := Array.replicate n 'x'
    cs := cs.set! startIdx 'a'
    cs := cs.set! (startIdx + 1) 'b'
    cs := cs.set! (startIdx + 2) 'c'
    return cs
  let s := String.ofList chars.toList
  let bytes := s.toUTF8
  let pieces := (Array.range n).map fun i =>
    { source := BufferSource.original
      start := i
      length := 1
      lineBreaks := 0
      charCount := 1 }
  let tmp : PieceTable := {
    original := bytes
    addBuffers := #[]
    tree := PieceTree.empty
    undoStack := []
    redoStack := []
    undoStackCount := 0
    redoStackCount := 0
    undoLimit := 100
    lastInsert := none
  }
  let tree := PieceTree.fromPieces pieces tmp
  { tmp with tree := tree }


def testCrossLeafSearch : IO Unit := do
  IO.println "testCrossLeafSearch..."
  let pt := makeBoundaryTable
  let n := ViE.NodeCapacity + 1
  let startIdx := n / 2 - 1
  let pattern := "abc".toUTF8
  let (r1, _, _) := PieceTree.searchNext pt.tree pt pattern 0 64 true (Lean.RBMap.empty) #[] 16
  assertEqual "searchNext bloom across leaf" (some startIdx) r1
  let total := pt.tree.length
  let (r2, _, _) := PieceTree.searchPrev pt.tree pt pattern total 64 true (Lean.RBMap.empty) #[] 16
  assertEqual "searchPrev bloom across leaf" (some startIdx) r2

def testCrossLeafSearchNearBoundary : IO Unit := do
  IO.println "testCrossLeafSearchNearBoundary..."
  let pt := makeBoundaryTable
  let n := ViE.NodeCapacity + 1
  let startIdx := n / 2 - 1
  let pattern := "abc".toUTF8
  let startOffset := startIdx - 1
  let (r1, _, _) := PieceTree.searchNext pt.tree pt pattern startOffset 64 true (Lean.RBMap.empty) #[] 16
  assertEqual "searchNext from near boundary" (some startIdx) r1
  let startExclusive := startIdx + pattern.size
  let (r2, _, _) := PieceTree.searchPrev pt.tree pt pattern startExclusive 64 true (Lean.RBMap.empty) #[] 16
  assertEqual "searchPrev to near boundary" (some startIdx) r2


def test : IO Unit := do
  IO.println "Starting PieceTable Search Test..."
  testCrossLeafSearch
  testCrossLeafSearchNearBoundary
  IO.println "PieceTable Search Test passed!"

end Test.PieceTable.Search
