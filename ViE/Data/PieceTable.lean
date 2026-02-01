import ViE.Data.PieceTable.Piece
import ViE.Data.PieceTable.Types
import ViE.Data.PieceTable.Tree

namespace ViE.PieceTable

/-- Chunk size for splitting large files (16KB) -/
def PieceTable.ChunkSize : Nat := 1024 * 16

/-- Construct from bytes -/
def PieceTable.fromByteArray (bytes : ByteArray) : PieceTable :=
  if bytes.size == 0 then
    { original := bytes, add := ByteArray.empty, tree := PieceTree.empty }
  else
    -- Split bytes into chunks to avoid monolithic pieces
    let totalSize := bytes.size
    let rec splitChunks (start : Nat) (acc : Array Piece) : Array Piece :=
      if start >= totalSize then acc
      else
        let len := min PieceTable.ChunkSize (totalSize - start)
        let lines := ViE.Unicode.countNewlines bytes start len
        let chars := ViE.Unicode.countChars bytes start len
        let piece := { source := .original, start := start, length := len, lineBreaks := lines, charCount := chars }
        splitChunks (start + len) (acc.push piece)
    termination_by totalSize - start
    decreasing_by
      simp_wf
      rw [Nat.sub_add_eq]
      have h : start < totalSize := Nat.lt_of_not_le (by assumption)
      apply Nat.sub_lt_self
      · have h1 : 0 < totalSize - start := Nat.sub_pos_of_lt h
        apply Nat.lt_min.mpr
        constructor
        . show 0 < PieceTable.ChunkSize
          unfold PieceTable.ChunkSize
          exact Nat.zero_lt_succ _
        · assumption
      · apply Nat.min_le_right

    let pieces := splitChunks 0 #[]
    let tree := PieceTree.fromPieces pieces
    { original := bytes, add := ByteArray.empty, tree := tree }

/-- Construct from initial string -/
def PieceTable.fromString (s : String) : PieceTable :=
  PieceTable.fromByteArray s.toUTF8

/-- Convert tree to string -/
def PieceTable.toString (pt : PieceTable) : String :=
  PieceTree.getSubstring pt.tree 0 pt.tree.length pt

/-- Insert text at offset -/
def PieceTable.insert (pt : PieceTable) (offset : Nat) (text : String) : PieceTable :=
  if text.isEmpty then pt
  else
    let (pt', newPiece) := PieceTableHelper.appendText pt text
    let (l, r) := PieceTree.split pt.tree offset pt'
    let mid := PieceTree.mkLeaf #[newPiece]
    let newTree := PieceTree.concat (PieceTree.concat l mid) r
    { pt' with tree := newTree }

/-- Delete range [offset, offset + length) -/
def PieceTable.delete (pt : PieceTable) (offset : Nat) (length : Nat) : PieceTable :=
  if length == 0 then pt
  else
    let newTree := PieceTree.delete pt.tree offset length pt
    { pt with tree := newTree }

/-- Get line from buffer -/
def PieceTable.getLine (pt : PieceTable) (lineIdx : Nat) : Option String :=
  PieceTree.getLine pt.tree lineIdx pt

/-- Get line range from buffer -/
def PieceTable.getLineRange (pt : PieceTable) (lineIdx : Nat) : Option (Nat × Nat) :=
  PieceTree.getLineRange pt.tree lineIdx pt

/-- Get line char length from buffer -/
def PieceTable.getLineLength (pt : PieceTable) (lineIdx : Nat) : Option Nat :=
  PieceTree.getLineLength pt.tree lineIdx pt

end ViE.PieceTable
