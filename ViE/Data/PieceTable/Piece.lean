namespace ViE

/-- Source of a piece: either the original file (read-only) or the add buffer (append-only) -/
inductive BufferSource where
  | original
  | add (idx : Nat)
  deriving Repr, BEq, Inhabited

/-- A piece descriptor pointing to a range in a source buffer -/
structure Piece where
  source : BufferSource
  start : Nat
  length : Nat
  lineBreaks : Nat
  charCount : Nat
  deriving Repr, BEq, Inhabited

/-- Aggregated statistics for a node -/
structure Stats where
  bytes : Nat
  lines : Nat
  chars : Nat
  height : Nat
  deriving Repr, Inhabited, BEq

def Stats.empty : Stats := { bytes := 0, lines := 0, chars := 0, height := 0 }

def Stats.ofPiece (p : Piece) : Stats :=
  { bytes := p.length, lines := p.lineBreaks, chars := p.charCount, height := 1 }

instance : Add Stats where
  add a b := {
    bytes := a.bytes + b.bytes,
    lines := a.lines + b.lines,
    chars := a.chars + b.chars,
    height := max a.height b.height
  }

/-- B+ Tree Node Capacity (Branching Factor) -/
def NodeCapacity : Nat := 32

/-- Maximum piece size to bound linear scans (2KB) -/
def ChunkSize : Nat := 2048

/-- Bloom filter bit size for trigram indexing. -/
def BloomBits : Nat := 4096

/-- Bloom filter byte size. -/
def BloomBytes : Nat := BloomBits / 8


/-- Search metadata for a piece tree node. -/
structure SearchBloom where
  bits : ByteArray
  prefixBytes : Array UInt8
  suffixBytes : Array UInt8
  deriving Inhabited

def SearchBloom.empty : SearchBloom := {
  bits := ByteArray.mk (Array.replicate BloomBytes (0 : UInt8)),
  prefixBytes := #[],
  suffixBytes := #[]
}

instance : Repr SearchBloom where
  reprPrec sb _ :=
    s!"SearchBloom(bits={sb.bits.size}, prefix={sb.prefixBytes}, suffix={sb.suffixBytes})"

/-- Tracking the last insertion for merging contiguous edits -/
structure LastInsert where
  docOffset : Nat
  bufferIdx : Nat
  bufferOffset : Nat
  deriving Repr, Inhabited, BEq

/-- A node in the B+ Piece Tree -/
inductive PieceTree where
  | empty
  | leaf (pieces : Array Piece) (stats : Stats) (searchMeta : SearchBloom)
  | internal (children : Array PieceTree) (stats : Stats) (searchMeta : SearchBloom)
  deriving Inhabited, Repr

structure PieceTable where
  original : ByteArray
  addBuffers : Array ByteArray
  tree : PieceTree
  bloomBuildLeafBits : Bool := true
  undoStack : List (PieceTree × Nat) := []
  redoStack : List (PieceTree × Nat) := []
  undoStackCount : Nat := 0
  redoStackCount : Nat := 0
  undoLimit : Nat := 100
  lastInsert : Option LastInsert := none
  deriving Inhabited

end ViE
