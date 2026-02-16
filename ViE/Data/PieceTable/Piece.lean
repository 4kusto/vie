namespace ViE

/-- Source of a piece: either the original file (read-only) or the add buffer (append-only) -/
inductive BufferSource where
  | original
  | add (idx : Nat)
  deriving Repr, BEq, Inhabited

/-- A piece descriptor pointing to a range in a source buffer -/
structure Piece where
  source : BufferSource
  start : UInt64
  length : UInt64
  lineBreaks : UInt64
  charCount : UInt64
  deriving Repr, BEq, Inhabited

/-- Aggregated statistics for a node -/
structure Stats where
  bytes : UInt64
  lines : UInt64
  chars : UInt64
  height : UInt64
  deriving Repr, Inhabited, BEq

def Stats.empty : Stats := { bytes := 0, lines := 0, chars := 0, height := 0 }

def Stats.ofPiece (p : Piece) : Stats :=
  { bytes := p.length, lines := p.lineBreaks, chars := p.charCount, height := 1 }

instance : Add Stats where
  add a b := {
    bytes := a.bytes + b.bytes,
    lines := a.lines + b.lines,
    chars := a.chars + b.chars,
    height := if a.height > b.height then a.height else b.height
  }

/-- B+ Tree Node Capacity (Branching Factor) -/
def NodeCapacity : Nat := 32

/-- Maximum piece size to bound linear scans (2KB) -/
def ChunkSize : Nat := 2048

/-- Soft cap for reusing the tail add-buffer to avoid excessive copy amplification. -/
def AddBufferReuseLimit : Nat := 64 * 1024

/-- Bloom filter bit size for trigram indexing. -/
def BloomBits : Nat := 4096

/-- Bloom filter byte size. -/
def BloomBytes : Nat := BloomBits / 8


/-- Search metadata for a piece tree node. -/
structure SearchBloom where
  bits : ByteArray
  prefixBytes : Array UInt8
  suffixBytes : Array UInt8
  hasBits : Bool := false
  deriving Inhabited

def SearchBloom.empty : SearchBloom := {
  bits := ByteArray.mk (Array.replicate BloomBytes (0 : UInt8)),
  prefixBytes := #[],
  suffixBytes := #[],
  hasBits := false
}

instance : Repr SearchBloom where
  reprPrec sb _ :=
    s!"SearchBloom(bits={sb.bits.size}, hasBits={sb.hasBits}, prefix={sb.prefixBytes}, suffix={sb.suffixBytes})"

/-- Internal node metadata for O(log n) child lookup -/
structure InternalMeta where
  /-- Cumulative byte offsets for each child (child[i] starts at cumulativeBytes[i]) -/
  cumulativeBytes : Array UInt64
  /-- Cumulative line counts for each child -/
  cumulativeLines : Array UInt64
  /-- Cumulative character counts for each child -/
  cumulativeChars : Array UInt64
  deriving Inhabited, Repr

def InternalMeta.empty : InternalMeta := {
  cumulativeBytes := #[0],
  cumulativeLines := #[0],
  cumulativeChars := #[0]
}

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
  | internal (children : Array PieceTree) (stats : Stats) (searchMeta : SearchBloom) (internalMeta : InternalMeta)
  deriving Inhabited, Repr

structure PieceTable where
  original : ByteArray
  addBuffers : Array ByteArray
  tree : PieceTree
  lineIndexCache : Option (Array Nat) := none
  bloomBuildLeafBits : Bool := true
  undoStack : List (PieceTree × Nat) := []
  redoStack : List (PieceTree × Nat) := []
  undoStackCount : Nat := 0
  redoStackCount : Nat := 0
  undoLimit : Nat := 100
  lastInsert : Option LastInsert := none
  deriving Inhabited

end ViE
