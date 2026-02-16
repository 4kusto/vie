namespace ViE

/-- Source of a piece: either the original file (read-only) or the add buffer (append-only) -/
inductive BufferSource where
  | original
  | add
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

end ViE
