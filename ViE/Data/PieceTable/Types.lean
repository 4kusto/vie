import ViE.Data.PieceTable.Piece

namespace ViE

/-- A node in the B+ Piece Tree -/
inductive PieceTree : Type _ where
  | empty
  | leaf (pieces : Array Piece) (stats : Stats)
  | internal (children : Array PieceTree) (stats : Stats)
  deriving Repr, Inhabited

structure PieceTable where
  original : ByteArray
  add : ByteArray
  tree : PieceTree
  undoStack : List (PieceTree × Nat) := []
  redoStack : List (PieceTree × Nat) := []
  undoLimit : Nat := 100
  lastInsert : Option (Nat × Nat) := none
  deriving Inhabited

end ViE
