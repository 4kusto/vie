import ViE.Data.PieceTable.Piece

namespace ViE.PieceTable

/-- A node in the B+ Piece Tree -/
inductive PieceTree where
  | empty
  | leaf (pieces : Array Piece) (stats : Stats)
  | internal (children : Array PieceTree) (stats : Stats)
  deriving Repr, Inhabited

structure PieceTable where
  original : ByteArray
  add : ByteArray
  tree : PieceTree
  deriving Inhabited

end ViE.PieceTable
