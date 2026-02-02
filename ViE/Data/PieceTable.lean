import ViE.Data.PieceTable.Piece
import ViE.Data.PieceTable.Types
import ViE.Data.PieceTable.Tree

namespace ViE

/-- Chunk size for splitting large files (16KB) -/
def PieceTable.ChunkSize : Nat := 1024 * 16

/-- Construct from bytes -/
def PieceTable.fromByteArray (bytes : ByteArray) : PieceTable :=
  if bytes.size == 0 then
    { original := bytes, add := ByteArray.empty, tree := PieceTree.empty, undoStack := [], redoStack := [], undoLimit := 100, lastInsert := none }
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
    { original := bytes, add := ByteArray.empty, tree := tree, undoStack := [], redoStack := [], undoLimit := 100, lastInsert := none }

/-- Construct from initial string -/
def PieceTable.fromString (s : String) : PieceTable :=
  PieceTable.fromByteArray s.toUTF8

/-- Convert tree to string -/
def PieceTable.toString (pt : PieceTable) : String :=
  PieceTree.getSubstring pt.tree 0 pt.tree.length pt

/--
  Insert text at the specified offset.

  params:
  - offset: The byte offset where insertion begins.
  - text: The string content to insert.
  - cursorOffset: The cursor position *after* this insertion, stored in the undo stack
    to restore cursor position when undoing this operation.
-/
def PieceTable.insert (pt : PieceTable) (offset : Nat) (text : String) (cursorOffset : Nat) : PieceTable :=
  if text.isEmpty then pt
  else
    let (pt', newPiece) := PieceTableHelper.appendText pt text
    let (l, r) := PieceTree.split pt.tree offset pt'
    let mid := PieceTree.mkLeaf #[newPiece]
    let newTree := PieceTree.concat (PieceTree.concat l mid) r

    -- Check optimization/merge compatibility
    let (finalUndoStack, newLastInsert) :=
      match pt.lastInsert with
      | some (lastOff, lastAddOff) =>
        if offset == lastOff && lastAddOff == pt.add.size then
          -- MERGE: Contiguous edit in doc and add buffer.
          -- Don't push to undoStack (reuse previous state as undo point)
          (pt.undoStack, some (offset + text.utf8ByteSize, lastAddOff + text.utf8ByteSize))
        else
          -- NO MERGE: Push current state
          let stack := (pt.tree, cursorOffset) :: pt.undoStack
          let params := if stack.length > pt.undoLimit then stack.take pt.undoLimit else stack
          (params, some (offset + text.utf8ByteSize, pt.add.size + text.utf8ByteSize))
      | none =>
          let stack := (pt.tree, cursorOffset) :: pt.undoStack
          let params := if stack.length > pt.undoLimit then stack.take pt.undoLimit else stack
          (params, some (offset + text.utf8ByteSize, pt.add.size + text.utf8ByteSize))

    { pt' with
      tree := newTree
      undoStack := finalUndoStack
      redoStack := []
      lastInsert := newLastInsert
    }

/--
  Delete a range of text.

  params:
  - offset: The starting byte offset of the range to delete.
  - length: The number of bytes to delete.
  - cursorOffset: The cursor position *after* this deletion, stored in the undo stack
    to restore cursor position when undoing this operation.
-/
def PieceTable.delete (pt : PieceTable) (offset : Nat) (length : Nat) (cursorOffset : Nat) : PieceTable :=
  if length == 0 then pt
  else
    let newTree := PieceTree.delete pt.tree offset length pt
    let stack := (pt.tree, cursorOffset) :: pt.undoStack
    let finalStack := if stack.length > pt.undoLimit then stack.take pt.undoLimit else stack

    { pt with
      tree := newTree
      undoStack := finalStack
      redoStack := []
      lastInsert := none -- Break merge chain
    }

/-- Commit the current edit group, forcing the next insert to start a new undo item. -/
def PieceTable.commit (pt : PieceTable) : PieceTable :=
  { pt with lastInsert := none }

/-- Undo the last operation -/
def PieceTable.undo (pt : PieceTable) (currentCursor : Nat) : PieceTable × Option Nat :=
  match pt.undoStack with
  | [] => (pt, none)
  | (prev, prevCursor) :: rest =>
    ({ pt with
      tree := prev
      undoStack := rest
      redoStack := (pt.tree, currentCursor) :: pt.redoStack
      lastInsert := none
    }, some prevCursor)

/-- Redo the last undone operation -/
def PieceTable.redo (pt : PieceTable) (currentCursor : Nat) : PieceTable × Option Nat :=
  match pt.redoStack with
  | [] => (pt, none)
  | (next, nextCursor) :: rest =>
    ({ pt with
      tree := next
      undoStack := (pt.tree, currentCursor) :: pt.undoStack
      redoStack := rest
      lastInsert := none
    }, some nextCursor)

/-- Get line from buffer -/
def PieceTable.getLine (pt : PieceTable) (lineIdx : Nat) : Option String :=
  PieceTree.getLine pt.tree lineIdx pt

/-- Get line range from buffer -/
def PieceTable.getLineRange (pt : PieceTable) (lineIdx : Nat) : Option (Nat × Nat) :=
  PieceTree.getLineRange pt.tree lineIdx pt

/-- Get line char length from buffer -/
def PieceTable.getLineLength (pt : PieceTable) (lineIdx : Nat) : Option Nat :=
  PieceTree.getLineLength pt.tree lineIdx pt

/-- Get byte offset from Row/Col position -/
def PieceTable.getOffsetFromPoint (pt : PieceTable) (row col : Nat) : Option Nat :=
  match PieceTable.getLineRange pt row with
  | some (startOff, len) =>
      -- Allow col up to len (inclusive) for appending at end of line
      if col <= len then some (startOff + col)
      else if col == len + 1 then some (startOff + len) -- Lenient for cursor logic? No, strict.
      else some (startOff + len) -- Clamp to end of line if strictly greater? Better to be safe.
  | none => none

def PieceTable.lineCount (pt : PieceTable) : Nat :=
  match pt.tree with
  | .leaf _ s => s.lines + 1
  | .internal _ s => s.lines + 1
  | .empty => 1

def PieceTable.length (pt : PieceTable) : Nat := pt.tree.length

/-- Check if the piece table buffer ends with a newline character.
    Optimized to avoid converting the entire buffer to string. -/
def PieceTable.endsWithNewline (pt : PieceTable) : Bool :=
  let len := pt.length
  if len == 0 then false
  else
    let s := PieceTree.getSubstring pt.tree (len - 1) len pt
    s == "\n"

partial def PieceTable.findLineForOffset (pt : PieceTable) (target : Nat) (low high : Nat) : Option (Nat × Nat) :=
  if low > high then none
  else
    let mid := (low + high) / 2
    match pt.getLineRange mid with
    | some (start, len) =>
      let endOff := start + len
      if target >= start && target <= endOff then
        some (mid, target - start)
      else if target < start then
         if mid == 0 then none
         else PieceTable.findLineForOffset pt target low (mid - 1)
      else
         PieceTable.findLineForOffset pt target (mid + 1) high
    | none => none

def PieceTable.getPointFromOffset (pt : PieceTable) (offset : Nat) : (Nat × Nat) :=
  match PieceTable.findLineForOffset pt offset 0 pt.lineCount with
  | some (r, c) => (r, c)
  | none => (0, 0) -- Fallback

end ViE
