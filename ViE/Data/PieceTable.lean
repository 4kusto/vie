import ViE.Data.PieceTable.Piece
import ViE.Data.PieceTable.Tree
import ViE.Unicode

namespace ViE

/-- Construct from bytes -/
def PieceTable.fromByteArray (bytes : ByteArray) (buildLeafBits : Bool := true) : PieceTable :=
  if bytes.size == 0 then
    { original := bytes, addBuffers := #[], tree := PieceTree.empty, bloomBuildLeafBits := buildLeafBits,
      undoStack := [], redoStack := [], undoLimit := 100, lastInsert := none }
  else
    -- Split bytes into chunks to avoid monolithic pieces
    let totalSize := bytes.size
    let rec splitChunks (start : Nat) (acc : Array Piece) : Array Piece :=
      if start >= totalSize then acc
      else
        let len := min ChunkSize (totalSize - start)
        let lines := Unicode.countNewlines bytes start len
        let chars := Unicode.countChars bytes start len
        let piece : Piece := { source := BufferSource.original, start := start, length := len, lineBreaks := lines, charCount := chars }
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
        . show 0 < ChunkSize
          unfold ChunkSize
          exact Nat.zero_lt_succ _
        · assumption
      · apply Nat.min_le_right

    let pieces := splitChunks 0 #[]
    let tmpPt : PieceTable := {
      original := bytes, addBuffers := #[], tree := PieceTree.empty, bloomBuildLeafBits := buildLeafBits,
      undoStack := [], redoStack := [], undoStackCount := 0, redoStackCount := 0, undoLimit := 100, lastInsert := none
    }
    let tree := PieceTree.fromPieces pieces tmpPt
    { original := bytes, addBuffers := #[], tree := tree, bloomBuildLeafBits := buildLeafBits,
      undoStack := [], redoStack := [], undoLimit := 100, lastInsert := none }

/-- Construct from initial string -/
def PieceTable.fromString (s : String) (buildLeafBits : Bool := true) : PieceTable :=
  PieceTable.fromByteArray s.toUTF8 buildLeafBits

/-- Convert tree to string -/
def PieceTable.toString (pt : PieceTable) : String :=
  PieceTree.getSubstring pt.tree 0 pt.tree.length pt

/--
  Insert text at the specified offset.
-/
def PieceTable.insert (pt : PieceTable) (offset : Nat) (text : String) (cursorOffset : Nat) : PieceTable :=
  if text.isEmpty then pt
  else
    let (pt', newPieces) := PieceTableHelper.appendText pt text
    let (l, r) := PieceTree.split pt.tree offset pt'
    let mid := PieceTree.fromPieces newPieces pt'
    let newTree := PieceTree.concat (PieceTree.concat l mid pt') r pt'

    -- Check optimization/merge compatibility
    let (finalUndoStack, newUndoCount, newLastInsert) :=
      match pt.lastInsert with
      | some last =>
        let lastBuf := pt.addBuffers.getD last.bufferIdx ByteArray.empty
        let isContig := offset == last.docOffset
        let isLastBuf := last.bufferIdx == pt.addBuffers.size - 1
        let isEndOfBuf := last.bufferOffset == lastBuf.size

        if isContig && isLastBuf && isEndOfBuf then
          -- MERGE: Contiguous edit in doc and add buffer.
          -- Don't push to undoStack (reuse previous state as undo point)
          (pt.undoStack, pt.undoStackCount, some { docOffset := offset + text.toUTF8.size, bufferIdx := pt.addBuffers.size, bufferOffset := text.toUTF8.size })
        else
          -- NO MERGE: Push current state
          let stack := (pt.tree, cursorOffset) :: pt.undoStack
          let newCount := pt.undoStackCount + 1
          let (finalStack, finalCount) := if newCount > pt.undoLimit then (stack.take pt.undoLimit, pt.undoLimit) else (stack, newCount)
          (finalStack, finalCount, some { docOffset := offset + text.toUTF8.size, bufferIdx := pt.addBuffers.size, bufferOffset := text.toUTF8.size })
      | none =>
          let stack := (pt.tree, cursorOffset) :: pt.undoStack
          let newCount := pt.undoStackCount + 1
          let (finalStack, finalCount) := if newCount > pt.undoLimit then (stack.take pt.undoLimit, pt.undoLimit) else (stack, newCount)
          (finalStack, finalCount, some { docOffset := offset + text.toUTF8.size, bufferIdx := pt.addBuffers.size, bufferOffset := text.toUTF8.size })

    { pt' with
      tree := newTree
      undoStack := finalUndoStack
      undoStackCount := newUndoCount
      redoStack := []
      redoStackCount := 0
      lastInsert := newLastInsert
    }

/-- Delete a range of text. -/
def PieceTable.delete (pt : PieceTable) (offset : Nat) (length : Nat) (cursorOffset : Nat) : PieceTable :=
  if length == 0 then pt
  else
    let newTree := PieceTree.delete pt.tree offset length pt
    let stack := (pt.tree, cursorOffset) :: pt.undoStack
    let newCount := pt.undoStackCount + 1
    let (finalStack, finalCount) := if newCount > pt.undoLimit then (stack.take pt.undoLimit, pt.undoLimit) else (stack, newCount)

    { pt with
      tree := newTree
      undoStack := finalStack
      undoStackCount := finalCount
      redoStack := []
      redoStackCount := 0
      lastInsert := none -- Break merge chain
    }

/-- Insert text without touching undo/redo stacks (internal for bulk edits). -/
def PieceTable.insertRaw (pt : PieceTable) (offset : Nat) (text : String) : PieceTable :=
  if text.isEmpty then pt
  else
    let (pt', newPieces) := PieceTableHelper.appendText pt text
    let (l, r) := PieceTree.split pt.tree offset pt'
    let mid := PieceTree.fromPieces newPieces pt'
    let newTree := PieceTree.concat (PieceTree.concat l mid pt') r pt'
    { pt' with tree := newTree, lastInsert := none }

/-- Delete a range without touching undo/redo stacks (internal for bulk edits). -/
def PieceTable.deleteRaw (pt : PieceTable) (offset : Nat) (length : Nat) : PieceTable :=
  if length == 0 then pt
  else
    let newTree := PieceTree.delete pt.tree offset length pt
    { pt with tree := newTree, lastInsert := none }

/-- Apply a list of replacements as a single undoable edit. -/
def PieceTable.applyReplacements (pt : PieceTable) (cursorOffset : Nat) (replacements : Array (Nat × Nat)) (newText : String) : PieceTable :=
  if replacements.isEmpty then
    pt
  else
    let oldTree := pt.tree
    let pt' := Id.run do
      let mut acc := pt
      for (startOff, endOff) in replacements.reverse do
        let len := endOff - startOff
        acc := acc.deleteRaw startOff len
        acc := acc.insertRaw startOff newText
      return acc
    let stack := (oldTree, cursorOffset) :: pt'.undoStack
    let newCount := pt'.undoStackCount + 1
    let (finalStack, finalCount) :=
      if newCount > pt'.undoLimit then
        (stack.take pt'.undoLimit, pt'.undoLimit)
      else
        (stack, newCount)
    { pt' with
      undoStack := finalStack
      undoStackCount := finalCount
      redoStack := []
      redoStackCount := 0
      lastInsert := none
    }

/-- Apply deletions as a single undoable edit. -/
def PieceTable.applyDeletions (pt : PieceTable) (cursorOffset : Nat) (ranges : Array (Nat × Nat)) : PieceTable :=
  PieceTable.applyReplacements pt cursorOffset ranges ""

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
      undoStackCount := pt.undoStackCount - 1
      redoStack := (pt.tree, currentCursor) :: pt.redoStack
      redoStackCount := pt.redoStackCount + 1
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
      undoStackCount := pt.undoStackCount + 1
      redoStack := rest
      redoStackCount := pt.redoStackCount - 1
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
      -- Col is a display column; convert to byte offset within the line.
      let lineStr := PieceTree.getSubstring pt.tree startOff len pt
      let byteOff := ViE.Unicode.displayColToByteOffset lineStr col
      let clamped := if byteOff <= len then byteOff else len
      some (startOff + clamped)
  | none => none


def PieceTable.length (pt : PieceTable) : Nat := (PieceTree.stats pt.tree).bytes

/-- Check if the piece table buffer ends with a newline character. -/
def PieceTable.endsWithNewline (pt : PieceTable) : Bool :=
  let len := pt.length
  if len == 0 then false
  else
    let s := PieceTree.getSubstring pt.tree (len - 1) 1 pt
    s == "\n"

def PieceTable.lineCount (pt : PieceTable) : Nat :=
  let breaks := PieceTree.lineBreaks pt.tree
  if breaks == 0 then 1
  -- If the file ends with a newline, Vim doesn't count it as a new empty line
  -- unless it's preceded by another newline (e.g., "a\n\n" is 2 lines).
  else if pt.endsWithNewline then breaks
  else breaks + 1

private def PieceTable.findLineForOffsetCore (pt : PieceTable) (target : Nat) (low high : Nat) (fuel : Nat) : Option (Nat × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
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
           else PieceTable.findLineForOffsetCore pt target low (mid - 1) fuel
        else
           PieceTable.findLineForOffsetCore pt target (mid + 1) high fuel
      | none => none

def PieceTable.findLineForOffset (pt : PieceTable) (target : Nat) (low high : Nat) : Option (Nat × Nat) :=
  let fuel := pt.lineCount + 1
  PieceTable.findLineForOffsetCore pt target low high fuel

def PieceTable.getPointFromOffset (pt : PieceTable) (offset : Nat) : (Nat × Nat) :=
  match PieceTable.findLineForOffset pt offset 0 pt.lineCount with
  | some (r, c) =>
    match PieceTable.getLineRange pt r with
    | some (startOff, len) =>
      let rel := if c <= len then c else len
      let sub := PieceTree.getSubstring pt.tree startOff rel pt
      let displayCol := ViE.Unicode.stringWidth sub
      (r, displayCol)
    | none => (r, c)
  | none => (0, 0) -- Fallback

end ViE
