-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.Data.PieceTable.Piece
import ViE.Data.PieceTable.Tree
import ViE.Unicode

namespace ViE

/-- Build line-start offsets by walking the piece tree in document order. -/
private def buildLineIndex (pt : PieceTable) : Array Nat := Id.run do
  let capacity := PieceTree.lineBreaks pt.tree + 1
  let mut starts : Array Nat := (Array.mkEmpty capacity).push 0
  let mut docOff := 0
  let mut stack : List PieceTree := [pt.tree]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | node :: rest =>
        stack := rest
        match node with
        | PieceTree.empty => pure ()
        | PieceTree.leaf pieces _ _ =>
            for p in pieces do
              let buf := PieceTableHelper.getBuffer pt p.source
              let stop := p.start.toNat + p.length.toNat
              let mut i := p.start.toNat
              while i < stop do
                if buf[i]! == 10 then
                  starts := starts.push (docOff + 1)
                i := i + 1
                docOff := docOff + 1
        | PieceTree.internal children _ _ _ =>
            let mut i := children.size
            while i > 0 do
              let j := i - 1
              stack := children[j]! :: stack
              i := j
  return starts

private def withLineIndexCache (pt : PieceTable) : PieceTable :=
  { pt with lineIndexCache := some (buildLineIndex pt) }

/-- Construct from bytes. `buildOnEdit` controls bloom rebuilding during subsequent edits. -/
def PieceTable.fromByteArray (bytes : ByteArray) (buildLeafBits : Bool := true) (buildOnEdit : Bool := false) : PieceTable :=
  if bytes.size == 0 then
    {
      original := bytes, addBuffers := #[], tree := PieceTree.empty, bloomBuildLeafBits := buildLeafBits,
      bloomBuildOnEdit := buildOnEdit,
      undoStack := [], redoStack := [], undoLimit := 100, lastInsert := none, lineIndexCache := some #[0]
    }
  else
    let totalSize := bytes.size
    -- Split bytes into chunks while collecting line starts in one pass.
    let rec splitChunks (start : Nat) (pieces : Array Piece) (starts : Array Nat) : (Array Piece × Array Nat) :=
      if start >= totalSize then
        (pieces, starts)
      else
        let len := min ChunkSize (totalSize - start)
        let stop := start + len
        let rec scan (i : Nat) (lines chars : Nat) (lineStarts : Array Nat) : (Nat × Nat × Array Nat) :=
          if i >= stop then
            (lines, chars, lineStarts)
          else
            let b := bytes[i]!
            let lineStarts' := if b == 10 then lineStarts.push (i + 1) else lineStarts
            let lines' := if b == 10 then lines + 1 else lines
            let chars' := if (b &&& 0xC0) != 0x80 then chars + 1 else chars
            scan (i + 1) lines' chars' lineStarts'
        let (lines, chars, starts') := scan start 0 0 starts
        let piece : Piece := { source := BufferSource.original, start := start.toUInt64, length := len.toUInt64, lineBreaks := lines.toUInt64, charCount := chars.toUInt64 }
        splitChunks (start + len) (pieces.push piece) starts'
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

    let (pieces, starts) := splitChunks 0 #[] #[0]
    let tmpPt : PieceTable := {
      -- Build bloom bits during initial load if enabled, regardless of edit policy.
      original := bytes, addBuffers := #[], tree := PieceTree.empty, bloomBuildLeafBits := buildLeafBits, bloomBuildOnEdit := true,
      undoStack := [], redoStack := [], undoStackCount := 0, redoStackCount := 0, undoLimit := 100, lastInsert := none
    }
    let tree := PieceTree.fromPieces pieces tmpPt
    {
      original := bytes, addBuffers := #[], tree := tree, bloomBuildLeafBits := buildLeafBits, bloomBuildOnEdit := buildOnEdit,
      undoStack := [], redoStack := [], undoLimit := 100, lastInsert := none, lineIndexCache := some starts
    }

/-- Construct from initial string. -/
def PieceTable.fromString (s : String) (buildLeafBits : Bool := true) (buildOnEdit : Bool := false) : PieceTable :=
  PieceTable.fromByteArray s.toUTF8 buildLeafBits buildOnEdit

/-- Convert tree to string -/
def PieceTable.toString (pt : PieceTable) : String :=
  PieceTree.getSubstring pt.tree 0 pt.tree.length pt

private def PieceTable.lineIndex (pt : PieceTable) : Array Nat :=
  match pt.lineIndexCache with
  | some idx => idx
  | none => buildLineIndex pt

/--
  Insert text at the specified offset.
-/
def PieceTable.insert (pt : PieceTable) (offset : Nat) (text : String) (cursorOffset : Nat) : PieceTable :=
  if text.isEmpty then pt
  else
    let (pt', newPieces, appendMeta) := PieceTableHelper.appendText pt text
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
          (pt.undoStack, pt.undoStackCount, some { docOffset := offset + text.toUTF8.size, bufferIdx := appendMeta.bufferIdx, bufferOffset := appendMeta.bufferEnd })
        else
          -- NO MERGE: Push current state
          let stack := (pt.tree, cursorOffset) :: pt.undoStack
          let newCount := pt.undoStackCount + 1
          let (finalStack, finalCount) := if newCount > pt.undoLimit then (stack.take pt.undoLimit, pt.undoLimit) else (stack, newCount)
          (finalStack, finalCount, some { docOffset := offset + text.toUTF8.size, bufferIdx := appendMeta.bufferIdx, bufferOffset := appendMeta.bufferEnd })
      | none =>
          let stack := (pt.tree, cursorOffset) :: pt.undoStack
          let newCount := pt.undoStackCount + 1
          let (finalStack, finalCount) := if newCount > pt.undoLimit then (stack.take pt.undoLimit, pt.undoLimit) else (stack, newCount)
          (finalStack, finalCount, some { docOffset := offset + text.toUTF8.size, bufferIdx := appendMeta.bufferIdx, bufferOffset := appendMeta.bufferEnd })

    withLineIndexCache { pt' with
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

    withLineIndexCache { pt with
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
    let (pt', newPieces, _) := PieceTableHelper.appendText pt text
    let (l, r) := PieceTree.split pt.tree offset pt'
    let mid := PieceTree.fromPieces newPieces pt'
    let newTree := PieceTree.concat (PieceTree.concat l mid pt') r pt'
    { pt' with tree := newTree, lineIndexCache := none, lastInsert := none }

/-- Delete a range without touching undo/redo stacks (internal for bulk edits). -/
def PieceTable.deleteRaw (pt : PieceTable) (offset : Nat) (length : Nat) : PieceTable :=
  if length == 0 then pt
  else
    let newTree := PieceTree.delete pt.tree offset length pt
    { pt with tree := newTree, lineIndexCache := none, lastInsert := none }

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
    withLineIndexCache { pt' with
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
    (withLineIndexCache { pt with
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
    (withLineIndexCache { pt with
      tree := next
      undoStack := (pt.tree, currentCursor) :: pt.undoStack
      undoStackCount := pt.undoStackCount + 1
      redoStack := rest
      redoStackCount := pt.redoStackCount - 1
      lastInsert := none
    }, some nextCursor)

/-- Get line range from buffer -/
def PieceTable.getLineRange (pt : PieceTable) (lineIdx : Nat) : Option (Nat × Nat) :=
  let idx := pt.lineIndex
  match idx[lineIdx]? with
  | none => none
  | some startOff =>
      let totalLen := pt.tree.length
      match idx[lineIdx + 1]? with
      | some nextStart =>
          let len := if nextStart > startOff then (nextStart - startOff - 1) else 0
          some (startOff, len)
      | none =>
          some (startOff, totalLen - startOff)

/-- Get line from buffer -/
def PieceTable.getLine (pt : PieceTable) (lineIdx : Nat) : Option String :=
  match PieceTable.getLineRange pt lineIdx with
  | some (off, len) => some (PieceTree.getSubstring pt.tree off len pt)
  | none => none

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


def PieceTable.length (pt : PieceTable) : Nat := (PieceTree.stats pt.tree).bytes.toNat

/-- Check if the piece table buffer ends with a newline character. -/
def PieceTable.endsWithNewline (pt : PieceTable) : Bool :=
  let len := pt.length
  if len == 0 then false
  else
    let s := PieceTree.getSubstring pt.tree (len - 1) 1 pt
    s == "\n"

def PieceTable.lineCount (pt : PieceTable) : Nat :=
  let breaks := PieceTree.lineBreaks pt.tree
  -- In editor state, each newline creates a new line slot.
  -- Keep lineCount consistent with getLineRange/getLine and cursor rows.
  breaks + 1

private def PieceTable.findLineForOffsetCore (pt : PieceTable) (target : Nat) (low highExcl : Nat) : Option (Nat × Nat) :=
  if low >= highExcl then none
  else
    let mid := low + (highExcl - low) / 2
    match pt.getLineRange mid with
    | some (start, len) =>
      let endOff := start + len
      if target >= start && target <= endOff then
        some (mid, target - start)
      else if target < start then
        PieceTable.findLineForOffsetCore pt target low mid
      else
        PieceTable.findLineForOffsetCore pt target (mid + 1) highExcl
    | none => none
  termination_by highExcl - low
  decreasing_by
    · simp_wf
      omega
    · simp_wf
      omega

def PieceTable.findLineForOffset (pt : PieceTable) (target : Nat) (low high : Nat) : Option (Nat × Nat) :=
  PieceTable.findLineForOffsetCore pt target low (high + 1)

def PieceTable.getPointFromOffset (pt : PieceTable) (offset : Nat) : (Nat × Nat) :=
  let hi := pt.lineCount - 1
  match PieceTable.findLineForOffset pt offset 0 hi with
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
