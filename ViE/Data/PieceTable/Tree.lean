import ViE.Data.PieceTable.Piece
import ViE.Unicode

namespace ViE

namespace PieceTableHelper

/-- Get the buffer data corresponding to a source -/
def getBuffer (pt : ViE.PieceTable) (source : ViE.BufferSource) : ByteArray :=
  match source with
  | ViE.BufferSource.original => pt.original
  | ViE.BufferSource.add idx => pt.addBuffers.getD idx (ByteArray.mk #[])

/-- Append text to add buffer, splitting into chunks if necessary -/
def appendText (pt : ViE.PieceTable) (text : String) : (ViE.PieceTable × Array ViE.Piece) :=
  let bytes := text.toUTF8
  let totalSize := bytes.size
  let bufferIdx := pt.addBuffers.size
  let newAddBuffers := pt.addBuffers.push bytes

  let rec splitChunks (start : Nat) (acc : Array ViE.Piece) : Array ViE.Piece :=
    if start >= totalSize then acc
    else
      let len := min ViE.ChunkSize (totalSize - start)
      let lines := ViE.Unicode.countNewlines bytes start len
      let chars := ViE.Unicode.countChars bytes start len
      let piece : ViE.Piece := {
        source := ViE.BufferSource.add bufferIdx,
        start := start,
        length := len,
        lineBreaks := lines,
        charCount := chars
      }
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
        . show 0 < ViE.ChunkSize
          unfold ViE.ChunkSize
          exact Nat.zero_lt_succ _
        · assumption
      · apply Nat.min_le_right

  let ps := splitChunks 0 #[]
  ({ pt with addBuffers := newAddBuffers }, ps)

/-- Split a piece into two at a given relative offset -/
def splitPiece (p : ViE.Piece) (offset : Nat) (pt : ViE.PieceTable) : (ViE.Piece × ViE.Piece) :=
  let buf := getBuffer pt p.source
  let leftLen := offset
  let rightLen := p.length - offset

  let leftLines := ViE.Unicode.countNewlines buf p.start leftLen
  let leftChars := ViE.Unicode.countChars buf p.start leftLen

  let leftPiece : ViE.Piece := { p with length := leftLen, lineBreaks := leftLines, charCount := leftChars }
  let rightPiece : ViE.Piece := { p with
    start := p.start + leftLen,
    length := rightLen,
    lineBreaks := p.lineBreaks - leftLines,
    charCount := p.charCount - leftChars
  }
  (leftPiece, rightPiece)

end PieceTableHelper

namespace PieceTree

/-- Get stats of a tree -/
def stats (t : ViE.PieceTree) : ViE.Stats :=
  match t with
  | ViE.PieceTree.empty => ViE.Stats.empty
  | ViE.PieceTree.leaf _ s => s
  | ViE.PieceTree.internal _ s => s

def length (t : ViE.PieceTree) : Nat := (stats t).bytes
def lineBreaks (t : ViE.PieceTree) : Nat := (stats t).lines
def height (t : ViE.PieceTree) : Nat := (stats t).height

/-- Create a leaf node -/
def mkLeaf (pieces : Array ViE.Piece) : ViE.PieceTree :=
  let s := pieces.foldl (fun acc p => acc + (ViE.Stats.ofPiece p)) ViE.Stats.empty
  ViE.PieceTree.leaf pieces s

/-- Create an internal node -/
def mkInternal (children : Array ViE.PieceTree) : ViE.PieceTree :=
  let s := children.foldl (fun acc c => acc + (stats c)) ViE.Stats.empty
  let s := { s with height := s.height + 1 }
  ViE.PieceTree.internal children s

/-- Efficiently concatenate a list of pieces into a tree -/
partial def fromPieces (pieces : Array ViE.Piece) : ViE.PieceTree :=
  if pieces.isEmpty then ViE.PieceTree.empty
  else if pieces.size <= ViE.NodeCapacity then
    mkLeaf pieces
  else
    let mid := pieces.size / 2
    let left := fromPieces (pieces.extract 0 mid)
    let right := fromPieces (pieces.extract mid pieces.size)
    mkInternal #[left, right]

/-- Concatenate two trees while maintaining B+ tree invariants -/
partial def concat (l : ViE.PieceTree) (r : ViE.PieceTree) : ViE.PieceTree :=
  match l, r with
  | ViE.PieceTree.empty, _ => r
  | _, ViE.PieceTree.empty => l

  | ViE.PieceTree.leaf ps1 _, ViE.PieceTree.leaf ps2 _ =>
    -- Try to merge the last piece of ps1 with the first piece of ps2
    if ps1.size > 0 && ps2.size > 0 then
      let p1 := ps1.back!
      let p2 := ps2[0]!
      if p1.source == p2.source && p1.start + p1.length == p2.start then
        let mergedPiece : ViE.Piece := { p1 with
          length := p1.length + p2.length,
          lineBreaks := p1.lineBreaks + p2.lineBreaks,
          charCount := p1.charCount + p2.charCount
        }
        let ps := (ps1.pop).push mergedPiece ++ (ps2.extract 1 ps2.size)
        if ps.size <= ViE.NodeCapacity then
          mkLeaf ps
        else
          let mid := ps.size / 2
          mkInternal #[mkLeaf (ps.extract 0 mid), mkLeaf (ps.extract mid ps.size)]
      else
        let ps := ps1 ++ ps2
        if ps.size <= ViE.NodeCapacity then mkLeaf ps
        else mkInternal #[mkLeaf ps1, mkLeaf ps2]
    else if ps1.size > 0 then l
    else r

  | ViE.PieceTree.internal cs1 _, ViE.PieceTree.internal cs2 _ =>
    let h1 := height l
    let h2 := height r
    if h1 == h2 then
      -- Merge boundary children
      let lastChild := cs1.back!
      let firstChild := cs2[0]!
      let merged := concat lastChild firstChild
      match merged with
      | ViE.PieceTree.internal newCS s =>
        if s.height == h1 then
           -- newCS is at the same level as siblings
           let combined := (cs1.pop) ++ newCS ++ (cs2.extract 1 cs2.size)
           if combined.size <= ViE.NodeCapacity then mkInternal combined
           else
             let mid := combined.size / 2
             mkInternal #[mkInternal (combined.extract 0 mid), mkInternal (combined.extract mid combined.size)]
        else
           -- height did not increase, just one child
           let combined := (cs1.pop).push merged ++ (cs2.extract 1 cs2.size)
           if combined.size <= ViE.NodeCapacity then mkInternal combined
           else
             let mid := combined.size / 2
             mkInternal #[mkInternal (combined.extract 0 mid), mkInternal (combined.extract mid combined.size)]
      | _ =>
        let combined := (cs1.pop).push merged ++ (cs2.extract 1 cs2.size)
        if combined.size <= ViE.NodeCapacity then mkInternal combined
        else
          let mid := combined.size / 2
          mkInternal #[mkInternal (combined.extract 0 mid), mkInternal (combined.extract mid combined.size)]
    else if h1 > h2 then
      -- Insert r into l's right side
      let lastChild := cs1.back!
      let newLast := concat lastChild r
      match newLast with
      | ViE.PieceTree.internal newChildren s =>
        if s.height == h1 then
           -- Split happened at l's level
           let combined := (cs1.pop) ++ newChildren
           if combined.size <= ViE.NodeCapacity then mkInternal combined
           else
              let mid := combined.size / 2
              mkInternal #[mkInternal (combined.extract 0 mid), mkInternal (combined.extract mid combined.size)]
        else
           mkInternal ((cs1.pop).push newLast)
      | _ => mkInternal ((cs1.pop).push newLast)
    else
      -- Insert l into r's left side
      let firstChild := cs2[0]!
      let newFirst := concat l firstChild
      match newFirst with
      | ViE.PieceTree.internal newChildren s =>
        if s.height == h2 then
           let combined := newChildren ++ (cs2.extract 1 cs2.size)
           if combined.size <= ViE.NodeCapacity then mkInternal combined
           else
              let mid := combined.size / 2
              mkInternal #[mkInternal (combined.extract 0 mid), mkInternal (combined.extract mid combined.size)]
        else
           mkInternal (#[newFirst] ++ (cs2.extract 1 cs2.size))
      | _ => mkInternal (#[newFirst] ++ (cs2.extract 1 cs2.size))

  -- Mixed types: wrap the smaller one and recurse
  | ViE.PieceTree.leaf .. , ViE.PieceTree.internal .. => concat (mkInternal #[l]) r
  | ViE.PieceTree.internal .. , ViE.PieceTree.leaf .. => concat l (mkInternal #[r])

/-- Split the tree at a given byte offset -/
partial def split (t : ViE.PieceTree) (offset : Nat) (pt : ViE.PieceTable) : (ViE.PieceTree × ViE.PieceTree) :=
  match t with
  | ViE.PieceTree.empty => (ViE.PieceTree.empty, ViE.PieceTree.empty)
  | ViE.PieceTree.leaf pieces _ =>
    let rec findSplitLeaf (i : Nat) (accOffset : Nat) : (ViE.PieceTree × ViE.PieceTree) :=
      if i >= pieces.size then (t, ViE.PieceTree.empty)
      else
        let p := pieces[i]!
        if offset < accOffset + p.length then
          let relOffset := offset - accOffset
          if relOffset == 0 then
             (mkLeaf (pieces.extract 0 i), mkLeaf (pieces.extract i pieces.size))
          else
             let (p1, p2) := PieceTableHelper.splitPiece p relOffset pt
             (mkLeaf ((pieces.extract 0 i).push p1), mkLeaf (#[p2] ++ (pieces.extract (i + 1) pieces.size)))
        else
          findSplitLeaf (i + 1) (accOffset + p.length)
    findSplitLeaf 0 0
  | ViE.PieceTree.internal children _ =>
    let rec findSplitInternal (i : Nat) (accOffset : Nat) : (ViE.PieceTree × ViE.PieceTree) :=
      if i >= children.size then (t, ViE.PieceTree.empty)
      else
        let c := children[i]!
        let cLen := length c
        if offset < accOffset + cLen then
          let (l, r) := split c (offset - accOffset) pt
          let leftSide := mkInternal ((children.extract 0 i).push l)
          let rightSide := mkInternal (#[r] ++ (children.extract (i + 1) children.size))
          (leftSide, rightSide)
        else
          findSplitInternal (i + 1) (accOffset + cLen)
    findSplitInternal 0 0

/-- Delete range from tree -/
def delete (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ViE.PieceTree :=
  let (l, mid_r) := split t offset pt
  let (_, r) := split mid_r len pt
  concat l r

/-- Get substring from tree -/
partial def getSubstring (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : String :=
  let rec collect (t : ViE.PieceTree) (off : Nat) (l : Nat) (acc : Array ByteArray) : (Array ByteArray × Nat) :=
    if l == 0 then (acc, 0)
    else match t with
      | ViE.PieceTree.empty => (acc, 0)
      | ViE.PieceTree.leaf pieces _ =>
        let rec scanLeaf (i : Nat) (accOffset : Nat) (currAcc : Array ByteArray) (remain : Nat) : (Array ByteArray × Nat) :=
          if i >= pieces.size || remain == 0 then (currAcc, l - remain)
          else
            let p := pieces[i]!
            let pLen := p.length
            if off < accOffset + pLen then
              let pStart := if off > accOffset then off - accOffset else 0
              let readLen := min remain (pLen - pStart)
              let buf := PieceTableHelper.getBuffer pt p.source
              let slice := buf.extract (p.start + pStart) (p.start + pStart + readLen)
              scanLeaf (i + 1) (accOffset + pLen) (currAcc.push slice) (remain - readLen)
            else
              scanLeaf (i + 1) (accOffset + pLen) currAcc remain
        scanLeaf 0 0 acc l
      | ViE.PieceTree.internal children _ =>
        let rec scanInternal (i : Nat) (accOffset : Nat) (currAcc : Array ByteArray) (remain : Nat) : (Array ByteArray × Nat) :=
          if i >= children.size || remain == 0 then (currAcc, l - remain)
          else
            let c := children[i]!
            let cLen := length c
            if off < accOffset + cLen then
              let cStart := if off > accOffset then off - accOffset else 0
              let (newAcc, readInThisChild) := collect c cStart remain currAcc
              scanInternal (i + 1) (accOffset + cLen) newAcc (remain - readInThisChild)
            else
              scanInternal (i + 1) (accOffset + cLen) currAcc remain
        scanInternal 0 0 acc l
  let (chunks, _) := collect t offset len #[]
  let combined := chunks.foldl (fun (acc : ByteArray) (b : ByteArray) => acc ++ b) (ByteArray.mk #[])
  String.fromUTF8! combined

/-- Find the leaf and relative offset containing the Nth newline -/
partial def findNthNewlineLeaf (t : ViE.PieceTree) (n : Nat) (pt : ViE.PieceTable) : Option (ViE.Piece × Nat × Nat) :=
  let rec scan (t : ViE.PieceTree) (n : Nat) (accOffset : Nat) : Option (ViE.Piece × Nat × Nat) :=
    match t with
    | ViE.PieceTree.empty => none
    | ViE.PieceTree.leaf pieces _ =>
      let rec findInPieces (i : Nat) (currN : Nat) (currOff : Nat) : Option (ViE.Piece × Nat × Nat) :=
        if i >= pieces.size then none
        else
          let p := pieces[i]!
          if currN < p.lineBreaks then
            let buf := PieceTableHelper.getBuffer pt p.source
            let rec findOffset (j : Nat) (targetN : Nat) : Nat :=
              if j >= p.length then p.length
              else if buf[p.start + j]! == 10 then
                if targetN == 0 then j + 1
                else findOffset (j + 1) (targetN - 1)
              else findOffset (j + 1) targetN
            let relOffset := findOffset 0 currN
            some (p, currOff, relOffset)
          else
            findInPieces (i + 1) (currN - p.lineBreaks) (currOff + p.length)
      findInPieces 0 n accOffset
    | ViE.PieceTree.internal children _ =>
      let rec findInChildren (i : Nat) (currN : Nat) (currOff : Nat) : Option (ViE.Piece × Nat × Nat) :=
        if i >= children.size then none
        else
          let child := children[i]!
          let childLines := lineBreaks child
          if currN < childLines then
            scan child currN currOff
          else
            findInChildren (i + 1) (currN - childLines) (currOff + length child)
      findInChildren 0 n accOffset
  scan t n 0

/-- Get range of a line in byte offsets -/
def getLineRange (t : ViE.PieceTree) (lineIdx : Nat) (pt : ViE.PieceTable) : Option (Nat × Nat) :=
  if lineIdx == 0 then
    let start := 0
    let endOff := match findNthNewlineLeaf t 0 pt with
      | some (_, acc, rel) => acc + rel - 1
      | none => length t
    some (start, endOff)
  else
    match findNthNewlineLeaf t (lineIdx - 1) pt with
    | some (_, acc, rel) =>
      let start := acc + rel
      let endOff := match findNthNewlineLeaf t lineIdx pt with
        | some (_, acc2, rel2) => acc2 + rel2 - 1
        | none => length t
      some (start, endOff - start)
    | none => none

def getLine (t : ViE.PieceTree) (lineIdx : Nat) (pt : ViE.PieceTable) : Option String :=
  match getLineRange t lineIdx pt with
  | some (off, len) => some (getSubstring t off len pt)
  | none => none

def getLineLength (t : ViE.PieceTree) (lineIdx : Nat) (pt : ViE.PieceTable) : Option Nat :=
  match getLineRange t lineIdx pt with
  | some (_, len) => some len
  | none => none

end PieceTree

end ViE
