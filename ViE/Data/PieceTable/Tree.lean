import ViE.Data.PieceTable.Piece
import ViE.Data.PieceTable.Types
import ViE.Unicode

namespace ViE.PieceTable

namespace PieceTableHelper

/-- Get the buffer data corresponding to a source -/
def getBuffer (pt : PieceTable) (source : BufferSource) : ByteArray :=
  match source with
  | .original => pt.original
  | .add => pt.add

/-- Append text to add buffer -/
def appendText (pt : PieceTable) (text : String) : (PieceTable × Piece) :=
  let bytes := text.toUTF8
  let start := pt.add.size
  let len := bytes.size
  let newAdd := pt.add ++ bytes
  let newLines := ViE.Unicode.countNewlines bytes 0 len
  let newChars := ViE.Unicode.countChars bytes 0 len
  let piece := { source := .add, start := start, length := len, lineBreaks := newLines, charCount := newChars }
  ({ pt with add := newAdd }, piece)

/-- Split a piece into two at a given relative offset. -/
def splitPiece (pt : PieceTable) (p : Piece) (offset : Nat) : (Piece × Piece) :=
  let buf := getBuffer pt p.source
  let leftLen := offset
  let rightLen := p.length - offset
  let leftLines := ViE.Unicode.countNewlines buf p.start leftLen
  let rightLines := p.lineBreaks - leftLines
  let leftChars := ViE.Unicode.countChars buf p.start leftLen
  let rightChars := p.charCount - leftChars
  let leftP := { p with length := leftLen, lineBreaks := leftLines, charCount := leftChars }
  let rightP := { p with start := p.start + leftLen, length := rightLen, lineBreaks := rightLines, charCount := rightChars }
  (leftP, rightP)

end PieceTableHelper

namespace PieceTree

/-- Get stats of a tree -/
def stats : PieceTree → Stats
  | empty => Stats.empty
  | leaf _ s => s
  | internal _ s => s

def length (t : PieceTree) : Nat := t.stats.bytes
def lineBreaks (t : PieceTree) : Nat := t.stats.lines
def height (t : PieceTree) : Nat := t.stats.height

/-- Helper to construct a leaf node from pieces -/
def mkLeaf (pieces : Array Piece) : PieceTree :=
  let stats := pieces.foldl (fun s p =>
    { s with bytes := s.bytes + p.length, lines := s.lines + p.lineBreaks, chars := s.chars + p.charCount })
    { bytes := 0, lines := 0, chars := 0, height := 1 }
  leaf pieces stats

/-- Helper to construct an internal node from children -/
def mkInternal (children : Array PieceTree) : PieceTree :=
  if children.isEmpty then empty
  else
    let firstHeight := (children[0]!).height
    let h := firstHeight + 1
    let stats := children.foldl (fun s c =>
      let cs := c.stats
      { s with bytes := s.bytes + cs.bytes, lines := s.lines + cs.lines, chars := s.chars + cs.chars })
      { bytes := 0, lines := 0, chars := 0, height := h }
    internal children stats

/-- Helper lemma for termination proofs -/
private theorem sizeOf_get_lt_internal (cs : Array PieceTree) (s : Stats) (i : Nat) (h : i < cs.size) :
    sizeOf (cs[i]) < sizeOf (internal cs s) := by
  cases cs with | mk data =>
  -- 1. Relate Array access to List access
  have eq : (Array.mk data)[i] = data.get ⟨i, h⟩ := rfl
  rw [eq]
  -- 2. Use standard List size property
  have lt_list : sizeOf (data.get ⟨i, h⟩) < sizeOf data :=
    List.sizeOf_lt_of_mem (List.get_mem data ⟨i, h⟩)
  -- 3. Prove data < internal cs s using simplification
  have lt_internal : sizeOf data < sizeOf (internal (Array.mk data) s) := by
    grind only [internal.sizeOf_spec, Array.mk.sizeOf_spec]
  -- 4. Transitivity
  apply Nat.lt_trans lt_list lt_internal

/-- Concatenate two trees -/
def concat (l : PieceTree) (r : PieceTree) : PieceTree :=
  match h : (l, r) with
  | (empty, _) => r
  | (_, empty) => l

  | (leaf ps1 _, leaf ps2 _) =>
    let ps := ps1 ++ ps2
    if ps.size <= NodeCapacity then
      mkLeaf ps
    else
      -- Split into two leaves
      let mid := ps.size / 2
      let l := mkLeaf (ps.extract 0 mid)
      let r := mkLeaf (ps.extract mid ps.size)
      mkInternal #[l, r]

    | (internal cs1 s1, internal cs2 s2) =>
    if l.height == r.height then
      let cs := cs1 ++ cs2
      if cs.size <= NodeCapacity then
        mkInternal cs
      else
        let mid := cs.size / 2
        let l := mkInternal (cs.extract 0 mid)
        let r := mkInternal (cs.extract mid cs.size)
        mkInternal #[l, r]
    else if l.height > r.height then
      -- Append r to the last child of l
      if h_empty : cs1.size = 0 then r
      else
        let lastIdx := cs1.size - 1
        have h_bound : lastIdx < cs1.size := Nat.pred_lt h_empty
        let lastChild := cs1[lastIdx]
        let newLast := concat lastChild r

        if newLast.height == lastChild.height then
          mkInternal (cs1.set! lastIdx newLast)
        else
          match newLast with
          | internal subChildren _ =>
               let newCs := cs1.pop ++ subChildren
               if newCs.size <= NodeCapacity then mkInternal newCs
               else
                  let mid := newCs.size / 2
                  mkInternal #[mkInternal (newCs.extract 0 mid), mkInternal (newCs.extract mid newCs.size)]
          | _ => mkInternal (cs1.push newLast)

    else -- l.height < r.height
      if h_empty : cs2.size = 0 then l
      else
        have h_bound : 0 < cs2.size := Nat.pos_of_ne_zero h_empty
        let firstChild := cs2[0]
        let newFirst := concat l firstChild

        if newFirst.height == firstChild.height then
          mkInternal (cs2.set! 0 newFirst)
        else
           match newFirst with
           | internal subChildren _ =>
               let newCs := subChildren ++ cs2.extract 1 cs2.size
               if newCs.size <= NodeCapacity then mkInternal newCs
               else
                  let mid := newCs.size / 2
                  mkInternal #[mkInternal (newCs.extract 0 mid), mkInternal (newCs.extract mid newCs.size)]
           | _ => mkInternal ((#[newFirst] ++ cs2))

  | (leaf ps1 s1, internal cs2 s2) =>
      if h_empty : cs2.size = 0 then l
      else
        have h_bound : 0 < cs2.size := Nat.pos_of_ne_zero h_empty
        let firstChild := cs2[0]
        let newFirst := concat l firstChild
        if newFirst.height == firstChild.height then
          mkInternal (cs2.set! 0 newFirst)
        else
           match newFirst with
           | internal subChildren _ =>
               let newCs := subChildren ++ cs2.extract 1 cs2.size
               if newCs.size <= NodeCapacity then mkInternal newCs
               else
                  let mid := newCs.size / 2
                  mkInternal #[mkInternal (newCs.extract 0 mid), mkInternal (newCs.extract mid newCs.size)]
           | _ => mkInternal ((#[newFirst] ++ cs2))

  | (internal cs1 s1, leaf ps2 s2) =>
      if h_empty : cs1.size = 0 then r
      else
        let lastIdx := cs1.size - 1
        have h_bound : lastIdx < cs1.size := Nat.pred_lt h_empty
        let lastChild := cs1[lastIdx]
        let newLast := concat lastChild r

        if newLast.height == lastChild.height then
          mkInternal (cs1.set! lastIdx newLast)
        else
          match newLast with
          | internal subChildren _ =>
              let newCs := cs1.pop ++ subChildren
              if newCs.size <= NodeCapacity then mkInternal newCs
              else
                 let mid := newCs.size / 2
                 mkInternal #[mkInternal (newCs.extract 0 mid), mkInternal (newCs.extract mid newCs.size)]
          | _ => mkInternal (cs1.push newLast)
termination_by sizeOf l + sizeOf r
decreasing_by
  simp_wf
  -- Case 1: l.height > r.height
  · have hl : l = internal cs1 s1 := congrArg Prod.fst h
    rw [hl]
    try apply Nat.add_lt_add_right
    apply sizeOf_get_lt_internal _ _ _ (by assumption)
  -- Case 2: l.height < r.height
  · have hr : r = internal cs2 s2 := congrArg Prod.snd h
    rw [hr]
    try apply Nat.add_lt_add_left
    apply sizeOf_get_lt_internal _ _ _ (by assumption)
  -- Case 3: l is leaf, r is internal
  · have hr : r = internal cs2 s2 := congrArg Prod.snd h
    rw [hr]
    try apply Nat.add_lt_add_left
    apply sizeOf_get_lt_internal _ _ _ (by assumption)
  -- Case 4: l is internal, r is leaf
  · have hl : l = internal cs1 s1 := congrArg Prod.fst h
    rw [hl]
    try apply Nat.add_lt_add_right
    apply sizeOf_get_lt_internal _ _ _ (by assumption)



/-- Split a leaf node at a specific piece index and internal offset -/
def splitLeaf (pieces : Array Piece) (stats : Stats) (pt : PieceTable) (offset : Nat) : (PieceTree × PieceTree) :=
  let rec findPiece (i : Nat) (currentOff : Nat) : (Nat × Nat) :=
    if i >= pieces.size then (pieces.size, currentOff)
    else
      let p := pieces[i]!
      if currentOff + p.length > offset then (i, currentOff)
      else findPiece (i + 1) (currentOff + p.length)

  let (idx, pStart) := findPiece 0 0

  if idx >= pieces.size then
    (leaf pieces stats, empty)
  else
    let p := pieces[idx]!
    let splitOff := offset - pStart

    if splitOff == 0 then
      let leftArr := pieces.extract 0 idx
      let rightArr := pieces.extract idx pieces.size
      (mkLeaf leftArr, mkLeaf rightArr)
    else if splitOff == p.length then
      let leftArr := pieces.extract 0 (idx + 1)
      let rightArr := pieces.extract (idx + 1) pieces.size
      (mkLeaf leftArr, mkLeaf rightArr)
    else
      let (p1, p2) := PieceTableHelper.splitPiece pt p splitOff
      let leftPieces := (pieces.extract 0 idx).push p1
      let rightPieces := (#[p2]).append (pieces.extract (idx + 1) pieces.size)
      (mkLeaf leftPieces, mkLeaf rightPieces)


mutual
  /-- Split the tree at a given character offset. -/
  def split (t : PieceTree) (offset : Nat) (pt : PieceTable) : (PieceTree × PieceTree) :=
    match t with
    | empty => (empty, empty)
    | leaf pieces s => splitLeaf pieces s pt offset
    | internal children curStats =>
      if offset == 0 then (empty, t)
      else if offset >= curStats.bytes then (t, empty)
      else
        splitAux children offset pt 0 0
  termination_by (sizeOf t, 0)
  decreasing_by
    simp_wf
    -- split -> splitAux
    apply Prod.Lex.left
    simp +arith

  /-- Aux helper for internal node split to scan children -/
  def splitAux (children : Array PieceTree) (offset : Nat) (pt : PieceTable) (i : Nat) (accOff : Nat) : (PieceTree × PieceTree) :=
    if h : i < children.size then
      let c := children[i]
      if accOff + c.length > offset then
        let (cLeft, cRight) := split c (offset - accOff) pt

        let leftChildren := (children.extract 0 i).push cLeft
        let rightChildren := (#[cRight]).append (children.extract (i + 1) children.size)

        let leftFiltered := leftChildren.filter (fun c => c.length > 0)
        let rightFiltered := rightChildren.filter (fun c => c.length > 0)

        (mkInternal leftFiltered, mkInternal rightFiltered)
      else
        splitAux children offset pt (i + 1) (accOff + c.length)
    else
      (mkInternal children, empty)
  termination_by (sizeOf children, children.size - i)
  decreasing_by
    all_goals simp_wf
    -- splitAux -> split (c)
    · apply Prod.Lex.left
      cases children with | mk data =>
      have lt_list : sizeOf (data.get ⟨i, h⟩) < sizeOf data :=
        List.sizeOf_lt_of_mem (List.get_mem data ⟨i, h⟩)
      have lt_array : sizeOf data < sizeOf (Array.mk data) := by
        grind only [Array.mk.sizeOf_spec]
      exact Nat.lt_trans lt_list lt_array

    -- splitAux -> splitAux (i+1)
    · apply Prod.Lex.right
      apply Nat.sub_lt_sub_left
      · exact h
      · exact Nat.lt_succ_self _
end

/-- Delete range [offset, offset + length) -/
def delete (t : PieceTree) (offset : Nat) (length : Nat) (pt : PieceTable) : PieceTree :=
  if length == 0 then t
  else
    let (l, r) := split t offset pt
    let (_, r') := split r length pt
    concat l r'

/-- Helper to scan pieces in a leaf for Nth newline -/
def findNthNewlineLeaf (pieces : Array Piece) (n : Nat) (pt : PieceTable) (i : Nat) (accOffset : Nat) : Nat :=
  if h : i < pieces.size then
    let p := pieces[i]
    if n < p.lineBreaks then
      let buf := PieceTableHelper.getBuffer pt p.source
      let rec scan (j : Nat) (cnt : Nat) : Nat :=
        if j >= p.length then j
        else
          if buf[p.start + j]! == 10 then
            if cnt == n then j
            else scan (j + 1) (cnt + 1)
          else scan (j + 1) cnt
      accOffset + (scan 0 0)
    else
      findNthNewlineLeaf pieces (n - p.lineBreaks) pt (i + 1) (accOffset + p.length)
  else
    accOffset
termination_by pieces.size - i

mutual
  /-- Find offset of the N-th newline (0-indexed). -/
  def findNthNewline (t : PieceTree) (n : Nat) (pt : PieceTable) : Nat :=
    match t with
    | empty => 0
    | leaf pieces _ => findNthNewlineLeaf pieces n pt 0 0
    | internal children _ => findNthNewlineAux children n pt 0 0
  termination_by (sizeOf t, 0)
  decreasing_by
    simp_wf
    -- findNthNewline -> findNthNewlineAux
    apply Prod.Lex.left
    simp +arith

  def findNthNewlineAux (children : Array PieceTree) (n : Nat) (pt : PieceTable) (i : Nat) (accOffset : Nat) : Nat :=
    if h : i < children.size then
      let child := children[i]
      let childLines := child.lineBreaks
      if n < childLines then
        accOffset + findNthNewline child n pt
      else
        findNthNewlineAux children (n - childLines) pt (i + 1) (accOffset + child.length)
    else
      accOffset
  termination_by (sizeOf children, children.size - i)
  decreasing_by
    all_goals simp_wf
    -- findNthNewlineAux -> findNthNewline
    · apply Prod.Lex.left
      cases children with | mk data =>
      have eq : (Array.mk data)[i] = data.get ⟨i, h⟩ := rfl
      rw [eq]
      have lt_list : sizeOf (data.get ⟨i, h⟩) < sizeOf data :=
        List.sizeOf_lt_of_mem (List.get_mem data ⟨i, h⟩)
      have lt_array : sizeOf data < sizeOf (Array.mk data) := by
        grind only [Array.mk.sizeOf_spec]
      exact Nat.lt_trans lt_list lt_array
    -- findNthNewlineAux -> findNthNewlineAux
    · apply Prod.Lex.right
      apply Nat.sub_lt_sub_left
      · exact h
      · exact Nat.lt_succ_self _
end


/-- Get substring of tree from start to end offset -/
partial def getSubstring (t : PieceTree) (startOff endOff : Nat) (pt : PieceTable) : String :=
  if startOff >= endOff then ""
  else
    let rec traverse (t : PieceTree) (currentOff : Nat) : String :=
      let tLen := t.length
      if currentOff + tLen <= startOff || currentOff >= endOff then ""
      else
        match t with
        | empty => ""
        | leaf pieces _ =>
           let rec scan (i : Nat) (off : Nat) (acc : String) : String :=
             if i >= pieces.size then acc
             else
               let p := pieces[i]!
               let pStart := off
               let pEnd := off + p.length
               let readStart := max startOff pStart
               let readEnd := min endOff pEnd

               if readStart < readEnd then
                 let buf := PieceTableHelper.getBuffer pt p.source
                 let sliceStart := p.start + (readStart - pStart)
                 let sliceEnd := p.start + (readEnd - pStart)
                 let str := String.fromUTF8! (buf.extract sliceStart sliceEnd)
                 scan (i + 1) pEnd (acc ++ str)
               else
                 scan (i + 1) pEnd acc
           scan 0 currentOff ""
        | internal children _ =>
           let rec scanInternal (i : Nat) (off : Nat) (acc : String) : String :=
             if i >= children.size then acc
             else
               let c := children[i]!
               let s := traverse c off
               scanInternal (i + 1) (off + c.length) (acc ++ s)
           scanInternal 0 currentOff ""
    traverse t 0

/-- Get total string length of a range (counting chars, not bytes, without allocation) -/
partial def countCharsInRange (t : PieceTree) (startOff endOff : Nat) (pt : PieceTable) : Nat :=
  if startOff >= endOff then 0
  else
    let rec traverse (t : PieceTree) (currentOff : Nat) : Nat :=
      let tLen := t.length
      if currentOff + tLen <= startOff || currentOff >= endOff then 0
      else if currentOff >= startOff && currentOff + tLen <= endOff then
        t.stats.chars
      else
        match t with
        | empty => 0
        | leaf pieces _ =>
           let rec scan (i : Nat) (off : Nat) (acc : Nat) : Nat :=
             if i >= pieces.size then acc
             else
               let p := pieces[i]!
               let pStart := off
               let pEnd := off + p.length
               if pEnd <= startOff || pStart >= endOff then
                 scan (i + 1) pEnd acc
               else if pStart >= startOff && pEnd <= endOff then
                 scan (i + 1) pEnd (acc + p.charCount)
               else
                 let readStart := max startOff pStart
                 let readEnd := min endOff pEnd
                 let buf := PieceTableHelper.getBuffer pt p.source
                 let sliceStart := p.start + (readStart - pStart)
                 let sliceLen := readEnd - readStart
                 let cnt := ViE.Unicode.countChars buf sliceStart sliceLen
                 scan (i + 1) pEnd (acc + cnt)
           scan 0 currentOff 0
        | internal children _ =>
           let rec scanInternal (i : Nat) (off : Nat) (acc : Nat) : Nat :=
             if i >= children.size then acc
             else
               let c := children[i]!
               let s := traverse c off
               scanInternal (i + 1) (off + c.length) (acc + s)
           scanInternal 0 currentOff 0
    traverse t 0

/-- Get line char length (0-indexed). Excludes newline at end of line. -/
def getLineLength (t : PieceTree) (lineIdx : Nat) (pt : PieceTable) : Option Nat :=
  let totalLines := t.lineBreaks
  if lineIdx > totalLines then none
  else
    let startOffset := if lineIdx == 0 then 0 else findNthNewline t (lineIdx - 1) pt + 1
    let endOffset :=
      if lineIdx == totalLines then
        t.length
      else
        findNthNewline t lineIdx pt
    some (countCharsInRange t startOffset endOffset pt)

def getLine (t : PieceTree) (lineIdx : Nat) (pt : PieceTable) : Option String :=
  let totalLines := t.lineBreaks
  if lineIdx > totalLines then none
  else
    let startOffset := if lineIdx == 0 then 0 else findNthNewline t (lineIdx - 1) pt + 1
    let endOffset :=
      if lineIdx == totalLines then
        t.length
      else
        findNthNewline t lineIdx pt
    some (getSubstring t startOffset endOffset pt)

/-- Get line range (start, length) -/
def getLineRange (t : PieceTree) (lineIdx : Nat) (pt : PieceTable) : Option (Nat × Nat) :=
  let totalLines := t.lineBreaks
  if lineIdx > totalLines then none
  else
    let startOffset := if lineIdx == 0 then 0 else findNthNewline t (lineIdx - 1) pt + 1
    let endOffset :=
      if lineIdx == totalLines then
        t.length
      else
        findNthNewline t lineIdx pt
    some (startOffset, endOffset - startOffset)

/-- Build a tree from a list of pieces (Bottom-Up construction) -/
partial def fromPieces (pieces : Array Piece) : PieceTree :=
  if pieces.isEmpty then empty
  else
    -- Step 1: Create Leaves
    let rec mkLeaves (i : Nat) (acc : Array PieceTree) : Array PieceTree :=
      if i >= pieces.size then acc
      else
        let chunk := pieces.extract i (i + NodeCapacity)
        let leaf := mkLeaf chunk
        mkLeaves (i + NodeCapacity) (acc.push leaf)

    let leaves := mkLeaves 0 #[]

    -- Step 2: Build Internal Nodes recursively
    let rec buildLevel (nodes : Array PieceTree) : PieceTree :=
      if nodes.size == 1 then
        nodes[0]!
      else
        let rec mkNextLevel (i : Nat) (acc : Array PieceTree) : Array PieceTree :=
          if i >= nodes.size then acc
          else
            let chunk := nodes.extract i (i + NodeCapacity)
            let node := mkInternal chunk
            mkNextLevel (i + NodeCapacity) (acc.push node)

        buildLevel (mkNextLevel 0 #[])

    buildLevel leaves

end PieceTree

end ViE.PieceTable
