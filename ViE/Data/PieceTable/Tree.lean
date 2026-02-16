import Lean
import ViE.Data.PieceTable.Piece
import ViE.Unicode

namespace ViE

namespace PieceTableHelper

structure AppendMeta where
  bufferIdx : Nat
  bufferEnd : Nat

/-- Get the buffer data corresponding to a source -/
def getBuffer (pt : ViE.PieceTable) (source : ViE.BufferSource) : ByteArray :=
  match source with
  | ViE.BufferSource.original => pt.original
  | ViE.BufferSource.add idx => pt.addBuffers.getD idx (ByteArray.mk #[])

/-- Append text to add buffer, splitting into chunks if necessary. Reuses tail add buffer when possible. -/
def appendText (pt : ViE.PieceTable) (text : String) : (ViE.PieceTable × Array ViE.Piece × AppendMeta) :=
  let bytes := text.toUTF8
  let totalSize := bytes.size
  let (bufferIdx, startOff, newAddBuffers) :=
    match pt.addBuffers.back? with
    | some tail =>
        if tail.size + totalSize <= ViE.AddBufferReuseLimit then
          let idx := pt.addBuffers.size - 1
          let startOff := tail.size
          let merged := tail ++ bytes
          let bufs := pt.addBuffers.set! idx merged
          (idx, startOff, bufs)
        else
          let idx := pt.addBuffers.size
          (idx, 0, pt.addBuffers.push bytes)
    | none =>
        (0, 0, #[bytes])

  let rec splitChunks (start : Nat) (acc : Array ViE.Piece) : Array ViE.Piece :=
    if start >= totalSize then acc
    else
      let len := min ViE.ChunkSize (totalSize - start)
      let (lines, chars) := ViE.Unicode.countNewlinesAndChars bytes start len
      let piece : ViE.Piece := {
        source := ViE.BufferSource.add bufferIdx,
        start := (startOff + start).toUInt64,
        length := len.toUInt64,
        lineBreaks := lines.toUInt64,
        charCount := chars.toUInt64
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
  ({ pt with addBuffers := newAddBuffers }, ps, { bufferIdx := bufferIdx, bufferEnd := startOff + totalSize })

/-- Split a piece into two at a given relative offset -/
def splitPiece (p : ViE.Piece) (offset : UInt64) (pt : ViE.PieceTable) : (ViE.Piece × ViE.Piece) :=
  let buf := getBuffer pt p.source
  let leftLen := offset
  let rightLen := p.length - offset

  let (leftLines, leftChars) := ViE.Unicode.countNewlinesAndChars buf p.start.toNat leftLen.toNat

  let leftPiece : ViE.Piece := { p with length := leftLen, lineBreaks := leftLines.toUInt64, charCount := leftChars.toUInt64 }
  let rightPiece : ViE.Piece := { p with
    start := p.start + leftLen
    length := rightLen,
    lineBreaks := p.lineBreaks - leftLines.toUInt64,
    charCount := p.charCount - leftChars.toUInt64
  }
  (leftPiece, rightPiece)

end PieceTableHelper

namespace PieceTree

/-- Get stats of a tree -/
def stats (t : ViE.PieceTree) : ViE.Stats :=
  match t with
  | ViE.PieceTree.empty => ViE.Stats.empty
  | ViE.PieceTree.leaf _ s _ => s
  | ViE.PieceTree.internal _ s _ _ => s

def length (t : ViE.PieceTree) : Nat := (stats t).bytes.toNat
def lineBreaks (t : ViE.PieceTree) : Nat := (stats t).lines.toNat
def height (t : ViE.PieceTree) : Nat := (stats t).height.toNat

def searchMetaOf (t : ViE.PieceTree) : ViE.SearchBloom :=
  match t with
  | ViE.PieceTree.empty => ViE.SearchBloom.empty
  | ViE.PieceTree.leaf _ _ m => m
  | ViE.PieceTree.internal _ _ m _ => m

/-- Compute cumulative offsets from children stats for O(log n) lookup -/
def computeCumulativeOffsets (children : Array ViE.PieceTree) : ViE.InternalMeta :=
  Id.run do
    let mut cumBytes : Array UInt64 := #[0]
    let mut cumLines : Array UInt64 := #[0]
    let mut cumChars : Array UInt64 := #[0]

    for i in [0:children.size] do
      let child := children[i]!
      let s := stats child

      let prevBytes := cumBytes.back!
      let prevLines := cumLines.back!
      let prevChars := cumChars.back!

      cumBytes := cumBytes.push (prevBytes + s.bytes)
      cumLines := cumLines.push (prevLines + s.lines)
      cumChars := cumChars.push (prevChars + s.chars)

    return {
      cumulativeBytes := cumBytes,
      cumulativeLines := cumLines,
      cumulativeChars := cumChars
    }

/-- Binary search to find child index containing the given byte offset -/
def findChildForOffset (imeta : ViE.InternalMeta) (offset : UInt64) : Nat :=
  Id.run do
    let arr := imeta.cumulativeBytes
    if arr.isEmpty then return 0
    if arr.size == 1 then return 0

    let mut left := 0
    let mut right := arr.size - 2  -- Last valid child index

    while left < right do
      let mid := (left + right + 1) / 2
      if arr[mid]! <= offset then
        left := mid
      else
        right := mid - 1

    return left

/-- Binary search to find child index containing the given line number -/
def findChildForLine (imeta : ViE.InternalMeta) (lineIdx : UInt64) : Nat :=
  Id.run do
    let arr := imeta.cumulativeLines
    if arr.isEmpty then return 0
    if arr.size == 1 then return 0

    let mut left := 0
    let mut right := arr.size - 2  -- Last valid child index

    while left < right do
      let mid := (left + right + 1) / 2
      if arr[mid]! <= lineIdx then
        left := mid
      else
        right := mid - 1

    return left

def bloomOr (a b : ByteArray) : ByteArray := Id.run do
  let mut out := a
  let size := min a.size b.size
  for i in [0:size] do
    out := out.set! i (out[i]! ||| b[i]!)
  out

def bloomSetBit (bloom : ByteArray) (idx : Nat) : ByteArray :=
  let byteIdx := idx / 8
  let bitIdx := idx % 8
  if byteIdx < bloom.size then
    let cur := bloom[byteIdx]!
    let mask : UInt8 := (1 : UInt8) <<< bitIdx.toUInt8
    bloom.set! byteIdx (cur ||| mask)
  else
    bloom

def bloomGetBit (bloom : ByteArray) (idx : Nat) : Bool :=
  let byteIdx := idx / 8
  let bitIdx := idx % 8
  if byteIdx < bloom.size then
    let cur := bloom[byteIdx]!
    let mask : UInt8 := (1 : UInt8) <<< bitIdx.toUInt8
    (cur &&& mask) != 0
  else
    false

/-- Polynomial rolling hash with base 31: b0·31² + b1·31¹ + b2·31⁰.
    Used as the first hash function for Bloom filter double-hashing. -/
def hash1 (b0 b1 b2 : UInt8) : Nat :=
  (b0.toNat * 961 + b1.toNat * 31 + b2.toNat) % ViE.BloomBits

/-- Polynomial rolling hash with base 131: b0·131² + b1·131¹ + b2·131⁰.
    Used as the second hash function for Bloom filter double-hashing. -/
def hash2 (b0 b1 b2 : UInt8) : Nat :=
  (b0.toNat * 17161 + b1.toNat * 131 + b2.toNat) % ViE.BloomBits

/-- Add a trigram to the Bloom filter. -/
def addTrigramToBloom (bloom : ByteArray) (b0 b1 b2 : UInt8) : ByteArray :=
  let h1 := hash1 b0 b1 b2
  let h2 := hash2 b0 b1 b2
  bloomSetBit (bloomSetBit bloom h1) h2

def addTrigramsFromArray (bloom : ByteArray) (arr : Array UInt8) : ByteArray := Id.run do
  if arr.size < 3 then
    return bloom
  let limit := arr.size - 2
  let mut out := bloom
  for i in [0:limit] do
    out := addTrigramToBloom out arr[i]! arr[i + 1]! arr[i + 2]!
  return out

def takeFirstBytes (arr : Array UInt8) (n : Nat) : Array UInt8 :=
  if arr.size <= n then arr else arr.extract 0 n

def takeLastBytes (arr : Array UInt8) (n : Nat) : Array UInt8 :=
  if arr.size <= n then arr else arr.extract (arr.size - n) arr.size

def buildPrefixBytes (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : Array UInt8 := Id.run do
  let mut i := 0
  let mut acc : Array UInt8 := #[]
  while i < pieces.size && acc.size < 2 do
    let p := pieces[i]!
    let buf := PieceTableHelper.getBuffer pt p.source
    let slice := buf.extract p.start.toNat (p.start.toNat + p.length.toNat)
    if slice.size > 0 then
      let need := 2 - acc.size
      let take := takeFirstBytes slice.data need
      acc := acc ++ take
    i := i + 1
  return acc

def buildSuffixBytes (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : Array UInt8 := Id.run do
  let mut i := pieces.size
  let mut acc : Array UInt8 := #[]
  while i > 0 && acc.size < 2 do
    let idx := i - 1
    let p := pieces[idx]!
    let buf := PieceTableHelper.getBuffer pt p.source
    let slice := buf.extract p.start.toNat (p.start.toNat + p.length.toNat)
    if slice.size > 0 then
      let need := 2 - acc.size
      let take := takeLastBytes slice.data need
      acc := take ++ acc
    i := idx
  return acc

def addBytesToBloom (bloom : ByteArray) (carry : Array UInt8) (bytes : ByteArray) : (ByteArray × Array UInt8) :=
  let arr := carry ++ bytes.data
  let bloom' := addTrigramsFromArray bloom arr
  let carry' := takeLastBytes arr 2
  (bloom', carry')

def addBoundaryTrigrams (bloom : ByteArray) (leftSuffix rightPrefix : Array UInt8) : ByteArray :=
  let combined := leftSuffix ++ rightPrefix
  addTrigramsFromArray bloom combined

def buildBloomForPieces (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : ViE.SearchBloom := Id.run do
  if !pt.bloomBuildLeafBits then
    let prefixBytes := buildPrefixBytes pieces pt
    let suffixBytes := buildSuffixBytes pieces pt
    return { bits := ViE.SearchBloom.empty.bits, prefixBytes := prefixBytes, suffixBytes := suffixBytes, hasBits := false }
  else
    let mut bits := ViE.SearchBloom.empty.bits
    let mut carry : Array UInt8 := #[]
    let mut prefixBytes : Array UInt8 := #[]
    for p in pieces do
      let buf := PieceTableHelper.getBuffer pt p.source
      let slice := buf.extract p.start.toNat (p.start.toNat + p.length.toNat)
      if prefixBytes.size < 2 && slice.size > 0 then
        let need := 2 - prefixBytes.size
        let arr := slice.data
        let take := takeFirstBytes arr need
        prefixBytes := prefixBytes ++ take
      let (bits', carry') := addBytesToBloom bits carry slice
      bits := bits'
      carry := carry'
    return { bits := bits, prefixBytes := prefixBytes, suffixBytes := carry, hasBits := true }

def bloomIsEmpty (bloom : ByteArray) : Bool :=
  bloom.data.all (fun b => b == 0)

def combineBloom (left right : ViE.SearchBloom) : ViE.SearchBloom :=
  let pref :=
    if left.prefixBytes.size >= 2 then left.prefixBytes
    else takeFirstBytes (left.prefixBytes ++ right.prefixBytes) 2
  let suf :=
    if right.suffixBytes.size >= 2 then right.suffixBytes
    else takeLastBytes (left.suffixBytes ++ right.suffixBytes) 2
  -- If any child bloom is empty (unknown), keep bits empty to avoid false negatives.
  if !left.hasBits || !right.hasBits then
    { bits := ViE.SearchBloom.empty.bits, prefixBytes := pref, suffixBytes := suf, hasBits := false }
  else
    let bits := bloomOr left.bits right.bits
    let bits := addBoundaryTrigrams bits left.suffixBytes right.prefixBytes
    { bits := bits, prefixBytes := pref, suffixBytes := suf, hasBits := true }

def buildBloomForChildren (children : Array ViE.PieceTree) : ViE.SearchBloom := Id.run do
  if children.isEmpty then
    return ViE.SearchBloom.empty
  let mut acc := searchMetaOf children[0]!
  for i in [1:children.size] do
    acc := combineBloom acc (searchMetaOf children[i]!)
  return acc

def patternTrigramHashes (pattern : ByteArray) : Array (Nat × Nat) := Id.run do
  if pattern.size < 3 then
    return #[]
  let arr := pattern.data
  let limit := pattern.size - 2
  let mut hashes : Array (Nat × Nat) := #[]
  for i in [0:limit] do
    let b0 := arr[i]!
    let b1 := arr[i + 1]!
    let b2 := arr[i + 2]!
    hashes := hashes.push (hash1 b0 b1 b2, hash2 b0 b1 b2)
  return hashes

def bloomMayContain (searchMeta : ViE.SearchBloom) (hashes : Array (Nat × Nat)) : Bool :=
  if hashes.isEmpty then
    true
  else if !searchMeta.hasBits then
    -- Empty bloom means "unknown", do not prune.
    true
  else
    hashes.all (fun (h1, h2) => bloomGetBit searchMeta.bits h1 && bloomGetBit searchMeta.bits h2)

def cacheInsert (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (maxSize : Nat) (key : Nat) (value : ByteArray)
  : (Lean.RBMap Nat ByteArray compare × Array Nat) :=
  let cache := cache.insert key value
  let order := if order.contains key then order else order.push key
  if order.size > maxSize then
    let dropCount := order.size - maxSize
    let evicted := order.extract 0 dropCount
    let order := order.extract dropCount order.size
    let cache := evicted.foldl (fun acc k => acc.erase k) cache
    (cache, order)
  else
    (cache, order)

def leafBloomBitsWithCache (pieces : Array ViE.Piece) (pt : ViE.PieceTable) (leafOffset : Nat)
  (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (maxSize : Nat)
  : (ByteArray × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  match cache.find? leafOffset with
  | some bits => (bits, cache, order)
  | none =>
      let bits := (buildBloomForPieces pieces pt).bits
      let (cache', order') := cacheInsert cache order maxSize leafOffset bits
      (bits, cache', order')

/-- Create a leaf node -/
def mkLeaf (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : ViE.PieceTree :=
  if pieces.size == 0 then
    ViE.PieceTree.empty
  else
    let s := pieces.foldl (fun acc p => acc + (ViE.Stats.ofPiece p)) ViE.Stats.empty
    let searchMeta := buildBloomForPieces pieces pt
    ViE.PieceTree.leaf pieces s searchMeta

/-- Create an internal node -/
def mkInternal (children : Array ViE.PieceTree) : ViE.PieceTree :=
  let validChildren := children.filter (fun c => match c with | ViE.PieceTree.empty => false | _ => true)
  if validChildren.size == 0 then
    ViE.PieceTree.empty
  else
    let s := validChildren.foldl (fun acc c => acc + (stats c)) ViE.Stats.empty
    let s := { s with height := s.height + 1 }
    let searchMeta := buildBloomForChildren validChildren
    let internalMeta := computeCumulativeOffsets validChildren
    ViE.PieceTree.internal validChildren s searchMeta internalMeta

/-- Efficiently concatenate a list of pieces into a tree -/
def fromPieces (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : ViE.PieceTree :=
  if pieces.isEmpty then
    ViE.PieceTree.empty
  else
    Id.run do
      let mut leaves : Array ViE.PieceTree := #[]
      let mut i := 0
      while i < pieces.size do
        let j := min (i + ViE.NodeCapacity) pieces.size
        leaves := leaves.push (mkLeaf (pieces.extract i j) pt)
        i := j
      let mut level := leaves
      while level.size > 1 do
        let mut parents : Array ViE.PieceTree := #[]
        let mut k := 0
        while k < level.size do
          let j := min (k + ViE.NodeCapacity) level.size
          parents := parents.push (mkInternal (level.extract k j))
          k := j
        level := parents
      return level[0]!

/-- Flatten a tree into pieces in document order (iterative to avoid deep recursion). -/
def toPieces (t : ViE.PieceTree) : Array ViE.Piece := Id.run do
  let mut out : Array ViE.Piece := #[]
  let mut stack : List ViE.PieceTree := [t]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | node :: rest =>
        stack := rest
        match node with
        | ViE.PieceTree.empty => pure ()
        | ViE.PieceTree.leaf pieces _ _ =>
            out := out ++ pieces
        | ViE.PieceTree.internal children _ _ _ =>
            let mut i := children.size
            while i > 0 do
              let j := i - 1
              stack := children[j]! :: stack
              i := j
  return out

/-- Insert `node` into the right spine of `tree` at the level matching `targetHeight`.
    Returns the merged tree, handling overflow splits. -/
private def insertRight (tree : ViE.PieceTree) (node : ViE.PieceTree) (targetHeight : Nat) : ViE.PieceTree :=
  Id.run do
    -- Collect spine frames going right
    let mut frames : Array (Array ViE.PieceTree) := #[]  -- left siblings at each level
    let mut cur := tree
    while height cur > targetHeight do
      match cur with
      | ViE.PieceTree.internal children _ _ _ =>
          -- Save all children except the rightmost as left siblings
          frames := frames.push (children.extract 0 (children.size - 1))
          cur := children.back!
      | _ => break  -- shouldn't happen if height > targetHeight
    -- cur and node are both at targetHeight; propagate them upward as new children
    let mut newChildren : Array ViE.PieceTree := #[cur, node]
    -- Walk back up, rebuilding from frames
    let mut fi := frames.size
    while fi > 0 do
      let j := fi - 1
      let siblings := frames[j]!
      let combined := siblings ++ newChildren
      if combined.size <= ViE.NodeCapacity then
        newChildren := #[mkInternal combined]
      else
        -- Split: too many children
        let mid := combined.size / 2
        let leftNode := mkInternal (combined.extract 0 mid)
        let rightNode := mkInternal (combined.extract mid combined.size)
        newChildren := #[leftNode, rightNode]
      fi := j
    if newChildren.size == 1 then
      return newChildren[0]!
    else
      return mkInternal newChildren

/-- Insert `node` into the left spine of `tree` at the level matching `targetHeight`.
    Returns the merged tree, handling overflow splits. -/
private def insertLeft (node : ViE.PieceTree) (tree : ViE.PieceTree) (targetHeight : Nat) : ViE.PieceTree :=
  Id.run do
    -- Collect spine frames going left
    let mut frames : Array (Array ViE.PieceTree) := #[]  -- right siblings at each level
    let mut cur := tree
    while height cur > targetHeight do
      match cur with
      | ViE.PieceTree.internal children _ _ _ =>
          -- Save all children except the leftmost as right siblings
          frames := frames.push (children.extract 1 children.size)
          cur := children[0]!
      | _ => break
    -- cur and node are both at targetHeight; propagate them upward as new children
    let mut newChildren : Array ViE.PieceTree := #[node, cur]
    -- Walk back up, rebuilding from frames
    let mut fi := frames.size
    while fi > 0 do
      let j := fi - 1
      let siblings := frames[j]!
      let combined := newChildren ++ siblings
      if combined.size <= ViE.NodeCapacity then
        newChildren := #[mkInternal combined]
      else
        let mid := combined.size / 2
        let leftNode := mkInternal (combined.extract 0 mid)
        let rightNode := mkInternal (combined.extract mid combined.size)
        newChildren := #[leftNode, rightNode]
      fi := j
    if newChildren.size == 1 then
      return newChildren[0]!
    else
      return mkInternal newChildren

/-- Concatenate two trees while maintaining B+ tree invariants.
    O(log n) structural merge: walks the spine of the taller tree to find a node
    at matching height, then inserts and propagates any overflows (splits) upward. -/
private def concatCore (l : ViE.PieceTree) (r : ViE.PieceTree) (pt : ViE.PieceTable) : ViE.PieceTree :=
  match l, r with
  | ViE.PieceTree.empty, _ => r
  | _, ViE.PieceTree.empty => l
  | ViE.PieceTree.leaf ps1 _ _, ViE.PieceTree.leaf ps2 _ _ =>
      -- Fast path for adjacent leaves; preserve piece merging behavior.
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
            mkLeaf ps pt
          else
            let mid := ps.size / 2
            mkInternal #[mkLeaf (ps.extract 0 mid) pt, mkLeaf (ps.extract mid ps.size) pt]
        else
          let ps := ps1 ++ ps2
          if ps.size <= ViE.NodeCapacity then mkLeaf ps pt
          else mkInternal #[mkLeaf ps1 pt, mkLeaf ps2 pt]
      else if ps1.size > 0 then
        l
      else
        r
  | _, _ =>
      let lh := height l
      let rh := height r
      if lh == rh then
        -- Same height: merge children to avoid unnecessary height increase
        match l, r with
        | ViE.PieceTree.internal cl _ _ _, ViE.PieceTree.internal cr _ _ _ =>
            let combined := cl ++ cr
            if combined.size <= ViE.NodeCapacity then
              mkInternal combined
            else
              let mid := combined.size / 2
              mkInternal #[mkInternal (combined.extract 0 mid), mkInternal (combined.extract mid combined.size)]
        | _, _ =>
            -- leaf + internal at same height (shouldn't normally happen), safe fallback
            insertRight l r rh
      else if lh > rh then
        -- l is taller: walk down l's right spine to find insertion point for r
        insertRight l r rh
      else
        -- r is taller: walk down r's left spine to find insertion point for l
        insertLeft l r lh

def concat (l : ViE.PieceTree) (r : ViE.PieceTree) (pt : ViE.PieceTable) : ViE.PieceTree :=
  concatCore l r pt

/-- Split the tree at a given byte offset. -/
private def splitCore (t : ViE.PieceTree) (offset : Nat) (pt : ViE.PieceTable) : (ViE.PieceTree × ViE.PieceTree) :=
  Id.run do
    if offset == 0 then
      return (ViE.PieceTree.empty, t)

    let mut node := t
    let mut off : UInt64 := offset.toUInt64
    let mut frames : Array (Array ViE.PieceTree × Array ViE.PieceTree) := #[]

    while true do
      match node with
      | ViE.PieceTree.empty =>
          return (ViE.PieceTree.empty, ViE.PieceTree.empty)
      | ViE.PieceTree.leaf pieces _ _ =>
          let mut i := 0
          let mut accOffset : UInt64 := 0
          let mut leftTree := node
          let mut rightTree := ViE.PieceTree.empty
          let mut found := false
          while i < pieces.size && !found do
            let p := pieces[i]!
            if off < accOffset + p.length then
              let relOffset := off - accOffset
              if relOffset == 0 then
                leftTree := mkLeaf (pieces.extract 0 i) pt
                rightTree := mkLeaf (pieces.extract i pieces.size) pt
              else
                let (p1, p2) := PieceTableHelper.splitPiece p relOffset pt
                leftTree := mkLeaf ((pieces.extract 0 i).push p1) pt
                rightTree := mkLeaf (#[p2] ++ (pieces.extract (i + 1) pieces.size)) pt
              found := true
            else
              accOffset := accOffset + p.length
              i := i + 1
          if !found then
            leftTree := node
            rightTree := ViE.PieceTree.empty

          let mut l := leftTree
          let mut r := rightTree
          let mut fi := frames.size
          while fi > 0 do
            let j := fi - 1
            let (leftSibs, rightSibs) := frames[j]!
            l := mkInternal (leftSibs.push l)
            r := mkInternal (#[r] ++ rightSibs)
            fi := j
          return (l, r)
      | ViE.PieceTree.internal children _ _ imeta =>
          -- Use binary search to find the child containing the offset
          let childIdx := findChildForOffset imeta off
          let child := children[childIdx]!
          let childStart := imeta.cumulativeBytes[childIdx]!
          let relativeOffset := off - childStart

          frames := frames.push (children.extract 0 childIdx, children.extract (childIdx + 1) children.size)
          node := child
          off := relativeOffset
          -- Continue to next iteration
    return (t, ViE.PieceTree.empty)

def split (t : ViE.PieceTree) (offset : Nat) (pt : ViE.PieceTable) : (ViE.PieceTree × ViE.PieceTree) :=
  splitCore t offset pt

/-- Delete range from tree -/
def delete (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ViE.PieceTree :=
  let (l, mid_r) := split t offset pt
  let (_, r) := split mid_r len pt
  concat l r pt

/-- Get bytes from tree. -/
private def getBytesCore (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ByteArray :=
  if len == 0 then
    ByteArray.mk #[]
  else
    let endOffset := offset + len
    Id.run do
      let mut out : ByteArray := ByteArray.mk (Array.mkEmpty len)
      let mut stack : List (ViE.PieceTree × Nat) := [(t, 0)]
      let mut cursor := offset
      let mut remain := len
      while remain > 0 && !stack.isEmpty do
        match stack with
        | [] => pure ()
        | (node, baseOffset) :: rest =>
            stack := rest
            let nodeLen := length node
            let nodeEnd := baseOffset + nodeLen
            if nodeEnd <= cursor || baseOffset >= endOffset then
              pure ()
            else
              match node with
              | ViE.PieceTree.empty => pure ()
              | ViE.PieceTree.leaf pieces _ _ =>
                  let mut i := 0
                  let mut pieceBase := baseOffset
                  while i < pieces.size && remain > 0 do
                    let p := pieces[i]!
                    let pLen := p.length.toNat
                    let pStart := pieceBase
                    let pEnd := pieceBase + pLen
                    if pEnd > cursor && pStart < endOffset then
                      let startInPiece := if cursor > pStart then cursor - pStart else 0
                      let maxReadable := pLen - startInPiece
                      let untilEnd := endOffset - (pStart + startInPiece)
                      let readLen := min remain (min maxReadable untilEnd)
                      if readLen > 0 then
                        let buf := PieceTableHelper.getBuffer pt p.source
                        let mut r := 0
                        while r < readLen do
                          out := out.push (buf[p.start.toNat + startInPiece + r]!)
                          r := r + 1
                        cursor := cursor + readLen
                        remain := remain - readLen
                    pieceBase := pieceBase + pLen
                    i := i + 1
              | ViE.PieceTree.internal children _ _ imeta =>
                  -- Use binary search to find start and end child indices
                  let relCursor : UInt64 := (if cursor > baseOffset then cursor - baseOffset else 0).toUInt64
                  let relEnd : UInt64 := (if endOffset > baseOffset then min (endOffset - baseOffset) (nodeLen - 1) else 0).toUInt64
                  let startChildIdx := findChildForOffset imeta relCursor
                  let endChildIdx := findChildForOffset imeta relEnd

                  -- Only process children in the relevant range
                  let mut i := min (endChildIdx + 1) children.size
                  while i > startChildIdx do
                    let j := i - 1
                    let child := children[j]!
                    let childStart := baseOffset + imeta.cumulativeBytes[j]!.toNat
                    let childEnd := if j + 1 < imeta.cumulativeBytes.size
                                    then baseOffset + imeta.cumulativeBytes[j + 1]!.toNat
                                    else nodeEnd
                    if childEnd > cursor && childStart < endOffset then
                      stack := (child, childStart) :: stack
                    i := j
      return out

def getBytes (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ByteArray :=
  getBytesCore t offset len pt

/-- Get substring from tree -/
def getSubstring (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : String :=
  String.fromUTF8! (getBytes t offset len pt)

/-- Find the leaf and relative offset containing the Nth newline -/
private def findNthNewlineLeafCore (t : ViE.PieceTree) (n : Nat) (pt : ViE.PieceTable) (accOffset : Nat)
  : Option (ViE.Piece × Nat × Nat) :=
  Id.run do
    let mut node := t
    let mut currN := n
    let mut currOff := accOffset
    while true do
      match node with
      | ViE.PieceTree.empty =>
          return none
      | ViE.PieceTree.leaf pieces _ _ =>
          let mut i := 0
          while i < pieces.size do
            let p := pieces[i]!
            if currN < p.lineBreaks.toNat then
              let buf := PieceTableHelper.getBuffer pt p.source
              let mut j := 0
              let mut targetN := currN
              let pLen := p.length.toNat
              let mut relOffset := pLen
              let mut done := false
              while j < pLen && !done do
                if buf[p.start.toNat + j]! == 10 then
                  if targetN == 0 then
                    relOffset := j + 1
                    done := true
                  else
                    targetN := targetN - 1
                j := j + 1
              return some (p, currOff, relOffset)
            currN := currN - p.lineBreaks.toNat
            currOff := currOff + p.length.toNat
            i := i + 1
          return none
      | ViE.PieceTree.internal children _ _ _ =>
          let mut i := 0
          let mut found := false
          while i < children.size && !found do
            let child := children[i]!
            let childLines := lineBreaks child
            if currN < childLines then
              node := child
              found := true
            else
              currN := currN - childLines
              currOff := currOff + length child
              i := i + 1
          if !found then
            return none
    return none

def findNthNewlineLeaf (t : ViE.PieceTree) (n : Nat) (pt : ViE.PieceTable) : Option (ViE.Piece × Nat × Nat) :=
  findNthNewlineLeafCore t n pt 0

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

def maximalSuffixLoop (x : ByteArray) (useLe : Bool) (m ms j k p : Int) : (Int × Int) :=
  Id.run do
    let mut ms := ms
    let mut j := j
    let mut k := k
    let mut p := p
    -- Keep an execution cap for robustness against malformed index states.
    let mNat := Int.toNat m
    let mut steps := (mNat + 1) * (mNat + 1) + 1
    while steps > 0 && j + k < m do
      let a := x[Int.toNat (j + k)]!
      let b := x[Int.toNat (ms + k)]!
      if useLe then
        if a < b then
          let jk := j + k
          j := jk
          k := 1
          p := jk - ms
        else if a == b then
          if k != p then
            k := k + 1
          else
            j := j + p
            k := 1
        else
          ms := j
          j := j + 1
          k := 1
          p := 1
      else if a > b then
        let jk := j + k
        j := jk
        k := 1
        p := jk - ms
      else if a == b then
        if k != p then
          k := k + 1
        else
          j := j + p
          k := 1
      else
        ms := j
        j := j + 1
        k := 1
        p := 1
      steps := steps - 1
    return (ms, p)

def maximalSuffix (x : ByteArray) (useLe : Bool) : (Int × Int) :=
  let m : Int := x.size
  maximalSuffixLoop x useLe m (-1) 0 1 1

private def twoWayForward1Core (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Nat) : Nat :=
  if j >= n then
    j
  else if haystack[i + j]! == needle[j]! then
    twoWayForward1Core haystack needle i n (j + 1)
  else
    j
  termination_by n - j
  decreasing_by
    simp_wf
    omega

def twoWayForward1 (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) : Int :=
  Int.ofNat (twoWayForward1Core haystack needle i n (Int.toNat j))

private def twoWayBackward1Core (haystack needle : ByteArray) (i : Nat) (mem : Int) (steps : Nat) : Int :=
  if hSteps : steps = 0 then
    mem
  else
    let j := mem + Int.ofNat steps
    if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
      twoWayBackward1Core haystack needle i mem (steps - 1)
    else
      j
  termination_by steps
  decreasing_by
    have hstepsPos : 0 < steps := Nat.pos_of_ne_zero hSteps
    exact Nat.sub_lt hstepsPos (by decide : 0 < 1)

def twoWayBackward1 (haystack needle : ByteArray) (i : Nat) (mem : Int) (j : Int) : Int :=
  if j <= mem then
    j
  else
    let steps := Int.toNat (j - mem)
    twoWayBackward1Core haystack needle i mem steps

private def twoWayForward2Core (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Nat) : Nat :=
  if j >= n then
    j
  else if haystack[i + j]! == needle[j]! then
    twoWayForward2Core haystack needle i n (j + 1)
  else
    j
  termination_by n - j
  decreasing_by
    simp_wf
    omega

def twoWayForward2 (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) : Int :=
  Int.ofNat (twoWayForward2Core haystack needle i n (Int.toNat j))

private def twoWayBackward2Core (haystack needle : ByteArray) (i : Nat) (steps : Nat) : Int :=
  if hSteps : steps = 0 then
    -1
  else
    let j := Int.ofNat steps - 1
    if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
      twoWayBackward2Core haystack needle i (steps - 1)
    else
      j
  termination_by steps
  decreasing_by
    have hstepsPos : 0 < steps := Nat.pos_of_ne_zero hSteps
    exact Nat.sub_lt hstepsPos (by decide : 0 < 1)

def twoWayBackward2 (haystack needle : ByteArray) (i : Nat) (j : Int) : Int :=
  if j < 0 then
    j
  else
    twoWayBackward2Core haystack needle i (Int.toNat (j + 1))

private def twoWayShortLoopCore (haystack needle : ByteArray) (_start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int) : Option Nat :=
  if i > maxStart then
    none
  else
    let j0 := max (Int.ofNat msNat) mem + 1
    let j := twoWayForward1 haystack needle i n j0
    if j >= n then
      let j2 := twoWayBackward1 haystack needle i mem (Int.ofNat msNat)
      if j2 <= mem then
        some i
      else
        let nextI := i + pNat
        if nextI <= i then
          none
        else
          let nextMem := Int.ofNat (n - pNat - 1)
          twoWayShortLoopCore haystack needle _start maxStart msNat pNat n nextI nextMem
    else
      let shift := Int.toNat (j - Int.ofNat msNat)
      if shift == 0 then
        none
      else
        let nextI := i + shift
        if nextI <= i then
          none
        else
          twoWayShortLoopCore haystack needle _start maxStart msNat pNat n nextI (-1)
  termination_by maxStart + 1 - i
  decreasing_by
    ·
      simp_wf
      grind
    ·
      simp_wf
      grind

def twoWayShortLoop (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int) : Option Nat :=
  twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem

private def twoWayLongLoopCore (haystack needle : ByteArray) (_start maxStart msNat pNat n : Nat) (i : Nat) : Option Nat :=
  if i > maxStart then
    none
  else
    let j := twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))
    if j >= n then
      let j2 := twoWayBackward2 haystack needle i (Int.ofNat msNat)
      if j2 < 0 then
        some i
      else
        let nextI := i + pNat
        if nextI <= i then
          none
        else
          twoWayLongLoopCore haystack needle _start maxStart msNat pNat n nextI
    else
      let shift := Int.toNat (j - Int.ofNat msNat)
      if shift == 0 then
        none
      else
        let nextI := i + shift
        if nextI <= i then
          none
        else
          twoWayLongLoopCore haystack needle _start maxStart msNat pNat n nextI
  termination_by maxStart + 1 - i
  decreasing_by
    ·
      simp_wf
      grind
    ·
      simp_wf
      grind

def twoWayLongLoop (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) : Option Nat :=
  twoWayLongLoopCore haystack needle start maxStart msNat pNat n i

def twoWaySearch (haystack : ByteArray) (needle : ByteArray) (start : Nat) : Option Nat :=
  let n := needle.size
  let h := haystack.size
  if n == 0 then
    some start
  else if h < n || start + n > h then
    none
  else
    let (ms1, p1) := maximalSuffix needle true
    let (ms2, p2) := maximalSuffix needle false
    let (ms, p) := if ms1 > ms2 then (ms1, p1) else (ms2, p2)
    let msNat := Int.toNat ms
    let pNat := Int.toNat p
    let maxStart := h - n
    let rec prefixEqual (i : Nat) : Bool :=
      if ms < 0 then true
      else if i > msNat then true
      else if i + pNat >= n then false
      else if needle[i]! == needle[i + pNat]! then
        prefixEqual (i + 1)
      else
        false
    let shortPeriod := prefixEqual 0
    if shortPeriod then
      twoWayShortLoop haystack needle start maxStart msNat pNat n start (-1)
    else
      twoWayLongLoop haystack needle start maxStart msNat pNat n start

def findPatternInBytes (haystack : ByteArray) (needle : ByteArray) (start : Nat) : Option Nat :=
  twoWaySearch haystack needle start

def findLastPatternInBytes (haystack : ByteArray) (needle : ByteArray) : Option Nat :=
  let n := needle.size
  let h := haystack.size
  if n == 0 then
    some 0
  else if h < n then
    none
  else
    let maxStart := h - n
    let rec loop (i : Nat) (last : Option Nat) : Option Nat :=
      if i > maxStart then last
      else
        match findPatternInBytes haystack needle i with
        | some idx =>
            if idx > maxStart then last
            else if idx < i then last
            else loop (idx + 1) (some idx)
        | none => last
      termination_by maxStart + 1 - i
      decreasing_by
        simp_wf
        omega
    loop 0 none

/-- Search forward for a byte pattern from a given offset -/
private def searchNextCore (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startOffset : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (_cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  if pattern.size == 0 then
    (none, cache, order)
  else
    let total := length t
    if startOffset >= total then
      (none, cache, order)
    else if pattern.size < 3 || !useBloom then
      let chunkLen := max chunkSize pattern.size
      let overlap := pattern.size - 1
      let found := Id.run do
        let mut offset := startOffset
        while offset < total do
          let remaining := total - offset
          let readLen := min chunkLen remaining
          if readLen < pattern.size then
            return none
          let bytes := getBytes t offset readLen pt
          match findPatternInBytes bytes pattern 0 with
          | some idx => return some (offset + idx)
          | none =>
              if offset + readLen >= total then
                return none
              offset := offset + (readLen - overlap)
        return none
      (found, cache, order)
    else
      let hashes := patternTrigramHashes pattern
      let overlap := pattern.size - 1
      Id.run do
        let mut stack : List (ViE.PieceTree × Nat) := [(t, 0)]
        let mut cacheAcc := cache
        let mut orderAcc := order
        while !stack.isEmpty do
          match stack with
          | [] => pure ()
          | (node, baseOffset) :: rest =>
              stack := rest
              if baseOffset + length node <= startOffset then
                pure ()
              else
                match node with
                | ViE.PieceTree.empty => pure ()
                | ViE.PieceTree.leaf _ _ m =>
                    let relStart := if startOffset > baseOffset then startOffset - baseOffset else 0
                    let remain := length node - relStart
                    let globalStart := baseOffset + relStart
                    let available := total - globalStart
                    let readLen := min (remain + overlap) available
                    if readLen < pattern.size then
                      pure ()
                    else
                      let crossesBoundary := readLen > remain
                      if !crossesBoundary && !bloomMayContain m hashes then
                        pure ()
                      else
                        let bytes := getBytes t globalStart readLen pt
                        match findPatternInBytes bytes pattern 0 with
                        | some idx => return (some (globalStart + idx), cacheAcc, orderAcc)
                        | none => pure ()
                | ViE.PieceTree.internal children _ m _ =>
                    if !bloomMayContain m hashes then
                      pure ()
                    else
                      let mut i := children.size
                      let mut childEnd := baseOffset + length node
                      while i > 0 do
                        let j := i - 1
                        let child := children[j]!
                        let childLen := length child
                        let childStart := childEnd - childLen
                        if childEnd > startOffset then
                          stack := (child, childStart) :: stack
                        childEnd := childStart
                        i := j
        return (none, cacheAcc, orderAcc)

def searchNext (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startOffset : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  searchNextCore t pt pattern startOffset chunkSize useBloom cache order cacheMax

/-- Search backward for a byte pattern ending before startExclusive -/
private def searchPrevCore (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startExclusive : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (_cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  if pattern.size == 0 then
    (none, cache, order)
  else
    let total := length t
    let end0 := min startExclusive total
    if end0 == 0 then
      (none, cache, order)
    else if pattern.size < 3 || !useBloom then
      let chunkLen := max chunkSize pattern.size
      let overlap := pattern.size - 1
      let found := Id.run do
        let mut endOffset := end0
        while endOffset > 0 do
          let start := if endOffset > chunkLen then endOffset - chunkLen else 0
          let readLen := endOffset - start
          if readLen < pattern.size then
            if start == 0 then
              return none
            endOffset := start + overlap
          else
            let bytes := getBytes t start readLen pt
            match findLastPatternInBytes bytes pattern with
            | some idx =>
                let pos := start + idx
                if pos < endOffset then
                  return some pos
                return none
            | none =>
                if start == 0 then
                  return none
                endOffset := start + overlap
        return none
      (found, cache, order)
    else
      let hashes := patternTrigramHashes pattern
      let overlap := pattern.size - 1
      Id.run do
        let mut stack : List (ViE.PieceTree × Nat) := [(t, 0)]
        let mut cacheAcc := cache
        let mut orderAcc := order
        while !stack.isEmpty do
          match stack with
          | [] => pure ()
          | (node, baseOffset) :: rest =>
              stack := rest
              if baseOffset >= end0 then
                pure ()
              else
                match node with
                | ViE.PieceTree.empty => pure ()
                | ViE.PieceTree.leaf _ _ m =>
                    let relEnd := min (end0 - baseOffset) (length node)
                    let globalEnd := baseOffset + relEnd
                    let globalStart := if baseOffset > overlap then baseOffset - overlap else 0
                    let readLen := globalEnd - globalStart
                    if readLen < pattern.size then
                      pure ()
                    else
                      let crossesBoundary := globalStart < baseOffset
                      if !crossesBoundary && !bloomMayContain m hashes then
                        pure ()
                      else
                        let bytes := getBytes t globalStart readLen pt
                        match findLastPatternInBytes bytes pattern with
                        | some idx =>
                            let pos := globalStart + idx
                            if pos < end0 then
                              return (some pos, cacheAcc, orderAcc)
                            pure ()
                        | none => pure ()
                | ViE.PieceTree.internal children _ m _ =>
                    if !bloomMayContain m hashes then
                      pure ()
                    else
                      let mut i := 0
                      let mut childOffset := baseOffset
                      while i < children.size do
                        let child := children[i]!
                        if childOffset < end0 then
                          stack := (child, childOffset) :: stack
                        childOffset := childOffset + length child
                        i := i + 1
        return (none, cacheAcc, orderAcc)

def searchPrev (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startExclusive : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  searchPrevCore t pt pattern startExclusive chunkSize useBloom cache order cacheMax

end PieceTree

end ViE
