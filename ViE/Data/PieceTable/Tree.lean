import Lean
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
  | ViE.PieceTree.leaf _ s _ => s
  | ViE.PieceTree.internal _ s _ => s

def length (t : ViE.PieceTree) : Nat := (stats t).bytes
def lineBreaks (t : ViE.PieceTree) : Nat := (stats t).lines
def height (t : ViE.PieceTree) : Nat := (stats t).height

def searchMetaOf (t : ViE.PieceTree) : ViE.SearchBloom :=
  match t with
  | ViE.PieceTree.empty => ViE.SearchBloom.empty
  | ViE.PieceTree.leaf _ _ m => m
  | ViE.PieceTree.internal _ _ m => m

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
    let mask : UInt8 := UInt8.ofNat (1 <<< bitIdx)
    bloom.set! byteIdx (cur ||| mask)
  else
    bloom

def bloomGetBit (bloom : ByteArray) (idx : Nat) : Bool :=
  let byteIdx := idx / 8
  let bitIdx := idx % 8
  if byteIdx < bloom.size then
    let cur := bloom[byteIdx]!
    let mask : UInt8 := UInt8.ofNat (1 <<< bitIdx)
    (cur &&& mask) != 0
  else
    false

def hash1 (b0 b1 b2 : UInt8) : Nat :=
  (b0.toNat * 961 + b1.toNat * 31 + b2.toNat) % ViE.BloomBits

def hash2 (b0 b1 b2 : UInt8) : Nat :=
  (b0.toNat * 17161 + b1.toNat * 131 + b2.toNat) % ViE.BloomBits

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

partial def buildPrefixBytes (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : Array UInt8 :=
  let rec loop (i : Nat) (acc : Array UInt8) : Array UInt8 :=
    if i >= pieces.size || acc.size >= 2 then
      acc
    else
      let p := pieces[i]!
      let buf := PieceTableHelper.getBuffer pt p.source
      let slice := buf.extract p.start (p.start + p.length)
      if slice.size > 0 then
        let need := 2 - acc.size
        let take := takeFirstBytes slice.data need
        loop (i + 1) (acc ++ take)
      else
        loop (i + 1) acc
  loop 0 #[]

partial def buildSuffixBytes (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : Array UInt8 :=
  let rec loop (i : Nat) (acc : Array UInt8) : Array UInt8 :=
    if i == 0 || acc.size >= 2 then
      acc
    else
      let idx := i - 1
      let p := pieces[idx]!
      let buf := PieceTableHelper.getBuffer pt p.source
      let slice := buf.extract p.start (p.start + p.length)
      if slice.size > 0 then
        let need := 2 - acc.size
        let take := takeLastBytes slice.data need
        loop idx (take ++ acc)
      else
        loop idx acc
  loop pieces.size #[]

def addBytesToBloom (bloom : ByteArray) (carry : Array UInt8) (bytes : ByteArray) : (ByteArray × Array UInt8) :=
  let arr := carry ++ bytes.data
  let bloom' := addTrigramsFromArray bloom arr
  let carry' := takeLastBytes arr 2
  (bloom', carry')

def addBoundaryTrigrams (bloom : ByteArray) (leftSuffix rightPrefix : Array UInt8) : ByteArray :=
  let combined := leftSuffix ++ rightPrefix
  addTrigramsFromArray bloom combined

def buildBloomForPieces (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : ViE.SearchBloom := Id.run do
  if !ViE.BloomBuildLeafBits then
    let prefixBytes := buildPrefixBytes pieces pt
    let suffixBytes := buildSuffixBytes pieces pt
    return { bits := ViE.SearchBloom.empty.bits, prefixBytes := prefixBytes, suffixBytes := suffixBytes }
  else
    let mut bits := ViE.SearchBloom.empty.bits
    let mut carry : Array UInt8 := #[]
    let mut prefixBytes : Array UInt8 := #[]
    for p in pieces do
      let buf := PieceTableHelper.getBuffer pt p.source
      let slice := buf.extract p.start (p.start + p.length)
      if prefixBytes.size < 2 && slice.size > 0 then
        let need := 2 - prefixBytes.size
        let arr := slice.data
        let take := takeFirstBytes arr need
        prefixBytes := prefixBytes ++ take
      let (bits', carry') := addBytesToBloom bits carry slice
      bits := bits'
      carry := carry'
    return { bits := bits, prefixBytes := prefixBytes, suffixBytes := carry }

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
  if bloomIsEmpty left.bits || bloomIsEmpty right.bits then
    { bits := ViE.SearchBloom.empty.bits, prefixBytes := pref, suffixBytes := suf }
  else
    let bits := bloomOr left.bits right.bits
    let bits := addBoundaryTrigrams bits left.suffixBytes right.prefixBytes
    { bits := bits, prefixBytes := pref, suffixBytes := suf }

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

def bloomMayContain (bloom : ByteArray) (hashes : Array (Nat × Nat)) : Bool :=
  if hashes.isEmpty then
    true
  else if bloomIsEmpty bloom then
    -- Empty bloom means "unknown", do not prune.
    true
  else
    hashes.all (fun (h1, h2) => bloomGetBit bloom h1 && bloomGetBit bloom h2)

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
  let s := pieces.foldl (fun acc p => acc + (ViE.Stats.ofPiece p)) ViE.Stats.empty
  let searchMeta := buildBloomForPieces pieces pt
  ViE.PieceTree.leaf pieces s searchMeta

/-- Create an internal node -/
def mkInternal (children : Array ViE.PieceTree) : ViE.PieceTree :=
  let s := children.foldl (fun acc c => acc + (stats c)) ViE.Stats.empty
  let s := { s with height := s.height + 1 }
  let searchMeta := buildBloomForChildren children
  ViE.PieceTree.internal children s searchMeta

/-- Efficiently concatenate a list of pieces into a tree -/
partial def fromPieces (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : ViE.PieceTree :=
  if pieces.isEmpty then ViE.PieceTree.empty
  else if pieces.size <= ViE.NodeCapacity then
    mkLeaf pieces pt
  else
    let mid := pieces.size / 2
    let left := fromPieces (pieces.extract 0 mid) pt
    let right := fromPieces (pieces.extract mid pieces.size) pt
    mkInternal #[left, right]

/-- Concatenate two trees while maintaining B+ tree invariants -/
partial def concat (l : ViE.PieceTree) (r : ViE.PieceTree) (pt : ViE.PieceTable) : ViE.PieceTree :=
  match l, r with
  | ViE.PieceTree.empty, _ => r
  | _, ViE.PieceTree.empty => l

  | ViE.PieceTree.leaf ps1 _ _, ViE.PieceTree.leaf ps2 _ _ =>
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
          mkLeaf ps pt
        else
          let mid := ps.size / 2
          mkInternal #[mkLeaf (ps.extract 0 mid) pt, mkLeaf (ps.extract mid ps.size) pt]
      else
        let ps := ps1 ++ ps2
        if ps.size <= ViE.NodeCapacity then mkLeaf ps pt
        else mkInternal #[mkLeaf ps1 pt, mkLeaf ps2 pt]
    else if ps1.size > 0 then l
    else r

  | ViE.PieceTree.internal cs1 _ _, ViE.PieceTree.internal cs2 _ _ =>
    let h1 := height l
    let h2 := height r
    if h1 == h2 then
      -- Merge boundary children
      let lastChild := cs1.back!
      let firstChild := cs2[0]!
      let merged := concat lastChild firstChild pt
      match merged with
      | ViE.PieceTree.internal newCS s _ =>
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
      let newLast := concat lastChild r pt
      match newLast with
      | ViE.PieceTree.internal newChildren s _ =>
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
      let newFirst := concat l firstChild pt
      match newFirst with
      | ViE.PieceTree.internal newChildren s _ =>
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
  | ViE.PieceTree.leaf .. , ViE.PieceTree.internal .. => concat (mkInternal #[l]) r pt
  | ViE.PieceTree.internal .. , ViE.PieceTree.leaf .. => concat l (mkInternal #[r]) pt

/-- Split the tree at a given byte offset -/
partial def split (t : ViE.PieceTree) (offset : Nat) (pt : ViE.PieceTable) : (ViE.PieceTree × ViE.PieceTree) :=
  match t with
  | ViE.PieceTree.empty => (ViE.PieceTree.empty, ViE.PieceTree.empty)
  | ViE.PieceTree.leaf pieces _ _ =>
    let rec findSplitLeaf (i : Nat) (accOffset : Nat) : (ViE.PieceTree × ViE.PieceTree) :=
      if i >= pieces.size then (t, ViE.PieceTree.empty)
      else
        let p := pieces[i]!
        if offset < accOffset + p.length then
          let relOffset := offset - accOffset
          if relOffset == 0 then
             (mkLeaf (pieces.extract 0 i) pt, mkLeaf (pieces.extract i pieces.size) pt)
          else
             let (p1, p2) := PieceTableHelper.splitPiece p relOffset pt
             (mkLeaf ((pieces.extract 0 i).push p1) pt, mkLeaf (#[p2] ++ (pieces.extract (i + 1) pieces.size)) pt)
        else
          findSplitLeaf (i + 1) (accOffset + p.length)
    findSplitLeaf 0 0
  | ViE.PieceTree.internal children _ _ =>
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
  concat l r pt

/-- Get bytes from tree -/
partial def getBytes (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ByteArray :=
  let rec collect (t : ViE.PieceTree) (off : Nat) (l : Nat) (acc : Array ByteArray) : (Array ByteArray × Nat) :=
    if l == 0 then (acc, 0)
    else match t with
      | ViE.PieceTree.empty => (acc, 0)
      | ViE.PieceTree.leaf pieces _ _ =>
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
      | ViE.PieceTree.internal children _ _ =>
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
  chunks.foldl (fun (acc : ByteArray) (b : ByteArray) => acc ++ b) (ByteArray.mk #[])

/-- Get substring from tree -/
partial def getSubstring (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : String :=
  String.fromUTF8! (getBytes t offset len pt)

/-- Find the leaf and relative offset containing the Nth newline -/
partial def findNthNewlineLeaf (t : ViE.PieceTree) (n : Nat) (pt : ViE.PieceTable) : Option (ViE.Piece × Nat × Nat) :=
  let rec scan (t : ViE.PieceTree) (n : Nat) (accOffset : Nat) : Option (ViE.Piece × Nat × Nat) :=
    match t with
    | ViE.PieceTree.empty => none
    | ViE.PieceTree.leaf pieces _ _ =>
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
    | ViE.PieceTree.internal children _ _ =>
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

partial def maximalSuffixLoop (x : ByteArray) (useLe : Bool) (m ms j k p : Int) : (Int × Int) :=
  if j + k >= m then
    (ms, p)
  else
    let a := x[Int.toNat (j + k)]!
    let b := x[Int.toNat (ms + k)]!
    if useLe then
      if a < b then
        maximalSuffixLoop x useLe m ms (j + k) 1 (j + k - ms)
      else if a == b then
        if k != p then
          maximalSuffixLoop x useLe m ms j (k + 1) p
        else
          maximalSuffixLoop x useLe m ms (j + p) 1 p
      else
        maximalSuffixLoop x useLe m j (j + 1) 1 1
    else
      if a > b then
        maximalSuffixLoop x useLe m ms (j + k) 1 (j + k - ms)
      else if a == b then
        if k != p then
          maximalSuffixLoop x useLe m ms j (k + 1) p
        else
          maximalSuffixLoop x useLe m ms (j + p) 1 p
      else
        maximalSuffixLoop x useLe m j (j + 1) 1 1

def maximalSuffix (x : ByteArray) (useLe : Bool) : (Int × Int) :=
  let m : Int := x.size
  maximalSuffixLoop x useLe m (-1) 0 1 1

partial def twoWayForward1 (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) : Int :=
  if j >= n then
    j
  else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
    twoWayForward1 haystack needle i n (j + 1)
  else
    j

partial def twoWayBackward1 (haystack needle : ByteArray) (i : Nat) (mem : Int) (j : Int) : Int :=
  if j <= mem then
    j
  else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
    twoWayBackward1 haystack needle i mem (j - 1)
  else
    j

partial def twoWayForward2 (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) : Int :=
  if j >= n then
    j
  else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
    twoWayForward2 haystack needle i n (j + 1)
  else
    j

partial def twoWayBackward2 (haystack needle : ByteArray) (i : Nat) (j : Int) : Int :=
  if j < 0 then
    j
  else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
    twoWayBackward2 haystack needle i (j - 1)
  else
    j

partial def twoWayShortLoop (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int) : Option Nat :=
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
        let nextMem := Int.ofNat (n - pNat - 1)
        twoWayShortLoop haystack needle start maxStart msNat pNat n nextI nextMem
    else
      let shift := Int.toNat (j - Int.ofNat msNat)
      twoWayShortLoop haystack needle start maxStart msNat pNat n (i + shift) (-1)

partial def twoWayLongLoop (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) : Option Nat :=
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
        twoWayLongLoop haystack needle start maxStart msNat pNat n nextI
    else
      let shift := Int.toNat (j - Int.ofNat msNat)
      twoWayLongLoop haystack needle start maxStart msNat pNat n (i + shift)

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

partial def findPatternInBytes (haystack : ByteArray) (needle : ByteArray) (start : Nat) : Option Nat :=
  twoWaySearch haystack needle start

partial def findLastPatternInBytes (haystack : ByteArray) (needle : ByteArray) : Option Nat :=
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
            else loop (idx + 1) (some idx)
        | none => last
    loop 0 none

/-- Search forward for a byte pattern from a given offset -/
partial def searchNext (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startOffset : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  if pattern.size == 0 then
    (none, cache, order)
  else
    let total := length t
    if startOffset >= total then
      (none, cache, order)
    else
      if pattern.size < 3 || !useBloom then
        let chunkLen := max chunkSize pattern.size
        let overlap := pattern.size - 1
        let rec loop (offset : Nat) : Option Nat :=
          if offset >= total then none
          else
            let remaining := total - offset
            let readLen := min chunkLen remaining
            if readLen < pattern.size then
              none
            else
              let bytes := getBytes t offset readLen pt
              match findPatternInBytes bytes pattern 0 with
              | some idx => some (offset + idx)
              | none =>
                if offset + readLen >= total then none
                else
                  let nextOffset := offset + (readLen - overlap)
                  loop nextOffset
        (loop startOffset, cache, order)
      else
        let hashes := patternTrigramHashes pattern
        let rec searchNode (node : ViE.PieceTree) (baseOffset : Nat)
          (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat)
          : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
          if baseOffset + length node <= startOffset then
            (none, cache, order)
          else
            match node with
            | ViE.PieceTree.empty => (none, cache, order)
            | ViE.PieceTree.leaf _ _ _ =>
                let relStart := if startOffset > baseOffset then startOffset - baseOffset else 0
                let remain := length node - relStart
                if remain < pattern.size then
                  (none, cache, order)
                else
                  match node with
                  | ViE.PieceTree.leaf pieces _ m =>
                      let (bits, cache, order) :=
                        if bloomIsEmpty m.bits then
                          leafBloomBitsWithCache pieces pt baseOffset cache order cacheMax
                        else
                          (m.bits, cache, order)
                      if !bloomMayContain bits hashes then
                        (none, cache, order)
                      else
                        let bytes := getBytes node relStart remain pt
                        match findPatternInBytes bytes pattern 0 with
                        | some idx => (some (baseOffset + relStart + idx), cache, order)
                        | none => (none, cache, order)
                  | _ => (none, cache, order)
            | ViE.PieceTree.internal children _ _ =>
                let rec loop (i : Nat) (offset : Nat)
                  (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat)
                  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
                  if i >= children.size then
                    (none, cache, order)
                  else
                    let child := children[i]!
                    let childLen := length child
                    let childEnd := offset + childLen
                    if childEnd <= startOffset then
                      loop (i + 1) childEnd cache order
                    else
                      match searchNode child offset cache order with
                      | (some res, cache, order) => (some res, cache, order)
                      | (none, cache, order) => loop (i + 1) childEnd cache order
                loop 0 baseOffset cache order
        searchNode t 0 cache order

/-- Search backward for a byte pattern ending before startExclusive -/
partial def searchPrev (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startExclusive : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
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
      let rec loop (endOffset : Nat) : Option Nat :=
        if endOffset == 0 then none
        else
          let start := if endOffset > chunkLen then endOffset - chunkLen else 0
          let readLen := endOffset - start
          if readLen < pattern.size then
            if start == 0 then none else loop (start + overlap)
          else
            let bytes := getBytes t start readLen pt
            match findLastPatternInBytes bytes pattern with
            | some idx =>
                let pos := start + idx
                if pos < endOffset then some pos else none
            | none =>
                if start == 0 then none else loop (start + overlap)
      (loop end0, cache, order)
    else
      let hashes := patternTrigramHashes pattern
      let rec searchNode (node : ViE.PieceTree) (baseOffset : Nat)
        (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat)
        : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
        if baseOffset >= end0 then
          (none, cache, order)
        else
          match node with
          | ViE.PieceTree.empty => (none, cache, order)
          | ViE.PieceTree.leaf _ _ _ =>
              let relEnd := min (end0 - baseOffset) (length node)
              if relEnd < pattern.size then
                (none, cache, order)
              else
                match node with
                | ViE.PieceTree.leaf pieces _ m =>
                    let (bits, cache, order) :=
                      if bloomIsEmpty m.bits then
                        leafBloomBitsWithCache pieces pt baseOffset cache order cacheMax
                      else
                        (m.bits, cache, order)
                    if !bloomMayContain bits hashes then
                      (none, cache, order)
                    else
                      let bytes := getBytes node 0 relEnd pt
                      match findLastPatternInBytes bytes pattern with
                      | some idx => (some (baseOffset + idx), cache, order)
                      | none => (none, cache, order)
                | _ => (none, cache, order)
          | ViE.PieceTree.internal children _ _ =>
              let spans : Array (ViE.PieceTree × Nat) := Id.run do
                let mut acc : Array (ViE.PieceTree × Nat) := #[]
                let mut offset := baseOffset
                for child in children do
                  acc := acc.push (child, offset)
                  offset := offset + length child
                return acc
              let rec loop (i : Nat)
                (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat)
                : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
                if i >= spans.size then
                  (none, cache, order)
                else
                  let j := spans.size - 1 - i
                  let (child, childOffset) := spans[j]!
                  if childOffset >= end0 then
                    loop (i + 1) cache order
                  else
                    match searchNode child childOffset cache order with
                    | (some res, cache, order) =>
                        if res < end0 then (some res, cache, order) else loop (i + 1) cache order
                    | (none, cache, order) => loop (i + 1) cache order
              loop 0 cache order
      searchNode t 0 cache order

end PieceTree

end ViE
