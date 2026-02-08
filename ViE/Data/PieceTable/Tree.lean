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

def buildPrefixBytes (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : Array UInt8 := Id.run do
  let mut i := 0
  let mut acc : Array UInt8 := #[]
  while i < pieces.size && acc.size < 2 do
    let p := pieces[i]!
    let buf := PieceTableHelper.getBuffer pt p.source
    let slice := buf.extract p.start (p.start + p.length)
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
    let slice := buf.extract p.start (p.start + p.length)
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
def fromPieces (pieces : Array ViE.Piece) (pt : ViE.PieceTable) : ViE.PieceTree :=
  if pieces.isEmpty then ViE.PieceTree.empty
  else if pieces.size <= ViE.NodeCapacity then
    mkLeaf pieces pt
  else
    let mid := pieces.size / 2
    let left := fromPieces (pieces.extract 0 mid) pt
    let right := fromPieces (pieces.extract mid pieces.size) pt
    mkInternal #[left, right]
  termination_by pieces.size
  decreasing_by
    · simp_wf
      have hgt : ViE.NodeCapacity < pieces.size := Nat.lt_of_not_ge (by assumption)
      have hsize : 0 < pieces.size := Nat.lt_trans (by decide : 0 < ViE.NodeCapacity) hgt
      have hdiv : pieces.size / 2 < pieces.size := Nat.div_lt_self hsize (by decide : 1 < 2)
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hdiv
    · simp_wf
      have hgt : ViE.NodeCapacity < pieces.size := Nat.lt_of_not_ge (by assumption)
      have hsize : 0 < pieces.size := Nat.lt_trans (by decide : 0 < ViE.NodeCapacity) hgt
      have hge2 : 2 ≤ pieces.size := Nat.le_trans (by decide : 2 ≤ ViE.NodeCapacity) (Nat.le_of_lt hgt)
      have hhalf : 0 < pieces.size / 2 := Nat.div_pos hge2 (by decide : 0 < 2)
      exact Nat.sub_lt hsize hhalf

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
        | ViE.PieceTree.internal children _ _ =>
            let mut i := children.size
            while i > 0 do
              let j := i - 1
              stack := children[j]! :: stack
              i := j
  return out

/-- Concatenate two trees while maintaining B+ tree invariants. -/
private def concatCore (l : ViE.PieceTree) (r : ViE.PieceTree) (pt : ViE.PieceTable) (fuel : Nat) : ViE.PieceTree :=
  match fuel with
  | 0 =>
    -- Rebuild into a balanced tree in pathological cases instead of creating deep chains.
    fromPieces (toPieces l ++ toPieces r) pt
  | fuel + 1 =>
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
        let merged := concatCore lastChild firstChild pt fuel
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
        let newLast := concatCore lastChild r pt fuel
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
        let newFirst := concatCore l firstChild pt fuel
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
    | ViE.PieceTree.leaf .. , ViE.PieceTree.internal .. => concatCore (mkInternal #[l]) r pt fuel
    | ViE.PieceTree.internal .. , ViE.PieceTree.leaf .. => concatCore l (mkInternal #[r]) pt fuel
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def concat (l : ViE.PieceTree) (r : ViE.PieceTree) (pt : ViE.PieceTable) : ViE.PieceTree :=
  -- Cap recursion depth and rely on balanced fallback when exhausted.
  let rawFuel := (height l + height r + 4) * 8 + 64
  let fuel := min rawFuel 2048
  concatCore l r pt fuel

/-- Split the tree at a given byte offset. -/
private def splitCore (t : ViE.PieceTree) (offset : Nat) (pt : ViE.PieceTable) (fuel : Nat) : (ViE.PieceTree × ViE.PieceTree) :=
  match fuel with
  | 0 => (t, ViE.PieceTree.empty)
  | fuel + 1 =>
      match t with
      | ViE.PieceTree.empty => (ViE.PieceTree.empty, ViE.PieceTree.empty)
      | ViE.PieceTree.leaf pieces _ _ =>
          Id.run do
            let mut i := 0
            let mut accOffset := 0
            while i < pieces.size do
              let p := pieces[i]!
              if offset < accOffset + p.length then
                let relOffset := offset - accOffset
                if relOffset == 0 then
                  return (mkLeaf (pieces.extract 0 i) pt, mkLeaf (pieces.extract i pieces.size) pt)
                let (p1, p2) := PieceTableHelper.splitPiece p relOffset pt
                return (mkLeaf ((pieces.extract 0 i).push p1) pt, mkLeaf (#[p2] ++ (pieces.extract (i + 1) pieces.size)) pt)
              accOffset := accOffset + p.length
              i := i + 1
            return (t, ViE.PieceTree.empty)
      | ViE.PieceTree.internal children _ _ =>
          Id.run do
            let mut i := 0
            let mut accOffset := 0
            while i < children.size do
              let c := children[i]!
              let cLen := length c
              if offset < accOffset + cLen then
                let (l, r) := splitCore c (offset - accOffset) pt fuel
                let leftSide := mkInternal ((children.extract 0 i).push l)
                let rightSide := mkInternal (#[r] ++ (children.extract (i + 1) children.size))
                return (leftSide, rightSide)
              accOffset := accOffset + cLen
              i := i + 1
            return (t, ViE.PieceTree.empty)
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def split (t : ViE.PieceTree) (offset : Nat) (pt : ViE.PieceTable) : (ViE.PieceTree × ViE.PieceTree) :=
  let fuel := (height t + 4) * 32 + 64
  splitCore t offset pt fuel

/-- Delete range from tree -/
def delete (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ViE.PieceTree :=
  let (l, mid_r) := split t offset pt
  let (_, r) := split mid_r len pt
  concat l r pt

/-- Get bytes from tree. -/
private def getBytesCore (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) (fuel : Nat) : ByteArray :=
  let rec collect (fuel : Nat) (t : ViE.PieceTree) (off : Nat) (l : Nat) (acc : Array ByteArray) : (Array ByteArray × Nat) :=
    match fuel with
    | 0 => (acc, 0)
    | fuel + 1 =>
        if l == 0 then (acc, 0)
        else
          match t with
          | ViE.PieceTree.empty => (acc, 0)
          | ViE.PieceTree.leaf pieces _ _ =>
              Id.run do
                let mut i := 0
                let mut accOffset := 0
                let mut currAcc := acc
                let mut remain := l
                while i < pieces.size && remain > 0 do
                  let p := pieces[i]!
                  let pLen := p.length
                  if off < accOffset + pLen then
                    let pStart := if off > accOffset then off - accOffset else 0
                    let readLen := min remain (pLen - pStart)
                    let buf := PieceTableHelper.getBuffer pt p.source
                    let slice := buf.extract (p.start + pStart) (p.start + pStart + readLen)
                    currAcc := currAcc.push slice
                    remain := remain - readLen
                  accOffset := accOffset + pLen
                  i := i + 1
                return (currAcc, l - remain)
          | ViE.PieceTree.internal children _ _ =>
              Id.run do
                let mut i := 0
                let mut accOffset := 0
                let mut currAcc := acc
                let mut remain := l
                while i < children.size && remain > 0 do
                  let c := children[i]!
                  let cLen := length c
                  if off < accOffset + cLen then
                    let cStart := if off > accOffset then off - accOffset else 0
                    let (newAcc, readInThisChild) := collect fuel c cStart remain currAcc
                    currAcc := newAcc
                    remain := remain - readInThisChild
                  accOffset := accOffset + cLen
                  i := i + 1
                return (currAcc, l - remain)
  let (chunks, _) := collect fuel t offset len #[]
  chunks.foldl (fun (acc : ByteArray) (b : ByteArray) => acc ++ b) (ByteArray.mk #[])

def getBytes (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : ByteArray :=
  let fuel := (height t + 4) * 32 + 64
  getBytesCore t offset len pt fuel

/-- Get substring from tree -/
def getSubstring (t : ViE.PieceTree) (offset : Nat) (len : Nat) (pt : ViE.PieceTable) : String :=
  String.fromUTF8! (getBytes t offset len pt)

/-- Find the leaf and relative offset containing the Nth newline -/
private def findNthNewlineLeafCore (t : ViE.PieceTree) (n : Nat) (pt : ViE.PieceTable) (accOffset : Nat) (fuel : Nat)
  : Option (ViE.Piece × Nat × Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match t with
      | ViE.PieceTree.empty => none
      | ViE.PieceTree.leaf pieces _ _ =>
          Id.run do
            let mut i := 0
            let mut currN := n
            let mut currOff := accOffset
            while i < pieces.size do
              let p := pieces[i]!
              if currN < p.lineBreaks then
                let buf := PieceTableHelper.getBuffer pt p.source
                let mut j := 0
                let mut targetN := currN
                let mut relOffset := p.length
                let mut done := false
                while j < p.length && !done do
                  if buf[p.start + j]! == 10 then
                    if targetN == 0 then
                      relOffset := j + 1
                      done := true
                    else
                      targetN := targetN - 1
                  j := j + 1
                return some (p, currOff, relOffset)
              currN := currN - p.lineBreaks
              currOff := currOff + p.length
              i := i + 1
            return none
      | ViE.PieceTree.internal children _ _ =>
          Id.run do
            let mut i := 0
            let mut currN := n
            let mut currOff := accOffset
            while i < children.size do
              let child := children[i]!
              let childLines := lineBreaks child
              if currN < childLines then
                return findNthNewlineLeafCore child currN pt currOff fuel
              currN := currN - childLines
              currOff := currOff + length child
              i := i + 1
            return none
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def findNthNewlineLeaf (t : ViE.PieceTree) (n : Nat) (pt : ViE.PieceTable) : Option (ViE.Piece × Nat × Nat) :=
  let fuel := (height t + 4) * 32 + 64
  findNthNewlineLeafCore t n pt 0 fuel

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

private def maximalSuffixLoopCore (x : ByteArray) (useLe : Bool) (m ms j k p : Int) (fuel : Nat) : (Int × Int) :=
  match fuel with
  | 0 => (ms, p)
  | fuel + 1 =>
      if j + k >= m then
        (ms, p)
      else
        let a := x[Int.toNat (j + k)]!
        let b := x[Int.toNat (ms + k)]!
        if useLe then
          if a < b then
            maximalSuffixLoopCore x useLe m ms (j + k) 1 (j + k - ms) fuel
          else if a == b then
            if k != p then
              maximalSuffixLoopCore x useLe m ms j (k + 1) p fuel
            else
              maximalSuffixLoopCore x useLe m ms (j + p) 1 p fuel
          else
            maximalSuffixLoopCore x useLe m j (j + 1) 1 1 fuel
        else
          if a > b then
            maximalSuffixLoopCore x useLe m ms (j + k) 1 (j + k - ms) fuel
          else if a == b then
            if k != p then
              maximalSuffixLoopCore x useLe m ms j (k + 1) p fuel
            else
              maximalSuffixLoopCore x useLe m ms (j + p) 1 p fuel
          else
            maximalSuffixLoopCore x useLe m j (j + 1) 1 1 fuel
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def maximalSuffixLoop (x : ByteArray) (useLe : Bool) (m ms j k p : Int) : (Int × Int) :=
  let mNat := Int.toNat m
  let fuel := (mNat + 1) * (mNat + 1) + 1
  maximalSuffixLoopCore x useLe m ms j k p fuel

def maximalSuffix (x : ByteArray) (useLe : Bool) : (Int × Int) :=
  let m : Int := x.size
  maximalSuffixLoop x useLe m (-1) 0 1 1

private def twoWayForward1Core (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) (fuel : Nat) : Int :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
      if j >= n then
        j
      else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
        twoWayForward1Core haystack needle i n (j + 1) fuel
      else
        j
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def twoWayForward1 (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) : Int :=
  let fuel := Int.toNat (Int.ofNat n - j) + 1
  twoWayForward1Core haystack needle i n j fuel

private def twoWayBackward1Core (haystack needle : ByteArray) (i : Nat) (mem : Int) (j : Int) (fuel : Nat) : Int :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
      if j <= mem then
        j
      else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
        twoWayBackward1Core haystack needle i mem (j - 1) fuel
      else
        j
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def twoWayBackward1 (haystack needle : ByteArray) (i : Nat) (mem : Int) (j : Int) : Int :=
  let fuel := Int.toNat (j - mem) + 1
  twoWayBackward1Core haystack needle i mem j fuel

private def twoWayForward2Core (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) (fuel : Nat) : Int :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
      if j >= n then
        j
      else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
        twoWayForward2Core haystack needle i n (j + 1) fuel
      else
        j
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def twoWayForward2 (haystack needle : ByteArray) (i : Nat) (n : Nat) (j : Int) : Int :=
  let fuel := Int.toNat (Int.ofNat n - j) + 1
  twoWayForward2Core haystack needle i n j fuel

private def twoWayBackward2Core (haystack needle : ByteArray) (i : Nat) (j : Int) (fuel : Nat) : Int :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
      if j < 0 then
        j
      else if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
        twoWayBackward2Core haystack needle i (j - 1) fuel
      else
        j
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def twoWayBackward2 (haystack needle : ByteArray) (i : Nat) (j : Int) : Int :=
  let fuel := Int.toNat (j + 1) + 1
  twoWayBackward2Core haystack needle i j fuel

private def twoWayShortLoopCore (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int) (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
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
            twoWayShortLoopCore haystack needle start maxStart msNat pNat n nextI nextMem fuel
        else
          let shift := Int.toNat (j - Int.ofNat msNat)
          twoWayShortLoopCore haystack needle start maxStart msNat pNat n (i + shift) (-1) fuel
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def twoWayShortLoop (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int) : Option Nat :=
  let fuel := if start <= maxStart then maxStart - start + 2 else 1
  twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem fuel

private def twoWayLongLoopCore (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) (fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
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
            twoWayLongLoopCore haystack needle start maxStart msNat pNat n nextI fuel
        else
          let shift := Int.toNat (j - Int.ofNat msNat)
          twoWayLongLoopCore haystack needle start maxStart msNat pNat n (i + shift) fuel
  termination_by fuel
  decreasing_by
    all_goals exact Nat.lt_succ_self _

def twoWayLongLoop (haystack needle : ByteArray) (start maxStart msNat pNat n : Nat) (i : Nat) : Option Nat :=
  let fuel := if start <= maxStart then maxStart - start + 2 else 1
  twoWayLongLoopCore haystack needle start maxStart msNat pNat n i fuel

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
    let rec loop (i : Nat) (last : Option Nat) (fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => last
      | fuel + 1 =>
          if i > maxStart then last
          else
            match findPatternInBytes haystack needle i with
            | some idx =>
                if idx > maxStart then last
                else loop (idx + 1) (some idx) fuel
            | none => last
    loop 0 none (maxStart + 1)

/-- Search forward for a byte pattern from a given offset -/
private def searchNextCore (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startOffset : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (_cacheMax : Nat) (fuel : Nat)
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
      let rec searchNode (node : ViE.PieceTree) (baseOffset : Nat)
        (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (fuelN : Nat)
        : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
        match fuelN with
        | 0 => (none, cache, order)
        | fuelN + 1 =>
            if baseOffset + length node <= startOffset then
              (none, cache, order)
            else
              match node with
              | ViE.PieceTree.empty => (none, cache, order)
              | ViE.PieceTree.leaf _ _ m =>
                  let relStart := if startOffset > baseOffset then startOffset - baseOffset else 0
                  let remain := length node - relStart
                  let globalStart := baseOffset + relStart
                  let available := total - globalStart
                  let readLen := min (remain + overlap) available
                  if readLen < pattern.size then
                    (none, cache, order)
                  else
                    let crossesBoundary := readLen > remain
                    if !crossesBoundary && !bloomMayContain m.bits hashes then
                      (none, cache, order)
                    else
                      let bytes := getBytes t globalStart readLen pt
                      match findPatternInBytes bytes pattern 0 with
                      | some idx => (some (globalStart + idx), cache, order)
                      | none => (none, cache, order)
              | ViE.PieceTree.internal children _ m =>
                  if !bloomMayContain m.bits hashes then
                    (none, cache, order)
                  else
                    Id.run do
                      let mut i := 0
                      let mut offset := baseOffset
                      let mut cacheAcc := cache
                      let mut orderAcc := order
                      while i < children.size do
                        let child := children[i]!
                        let childLen := length child
                        let childEnd := offset + childLen
                        if childEnd > startOffset then
                          let (res, cache', order') := searchNode child offset cacheAcc orderAcc fuelN
                          cacheAcc := cache'
                          orderAcc := order'
                          match res with
                          | some _ => return (res, cacheAcc, orderAcc)
                          | none => pure ()
                        offset := childEnd
                        i := i + 1
                      return (none, cacheAcc, orderAcc)
      searchNode t 0 cache order fuel

def searchNext (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startOffset : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  let fuel := (height t + 4) * 32 + 64
  searchNextCore t pt pattern startOffset chunkSize useBloom cache order cacheMax fuel

/-- Search backward for a byte pattern ending before startExclusive -/
private def searchPrevCore (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startExclusive : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (_cacheMax : Nat) (fuel : Nat)
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
      let rec searchNode (node : ViE.PieceTree) (baseOffset : Nat)
        (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (fuelN : Nat)
        : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
        match fuelN with
        | 0 => (none, cache, order)
        | fuelN + 1 =>
            if baseOffset >= end0 then
              (none, cache, order)
            else
              match node with
              | ViE.PieceTree.empty => (none, cache, order)
              | ViE.PieceTree.leaf _ _ m =>
                  let relEnd := min (end0 - baseOffset) (length node)
                  let globalEnd := baseOffset + relEnd
                  let globalStart := if baseOffset > overlap then baseOffset - overlap else 0
                  let readLen := globalEnd - globalStart
                  if readLen < pattern.size then
                    (none, cache, order)
                  else
                    let crossesBoundary := globalStart < baseOffset
                    if !crossesBoundary && !bloomMayContain m.bits hashes then
                      (none, cache, order)
                    else
                      let bytes := getBytes t globalStart readLen pt
                      match findLastPatternInBytes bytes pattern with
                      | some idx =>
                          let pos := globalStart + idx
                          if pos < end0 then (some pos, cache, order) else (none, cache, order)
                      | none => (none, cache, order)
              | ViE.PieceTree.internal children _ m =>
                  if !bloomMayContain m.bits hashes then
                    (none, cache, order)
                  else
                    let spans : Array (ViE.PieceTree × Nat) := Id.run do
                      let mut acc : Array (ViE.PieceTree × Nat) := #[]
                      let mut offset := baseOffset
                      for child in children do
                        acc := acc.push (child, offset)
                        offset := offset + length child
                      return acc
                    Id.run do
                      let mut i := 0
                      let mut cacheAcc := cache
                      let mut orderAcc := order
                      while i < spans.size do
                        let j := spans.size - 1 - i
                        let (child, childOffset) := spans[j]!
                        if childOffset < end0 then
                          let (res, cache', order') := searchNode child childOffset cacheAcc orderAcc fuelN
                          cacheAcc := cache'
                          orderAcc := order'
                          match res with
                          | some v =>
                              if v < end0 then
                                return (some v, cacheAcc, orderAcc)
                              pure ()
                          | none => pure ()
                        i := i + 1
                      return (none, cacheAcc, orderAcc)
      searchNode t 0 cache order fuel

def searchPrev (t : ViE.PieceTree) (pt : ViE.PieceTable) (pattern : ByteArray) (startExclusive : Nat) (chunkSize : Nat)
  (useBloom : Bool) (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  let fuel := (height t + 4) * 32 + 64
  searchPrevCore t pt pattern startExclusive chunkSize useBloom cache order cacheMax fuel

end PieceTree

end ViE
