import ViE.UI.Primitives

namespace ViE.UI
open ViE

/-- Find all occurrences of a byte pattern within a byte array. -/
def findAllMatchesBytes (haystack : ByteArray) (needle : ByteArray) : Array (Nat × Nat) := Id.run do
  let n := needle.size
  let h := haystack.size
  if n == 0 || h < n then
    return #[]

  let limit := h - n + 1
  let mut out : Array (Nat × Nat) := #[]
  for i in [0:limit] do
    let mut matched := true
    for j in [0:n] do
      if matched && haystack[i + j]! != needle[j]! then
        matched := false
    if matched then
      out := out.push (i, i + n)
  return out

def overlapsByteRange (r : Nat × Nat) (byteStart byteEnd : Nat) : Bool :=
  let (s, e) := r
  byteStart < e && byteEnd > s

def activeMatchRange (hitRanges : Array (Nat × Nat)) (cursorByte : Option Nat) : Option (Nat × Nat) :=
  match cursorByte with
  | none => none
  | some cb =>
      let rec loop (i : Nat) : Option (Nat × Nat) :=
        if i >= hitRanges.size then
          none
        else
          let m := hitRanges[i]!
          let (s, e) := m
          if s <= cb && cb < e then
            some m
          else
            loop (i + 1)
      loop 0

def updateSearchLineCache (st : EditorState) (lineIdx : Row) (lineStr : String) (matchRanges : Array (Nat × Nat)) : EditorState :=
  match st.searchState with
  | none => st
  | some ss =>
      let lineMatches := ss.lineMatches.insert lineIdx (lineStr, matchRanges)
      let order :=
        if ss.lineOrder.contains lineIdx then
          ss.lineOrder
        else
          ss.lineOrder.push lineIdx
      let (lineMatches, order) :=
        if order.size > ss.lineCacheMax then
          let dropCount := order.size - ss.lineCacheMax
          let evicted := order.extract 0 dropCount
          let order := order.extract dropCount order.size
          let lineMatches := evicted.foldl (fun acc r => acc.erase r) lineMatches
          (lineMatches, order)
        else
          (lineMatches, order)
      { st with searchState := some { ss with lineMatches := lineMatches, lineOrder := order } }

def ensureSearchLineCacheForBuffer (st : EditorState) (bufferId : Nat) : EditorState :=
  match st.searchState with
  | none => st
  | some ss =>
      if ss.lineCacheBufferId == some bufferId then
        st
      else
        {
          st with
            searchState := some {
              ss with
                lineCacheBufferId := some bufferId
                lineMatches := Lean.RBMap.empty
                lineOrder := #[]
            }
        }

def getLineSearchMatches
    (st : EditorState)
    (bufferId : Nat)
    (lineIdx : Row)
    (lineStr : String)
    : (Array (Nat × Nat) × EditorState) :=
  let st := ensureSearchLineCacheForBuffer st bufferId
  match st.searchState with
  | none => (#[], st)
  | some ss =>
      if ss.pattern.isEmpty then
        (#[], st)
      else
        match ss.lineMatches.find? lineIdx with
        | some (cachedLine, cachedMatches) =>
            if cachedLine == lineStr then
              (cachedMatches, st)
            else
              let matchRanges := findAllMatchesBytes lineStr.toUTF8 ss.pattern.toUTF8
              let st' := updateSearchLineCache st lineIdx lineStr matchRanges
              (matchRanges, st')
        | none =>
            let matchRanges := findAllMatchesBytes lineStr.toUTF8 ss.pattern.toUTF8
            let st' := updateSearchLineCache st lineIdx lineStr matchRanges
            (matchRanges, st')

def prefetchSearchLineMatches
    (st : EditorState)
    (buf : FileBuffer)
    (startRow endRow : Nat)
    : EditorState :=
  let rec loop (row : Nat) (acc : EditorState) : EditorState :=
    if row >= endRow then
      acc
    else if row >= FileBuffer.lineCount buf then
      acc
    else
      let lineIdx : Row := ⟨row⟩
      let lineStr := getLineFromBuffer buf lineIdx |>.getD ""
      let (_, acc') := getLineSearchMatches acc buf.id lineIdx lineStr
      loop (row + 1) acc'
  loop startRow st

end ViE.UI
