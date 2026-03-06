import ViE.UI.Primitives
import Bliku.Tui.Search

namespace ViE.UI
open ViE

abbrev findAllMatchesBytes := Bliku.Tui.findAllMatchesBytes
abbrev overlapsByteRange := Bliku.Tui.overlapsByteRange
abbrev activeMatchRange := Bliku.Tui.activeMatchRange

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
