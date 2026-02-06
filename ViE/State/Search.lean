import ViE.State.Layout
import ViE.State.Movement
import ViE.Types
import ViE.Buffer.Content
import ViE.Data.PieceTable
import ViE.Data.PieceTable.Tree

namespace ViE

def searchChunkSize : Nat := 8192
def incrementalSearchDebounceMs : Nat := 120

def updateSearchCache (state : SearchState) (offset : Nat) : SearchState :=
  let cache := state.cache.push offset
  let cache :=
    if cache.size > state.cacheMax then
      cache.extract (cache.size - state.cacheMax) cache.size
    else
      cache
  { state with cache := cache }

def getCursorOffset (s : EditorState) : Nat :=
  let buf := s.getActiveBuffer
  let cursor := s.getCursor
  ViE.getOffsetFromPointInBuffer buf cursor.row.val cursor.col.val |>.getD 0

def applyMatchOffset (s : EditorState) (offset : Nat) : EditorState :=
  let buf := s.getActiveBuffer
  let (r, c) := buf.table.getPointFromOffset offset
  s.setCursor { row := ⟨r⟩, col := ⟨c⟩ }

def startSearch (s : EditorState) (pattern : String) (direction : SearchDirection) (useBloom : Bool) : EditorState :=
  let cursorOffset := getCursorOffset s
  let search : SearchState := {
    pattern := pattern
    direction := direction
    useBloom := useBloom
    lastMatch := none
    lastSearchOffset := cursorOffset
    cache := #[]
    cacheMax := 128
    lineMatches := Lean.RBMap.empty
    lineOrder := #[]
    lineCacheMax := 512
    bloomCache := Lean.RBMap.empty
    bloomOrder := #[]
    bloomCacheMax := s.config.searchBloomCacheMax
  }
  { s with searchState := some search }

def startOrUpdateSearch (s : EditorState) (pattern : String) (direction : SearchDirection) (useBloom : Bool) : EditorState :=
  match s.searchState with
  | none => startSearch s pattern direction useBloom
  | some st =>
      let cursorOffset := getCursorOffset s
      let st' := {
        st with
          pattern := pattern
          direction := direction
          useBloom := useBloom
          lastMatch := none
          lastSearchOffset := cursorOffset
          cache := #[]
          lineMatches := Lean.RBMap.empty
          lineOrder := #[]
      }
      { s with searchState := some st' }

def searchNextOffset (pt : PieceTable) (pattern : ByteArray) (startOffset : Nat) (useBloom : Bool)
  (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  PieceTree.searchNext pt.tree pt pattern startOffset searchChunkSize useBloom cache order cacheMax

def searchPrevOffset (pt : PieceTable) (pattern : ByteArray) (startExclusive : Nat) (useBloom : Bool)
  (cache : Lean.RBMap Nat ByteArray compare) (order : Array Nat) (cacheMax : Nat)
  : (Option Nat × Lean.RBMap Nat ByteArray compare × Array Nat) :=
  PieceTree.searchPrev pt.tree pt pattern startExclusive searchChunkSize useBloom cache order cacheMax

def findNextMatch (s : EditorState) (directionOverride : Option SearchDirection := none) : EditorState :=
  match s.searchState with
  | none => { s with message := "No search pattern" }
  | some st =>
    let direction := directionOverride.getD st.direction
    if st.pattern.isEmpty then
      { s with message := "Empty search pattern" }
    else
      let pt := s.getActiveBuffer.table
      let patBytes := st.pattern.toUTF8
      let startOffset :=
        match direction with
        | .forward =>
          match st.lastMatch with
          | some m => m + 1
          | none => getCursorOffset s
        | .backward =>
          match st.lastMatch with
          | some m => m
          | none => getCursorOffset s
      let useBloom := st.useBloom && patBytes.size >= 3
      let (result, bloomCache, bloomOrder) :=
        match direction with
        | .forward => searchNextOffset pt patBytes startOffset useBloom st.bloomCache st.bloomOrder st.bloomCacheMax
        | .backward => searchPrevOffset pt patBytes startOffset useBloom st.bloomCache st.bloomOrder st.bloomCacheMax
      let (result, wrapped, bloomCache, bloomOrder) :=
        match result, direction with
        | some r, _ => (some r, false, bloomCache, bloomOrder)
        | none, .forward =>
            if startOffset > 0 then
              let (r2, c2, o2) := searchNextOffset pt patBytes 0 useBloom bloomCache bloomOrder st.bloomCacheMax
              (r2, true, c2, o2)
            else
              (none, false, bloomCache, bloomOrder)
        | none, .backward =>
            let total := pt.tree.length
            if startOffset < total then
              let (r2, c2, o2) := searchPrevOffset pt patBytes total useBloom bloomCache bloomOrder st.bloomCacheMax
              (r2, true, c2, o2)
            else
              (none, false, bloomCache, bloomOrder)
      match result with
      | none =>
          let st' := { st with bloomCache := bloomCache, bloomOrder := bloomOrder }
          { s with searchState := some st', message := s!"Pattern not found: {st.pattern}" }
      | some off =>
          let s' := applyMatchOffset s off
          let st' := updateSearchCache { st with lastMatch := some off, bloomCache := bloomCache, bloomOrder := bloomOrder } off
          let st'' := { st' with direction := direction }
          let bloomTag := if useBloom then " [bloom]" else ""
          let msg :=
            if wrapped then
              s!"Wrapped: {st.pattern}{bloomTag}"
            else
              s!"Match: {st.pattern}{bloomTag}"
          { s' with searchState := some st'', message := msg }

def runIncrementalSearch (s : EditorState) : EditorState :=
  if s.mode != .searchForward && s.mode != .searchBackward then
    s
  else
    let pattern := s.inputState.commandBuffer
    if pattern.isEmpty then
      s
    else
      let direction := if s.mode == .searchBackward then SearchDirection.backward else SearchDirection.forward
      let s' := startOrUpdateSearch s pattern direction false
      findNextMatch s' (some direction)

def maybeRunIncrementalSearch (s : EditorState) (now : Nat) : EditorState :=
  if s.inputState.pendingSearch && now - s.inputState.lastSearchInputTime >= incrementalSearchDebounceMs then
    let s' := runIncrementalSearch s
    { s' with
      dirty := true
      inputState := { s'.inputState with pendingSearch := false, lastSearchRunTime := now }
    }
  else
    s

end ViE
