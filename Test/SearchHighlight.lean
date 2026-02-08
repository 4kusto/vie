import ViE.UI
import ViE.Config
import Test.Utils

namespace Test.SearchHighlight

open Test.Utils
open ViE


def test : IO Unit := do
  IO.println "Starting Search Highlight Test..."

  let hitRanges : Array (Nat × Nat) := #[(0, 4), (10, 14), (20, 24)]

  assertEqual "Active match picks cursor candidate" (some (10, 14)) (ViE.UI.activeMatchRange hitRanges (some 11))
  assertEqual "No active match when cursor is outside all matches" none (ViE.UI.activeMatchRange hitRanges (some 5))
  assertEqual "No active match when cursor is none" none (ViE.UI.activeMatchRange hitRanges none)

  let active := ViE.UI.activeMatchRange hitRanges (some 11)
  let activeHead :=
    match active with
    | some m => ViE.UI.overlapsByteRange m 0 1
    | none => false
  let activeBody :=
    match active with
    | some m => ViE.UI.overlapsByteRange m 11 12
    | none => false

  assertEqual "Active candidate does not color other matches" false activeHead
  assertEqual "Active candidate colors only its own range" true activeBody

  let s0 := ViE.startOrUpdateSearch ViE.initialState "abc" .forward false
  let (m1, s1) := ViE.UI.getLineSearchMatches s0 s0.getActiveBuffer.id 0 "abc abc"
  assertEqual "Line search cache computes matches" true (m1.size > 0)
  let cachedBeforeSwitch :=
    match s1.searchState with
    | some ss => ss.lineMatches.contains 0
    | none => false
  assertEqual "Line search cache populated" true cachedBeforeSwitch
  let s2 := ViE.UI.ensureSearchLineCacheForBuffer s1 9999
  let cacheClearedOnSwitch :=
    match s2.searchState with
    | some ss => ss.lineMatches.isEmpty && ss.lineCacheBufferId == some 9999
    | none => false
  assertEqual "Line search cache resets on buffer switch" true cacheClearedOnSwitch

  let t0 := 1000
  let (p0, k0) := ViE.parseKey ViE.initialState '\x1b' t0
  let (p1, k1) := ViE.parseKey p0 '[' (t0 + 1)
  let (p2, k2) := ViE.parseKey p1 '1' (t0 + 2)
  let (p3, k3) := ViE.parseKey p2 ';' (t0 + 3)
  let (p4, k4) := ViE.parseKey p3 '2' (t0 + 4)
  let (p5, k5) := ViE.parseKey p4 'X' (t0 + 5)
  assertEqual "Unknown CSI emits no keys while pending" ([] : List Key) (k0 ++ k1 ++ k2 ++ k3 ++ k4)
  assertEqual "Unknown CSI final emits Key.unknown" [Key.unknown 'X'] k5
  assertEqual "Unknown CSI clears pending state" "" p5.inputState.pendingKeys

  let chars : List Char := ['\x1b', '[', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '1', '2', '3']
  let (pLong, emitted) := chars.foldl
    (fun (acc : EditorState × List Key) ch =>
      let (st, out) := acc
      let (st', keys) := ViE.parseKey st ch (t0 + 20)
      (st', out ++ keys))
    (ViE.initialState, [])
  assertEqual "Overlong unknown CSI flushes emitted keys" true (!emitted.isEmpty)
  assertEqual "Overlong unknown CSI clears pending state" "" pLong.inputState.pendingKeys

end Test.SearchHighlight
