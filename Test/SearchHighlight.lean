import ViE.UI
import Test.Utils

namespace Test.SearchHighlight

open Test.Utils


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

end Test.SearchHighlight
