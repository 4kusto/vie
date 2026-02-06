import ViE.Window.Actions
import ViE.State
import ViE.Types
import ViE.Config

namespace Test.Scroll

open ViE

def assert (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    throw (IO.userError s!"Assertion failed: {msg}")

def test : IO Unit := do
  let state := ViE.initialState
  -- Set window size (e.g., 10 lines)
  let state := { state with windowHeight := 10, windowWidth := 80 }

  -- Move cursor to line 100
  let state := state.setCursor { row := ⟨100⟩, col := ⟨0⟩ }

  -- Enforce scroll
  let state := ViE.Window.enforceScroll state

  let (sRow, _) := state.getScroll
  IO.println s!"Cursor Row: 100, Scroll Row: {sRow.val}, Window Height: 10"

  -- View range is [sRow, sRow + 9] (10 lines)
  -- We expect 100 to be in [sRow, sRow + 9]
  -- So sRow <= 100 AND 100 < sRow + 10  => sRow > 90
  let visible := sRow.val <= 100 && 100 < sRow.val + 10
  assert "Cursor is visible" visible

  -- Upper boundary: cursor above scroll should pull scroll up
  let state2 := { state with
    mode := .normal
  }
  let state2 := state2.setScroll ⟨10⟩ ⟨0⟩
  let state2 := state2.setCursor { row := ⟨2⟩, col := ⟨0⟩ }
  let state2 := ViE.Window.enforceScroll state2
  let (sRow2, _) := state2.getScroll
  assert "Scroll moves up to include cursor" (sRow2.val == 2)

  -- Horizontal right boundary: cursor beyond view should scroll right
  let state3 := { state with windowHeight := 5, windowWidth := 20 }
  let state3 := state3.setScroll ⟨0⟩ ⟨0⟩
  let state3 := state3.setCursor { row := ⟨0⟩, col := ⟨30⟩ }
  let state3 := ViE.Window.enforceScroll state3
  let (_, sCol3) := state3.getScroll
  let colsInView := 20 -- showLineNumbers is false by default
  let visible3 := sCol3.val <= 30 && 30 < sCol3.val + colsInView
  assert "Horizontal scroll keeps cursor visible" visible3

  -- Horizontal left boundary: cursor before scroll should pull scroll left
  let state4 := { state with windowHeight := 5, windowWidth := 20 }
  let state4 := state4.setScroll ⟨0⟩ ⟨10⟩
  let state4 := state4.setCursor { row := ⟨0⟩, col := ⟨2⟩ }
  let state4 := ViE.Window.enforceScroll state4
  let (_, sCol4) := state4.getScroll
  assert "Horizontal scroll moves left to include cursor" (sCol4.val == 2)
