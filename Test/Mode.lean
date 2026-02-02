import ViE.State.Config
import ViE.Config
import ViE.Command.Impl
import ViE.Key.Map
import ViE.State.Edit
import ViE.State.Movement

namespace Test.Mode

open ViE

def assert (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    throw (IO.userError s!"Assertion failed: {msg}")

-- Helper to construct a full Config
def makeTestConfig : Config := {
  settings := ViE.defaultConfig
  commands := ViE.Command.defaultCommandMap
  bindings := ViE.Key.makeKeyMap ViE.Command.defaultCommandMap
}

-- Run a sequence of keys
def runKeys (startState : EditorState) (keys : List Key) : IO EditorState := do
  let config := makeTestConfig
  let mut s := startState
  for k in keys do
    s ← ViE.update config s k
  return s

def test : IO Unit := do
  IO.println "Starting Mode Test..."
  let s := ViE.initialState

  -- Scenario: Insert 'abc' then Esc.
  -- Initial: (0,0)
  -- 'i' -> Insert Mode
  -- 'a' -> "a", (0,1)
  -- 'b' -> "ab", (0,2)
  -- 'c' -> "abc", (0,3)
  -- Esc -> Normal Mode.
  -- Expected Vim behavior: Cursor should move left to (0,2) 'c'.
  -- If empty line "insert a then esc", "a" (0,1) -> (0,0).

  let keys := [Key.char 'i', Key.char 'a', Key.char 'b', Key.char 'c', Key.esc]
  let sEnd ← runKeys s keys

  -- Check Mode
  if sEnd.mode != Mode.normal then
    IO.println s!"[FAIL] Mode mismatch. Expected Normal, got {sEnd.mode}"
    assert "Mode is Normal" false
  else
    IO.println "[PASS] Mode is Normal"

  -- Check Text
  let text := getLineFromBuffer sEnd.getActiveBuffer 0 |>.getD ""
  if text != "abc" then
    IO.println s!"[FAIL] Text mismatch. Expected 'abc', got '{text}'"
    assert "Text is 'abc'" false
  else
     IO.println "[PASS] Text is 'abc'"

  -- Check Cursor
  -- Expect (0, 2)
  let cursor := sEnd.getCursor
  if cursor.col.val != 2 then
    IO.println s!"[FAIL] Cursor mismatch. Expected (0, 2), got ({cursor.row.val}, {cursor.col.val})"
    assert "Cursor moved left on Esc" false
  else
    IO.println "[PASS] Cursor moved left on Esc"

  IO.println "ModeTest passed!"

end Test.Mode
