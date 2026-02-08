import ViE.State.Config
import ViE.Config
import ViE.Command.Impl
import ViE.Key.Map
import ViE.State.Edit

namespace Test.CursorReproduction

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
  IO.println "Starting Cursor Reproduction Test..."
  let s := ViE.initialState

  -- Scenario: Insert, Undo, Insert
  let s1 := s.insertChar 'a'
  let s1 := s1.commitEdit -- Force separate undo group
  let s2 := s1.insertChar 'b'
  -- Text: 'ab', Cursor: (0, 2)

  let s3 := s2.undo
  -- Text: 'a', Cursor should be (0, 1)
  let cursor := s3.getCursor
  if cursor.col.val != 1 then
     IO.println s!"[FAIL] Undo cursor mismatch. Expected 1, got {cursor.col.val}"
     assert "Undo cursor" false
  else
     IO.println "[PASS] Undo cursor correct"

  -- Scenario: Wide character insert moves cursor by display width
  let s := ViE.initialState
  let wide := Char.ofNat 0x3042 -- Hiragana A (wide)
  let s := s.insertChar wide
  let cursor := s.getCursor
  if cursor.col.val != 2 then
     IO.println s!"[FAIL] Wide char cursor mismatch. Expected 2, got {cursor.col.val}"
     assert "Wide char cursor" false
  else
     IO.println "[PASS] Wide char cursor correct"

  let s4 := s3.insertChar 'c'
  -- Text: 'ac'
  let text := getLineFromBuffer s4.getActiveBuffer 0 |>.getD ""
  if text != "ac" then
      IO.println s!"[FAIL] Insert after undo failed. Expected 'ac', got '{text}'"
      assert "Insert after undo" false
  else
      IO.println "[PASS] Insert after undo works"

  -- Scenario: Paste, Undo, Paste (checking grouping too, but focusing on cursor)
  -- Reset
  let s := ViE.initialState
  let s := s.insertChar 'x'
  let s := s.yankCurrentLine -- Yank 'x\n'
  let _s := s.pasteBelow -- Paste 'x\n' -> 'x\nx\n' ??
  -- PasteBelow pastes line.

  -- Scenario: x command
  let s := ViE.initialState
  let s := s.insertChar 'h'
  let s := s.insertChar 'e'
  let s := s.insertChar 'y'
  -- "hey"
  let s := (s.moveCursorLeft).moveCursorLeft -- At 'h' (0,0)? No: 3 -> 2 -> 1. 'e'
  -- "hey" cursor at 2 ('y'). Left -> 1 ('e'). Left -> 0 ('h').
  -- Actually moveCursorLeft from (0,3) -> (0,2) 'y'.
  -- Let's use setCursor
  let s := s.setCursor (Point.make 0 1) -- 'e'
  let s := s.deleteCharAfterCursor -- Should delete 'e' -> "hy"
  let text := getLineFromBuffer s.getActiveBuffer 0 |>.getD ""
  if text != "hy" then
     IO.println s!"[FAIL] 'x' command (deleteCharAfterCursor) failed. Expected 'hy', got '{text}'"
     assert "x command" false
  else
     IO.println "[PASS] 'x' command works"

  -- Scenario: Insert mode transition + single-char delete keeps line count and cursor in sync.
  let s := ViE.initialState
  let s ← runKeys s [Key.char 'i', Key.enter]
  let c1 := s.getCursor
  assert "Enter in insert creates second line" (s.getActiveBuffer.lineCount == 2)
  assert "Enter in insert moves cursor to next line" (c1.row.val == 1 && c1.col.val == 0)

  let s ← runKeys s [Key.esc]
  let c2 := s.getCursor
  assert "Esc from insert keeps valid cursor row" (c2.row.val < s.getActiveBuffer.lineCount)
  assert "Esc from insert keeps row/col at second line head" (c2.row.val == 1 && c2.col.val == 0)

  -- Re-enter insert and delete one char (the previous newline) via Backspace.
  let s ← runKeys s [Key.char 'i', Key.backspace]
  let c3 := s.getCursor
  assert "Backspace at BOL joins lines" (s.getActiveBuffer.lineCount == 1)
  assert "Backspace at BOL moves cursor to joined line end" (c3.row.val == 0 && c3.col.val == 0)

  -- In normal mode x at empty line is a no-op and must keep cursor valid.
  let s ← runKeys s [Key.esc, Key.char 'x']
  let c4 := s.getCursor
  assert "x on empty line keeps line count" (s.getActiveBuffer.lineCount == 1)
  assert "x on empty line keeps cursor in range" (c4.row.val < s.getActiveBuffer.lineCount)

  IO.println "Cursor Reproduction Test Finished"

end Test.CursorReproduction
