import ViE.Types
import ViE.Buffer.Content
import ViE.State.Layout
import ViE.State.Movement

namespace Test.Utils

/-- Assert condition is true, throw error if false -/
def assert (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    throw (IO.userError s!"Assertion failed: {msg}")

/-- Assert equality with debug output -/
def assertEqual [Repr α] [BEq α] (msg : String) (expected actual : α) : IO Unit := do
  if expected == actual then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    IO.println s!"  Expected: {repr expected}"
    IO.println s!"  Actual:   {repr actual}"
    throw (IO.userError s!"Assertion failed: {msg}")

/-- Assert EditorState buffer content matches expected string -/
def assertBuffer (msg : String) (est : ViE.EditorState) (expected : String) : IO Unit := do
  let actual := est.getActiveBuffer.table.toString
  if actual == expected then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    IO.println s!"  Expected: '{expected}'"
    IO.println s!"  Actual:   '{actual}'"
    throw (IO.userError s!"Buffer content assertion failed: {msg}")

/-- Assert EditorState cursor position matches expected row/col -/
def assertCursor (msg : String) (est : ViE.EditorState) (r c : Nat) : IO Unit := do
  let cursor := est.getCursor
  if cursor.row.val == r && cursor.col.val == c then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}"
    IO.println s!"  Expected: ({r}, {c})"
    IO.println s!"  Actual:   ({cursor.row.val}, {cursor.col.val})"
    throw (IO.userError s!"Cursor assertion failed: {msg}")

end Test.Utils
