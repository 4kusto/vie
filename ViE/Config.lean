import ViE.State
import ViE.Key.Handler
import ViE.Key.Input

namespace ViE

/-- Parse a character into a list of keys, handling escape sequences statefully. -/
def parseKey (state : EditorState) (c : Char) (currentTime : Nat) : (EditorState × List Key) :=
  ViE.Key.parseKey state c currentTime

/-- Check for escape sequence timeout. -/
def checkTimeout (state : EditorState) (currentTime : Nat) : (EditorState × List Key) :=
  ViE.Key.checkTimeout state currentTime

def enforceScroll (state : EditorState) : EditorState :=
  let (h, w) := state.getActiveWindowScrollBounds
  -- Active window height. Reserve 1 line for status bar?
  -- UI logic reserves 1 for status bar in split rendering.
  let linesInView := if h > 1 then h - 1 else 1

  -- Vertical Scroll
  let (sRow, sCol) := state.getScroll
  let cursor := state.getCursor

  let state :=
    if cursor.row.val < sRow.val then
      state.setScroll cursor.row sCol
    else if cursor.row.val >= sRow.val + linesInView then
      let newScrollRow : Row := ⟨cursor.row.val - linesInView + 1⟩
      state.setScroll newScrollRow sCol
    else
      state

  -- Refresh scroll after potential update
  let (sRow, sCol) := state.getScroll

  -- Horizontal Scroll
  let lnWidth := if state.config.showLineNumbers then 4 else 0
  let colsInView := if w > lnWidth then w - lnWidth else 1

  let state :=
    if cursor.col.val < sCol.val then
      state.setScroll sRow cursor.col
    else if cursor.col.val >= sCol.val + colsInView then
      let newScrollCol : Col := ⟨cursor.col.val - colsInView + 1⟩
      state.setScroll sRow newScrollCol
    else
      state

  state

def update (config : Config) (state : EditorState) (k : Key) : IO EditorState := do
  let newState ← match state.mode with
  | .normal => config.bindings.normal state k
  | .insert => config.bindings.insert state k
  | .command => config.bindings.command state k
  | .searchForward => ViE.Key.handleSearchInput state k
  | .searchBackward => ViE.Key.handleSearchInput state k
  | .visual => config.bindings.visual state k
  | .visualBlock => config.bindings.visualBlock state k

  return enforceScroll newState

end ViE
