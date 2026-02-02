import ViE.Types
import ViE.State.Config
import ViE.Config
import ViE.Key.Map
import ViE.Command.Impl
import Test.Utils

open ViE
open Test.Utils

namespace Test.Integration

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

-- Helper: Convert string to list of char keys
def keys (s : String) : List Key :=
  s.toList.map Key.char

def test : IO Unit := do
  IO.println "Starting Integration Test..."

  -- Test 1: Typing "abc" -> Undo -> Insert "d"
  -- Expected: "abc" -> "" -> "d"
  -- Bug Report: After Undo, Insert mode might fail or buffer might be corrupted

  let s0 := ViE.initialState

  -- 1. Insert "abc"
  -- i a b c Esc
  let input1 := [Key.char 'i'] ++ keys "abc" ++ [Key.esc]
  let s1 ← runKeys s0 input1

  assertBuffer "Text after insert abc" s1 "abc"

  -- 2. Undo
  -- u
  let s2 ← runKeys s1 [Key.char 'u']
  assertBuffer "Text after undo" s2 ""
  assertCursor "Cursor after undo should be (0,0)" s2 0 0

  -- 3. Insert "d"
  -- i d Esc
  let s3 ← runKeys s2 [Key.char 'i', Key.char 'd', Key.esc]

  assertBuffer "Text after re-insert d" s3 "d"
  assertCursor "Cursor after insert 'd' and Esc should be (0,0)" s3 0 0

  IO.println "IntegrationTest passed!"

end Test.Integration
