import ViE.State.Movement
import ViE.State.Edit
import ViE.Key.Map
import ViE.Types
import ViE.Buffer.Content
import ViE.Config
import ViE.Command.Impl
import Test.Utils

namespace Test.Keybinds

open ViE
open Test.Utils

def makeTestConfig : Config := {
  settings := ViE.defaultConfig
  commands := ViE.Command.defaultCommandMap
  bindings := ViE.Key.makeKeyMap ViE.Command.defaultCommandMap
}

def keys (s : String) : List Key :=
  s.toList.map fun c =>
    if c == '\n' then Key.enter else Key.char c

def runKeys (s : EditorState) (ks : List Key) : IO EditorState := do
  let config := makeTestConfig
  ks.foldlM (fun s k => ViE.update config s k) s

def testMotions : IO Unit := do
  IO.println "  Testing Motions..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "line1\nline2\nline3" ++ [Key.esc] ++ keys "gg0")
  -- "line1\nline2\nline3" cursor at (0,0)

  -- l, h
  let s_l ← runKeys s1 [Key.char 'l']
  assertCursor "l moves right" s_l 0 1

  let s_lh ← runKeys s_l [Key.char 'h']
  assertCursor "h moves left" s_lh 0 0

  -- j, k
  let s_j ← runKeys s1 [Key.char 'j']
  assertCursor "j moves down" s_j 1 0

  let s_jk ← runKeys s_j [Key.char 'k']
  assertCursor "k moves up" s_jk 0 0

  -- 0, $
  let s_end ← runKeys s1 [Key.char '$']
  assertCursor "$ moves to end" s_end 0 4 -- '1' is at col 4

  let s_start ← runKeys s_end [Key.char '0']
  assertCursor "0 moves to start" s_start 0 0

  -- w, b, e
  let s_text ← runKeys s0 ([Key.char 'i'] ++ keys "word1 word2" ++ [Key.esc] ++ [Key.char '0'])
  let s_w ← runKeys s_text [Key.char 'w']
  assertCursor "w moves to next word" s_w 0 6

  let s_e ← runKeys s_text [Key.char 'e']
  assertCursor "e moves to end of word" s_e 0 4

  let s_we ← runKeys s_w [Key.char 'e']
  assertCursor "we moves to end of next word" s_we 0 10

  let s_web ← runKeys s_we [Key.char 'b']
  assertCursor "b moves to start of word" s_web 0 6

  -- gg, G
  let s_G ← runKeys s1 [Key.char 'G']
  assertCursor "G moves to last line" s_G 2 0

  let s_gg ← runKeys s_G [Key.char 'g', Key.char 'g']
  assertCursor "gg moves to first line" s_gg 0 0

  -- | (jump to column)
  let s_pipe ← runKeys s1 [Key.char '3', Key.char '|']
  assertCursor "| jumps to column" s_pipe 0 2 -- 1-indexed count 3 -> col 2

def testEditing : IO Unit := do
  IO.println "  Testing Editing..."
  let s0 := ViE.initialState

  -- i, a, A
  let s_i ← runKeys s0 [Key.char 'i', Key.char 'x', Key.esc]
  assertBuffer "i inserts" s_i "x"

  let s_a ← runKeys s_i [Key.char 'a', Key.char 'y', Key.esc]
  assertBuffer "a appends" s_a "xy"

  let s_A ← runKeys s_a [Key.char '0', Key.char 'A', Key.char 'z', Key.esc]
  assertBuffer "A appends at end" s_A "xyz"

  -- o, O
  let s_o ← runKeys s_i [Key.char 'o', Key.char 'y', Key.esc]
  assertBuffer "o inserts line below" s_o "x\ny"

  let s_O ← runKeys s_o [Key.char 'k', Key.char 'O', Key.char 'z', Key.esc]
  assertBuffer "O inserts line above" s_O "z\nx\ny"

  -- x
  let s_x ← runKeys s_i [Key.char 'x']
  assertBuffer "x deletes char" s_x ""

def testOperators : IO Unit := do
  IO.println "  Testing Operators..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "hello world" ++ [Key.esc] ++ [Key.char '0'])

  -- dw
  let s_dw ← runKeys s1 [Key.char 'd', Key.char 'w']
  assertBuffer "dw deletes word" s_dw "world"

  -- cw
  let s_cw ← runKeys s1 [Key.char 'c', Key.char 'w', Key.char 'h', Key.char 'i', Key.esc]
  assertBuffer "cw changes word" s_cw "hi world"

  -- dd
  let s_lines ← runKeys s0 ([Key.char 'i'] ++ keys "line1\nline2\nline3" ++ [Key.esc] ++ keys "ggj")
  let s_dd ← runKeys s_lines [Key.char 'd', Key.char 'd']
  assertBuffer "dd deletes current line" s_dd "line1\nline3"

  -- yy, p, P
  let s_yy ← runKeys s_lines [Key.char 'g', Key.char 'g', Key.char 'y', Key.char 'y']
  let s_p ← runKeys s_yy [Key.char 'G', Key.char 'p']
  assertBuffer "p pastes below" s_p "line1\nline2\nline3\nline1\n"

  let s_P ← runKeys s_yy [Key.char 'g', Key.char 'g', Key.char 'P']
  assertBuffer "P pastes above" s_P "line1\nline1\nline2\nline3"

def testVisual : IO Unit := do
  IO.println "  Testing Visual Mode..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "highlight me" ++ [Key.esc] ++ [Key.char '0'])

  -- v, d
  let s_v ← runKeys s1 [Key.char 'v', Key.char 'l', Key.char 'd']
  assertBuffer "visual d deletes selection" s_v "ghlight me"

  -- v, y, p
  let s_vy ← runKeys s1 [Key.char 'v', Key.char 'e', Key.char 'y']
  let s_vyp ← runKeys s_vy [Key.char '$', Key.char 'p']
  assertBuffer "visual y yanks selection" s_vyp "highlight me\nhighlight"

def testCounted : IO Unit := do
  IO.println "  Testing Counted Actions..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "a b c d e" ++ [Key.esc] ++ [Key.char '0'])

  -- 3w
  let s_3w ← runKeys s1 [Key.char '3', Key.char 'w']
  assertCursor "3w moves 3 words" s_3w 0 6

  -- 2j
  let s_lines ← runKeys s0 ([Key.char 'i'] ++ keys "1\n2\n3\n4" ++ [Key.esc] ++ [Key.char 'g', Key.char 'g'])
  let s_2j ← runKeys s_lines [Key.char '2', Key.char 'j']
  assertCursor "2j moves 2 lines down" s_2j 2 0

def testWorkgroupSwitch : IO Unit := do
  IO.println "  Testing Workgroup Switching..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 [Key.alt '3']
  assertEqual "Alt-3 switches workgroup" 3 s1.currentGroup
  let s2 ← runKeys s1 [Key.alt '0']
  assertEqual "Alt-0 switches workgroup" 0 s2.currentGroup

def test : IO Unit := do
  IO.println "Starting Expanded Keybind Tests..."
  testMotions
  testEditing
  testOperators
  testVisual
  testCounted
  testWorkgroupSwitch
  IO.println "All Expanded Keybind Tests passed!"

end Test.Keybinds
