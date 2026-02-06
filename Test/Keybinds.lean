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
  match s_x.clipboard with
  | some reg =>
      assertEqual "x register kind" RegisterKind.charwise reg.kind
      assertEqual "x register text" "x" reg.text
  | none => assertEqual "x register set" true false

def testOperators : IO Unit := do
  IO.println "  Testing Operators..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "hello world" ++ [Key.esc] ++ [Key.char '0'])

  -- dw
  let s_dw ← runKeys s1 [Key.char 'd', Key.char 'w']
  assertBuffer "dw deletes word" s_dw "world"
  match s_dw.clipboard with
  | some reg =>
      assertEqual "dw register kind" RegisterKind.charwise reg.kind
      assertEqual "dw register text" "hello " reg.text
  | none => assertEqual "dw register set" true false

  -- cw
  let s_cw ← runKeys s1 [Key.char 'c', Key.char 'w', Key.char 'h', Key.char 'i', Key.esc]
  assertBuffer "cw changes word" s_cw "hi world"

  -- dd
  let s_lines ← runKeys s0 ([Key.char 'i'] ++ keys "line1\nline2\nline3" ++ [Key.esc] ++ keys "ggj")
  let s_dd ← runKeys s_lines [Key.char 'd', Key.char 'd']
  assertBuffer "dd deletes current line" s_dd "line1\nline3"
  match s_dd.clipboard with
  | some reg =>
      assertEqual "dd register kind" RegisterKind.linewise reg.kind
      assertEqual "dd register text" "line2\n" reg.text
  | none => assertEqual "dd register set" true false

  -- yy, p, P
  let s_yy ← runKeys s_lines [Key.char 'g', Key.char 'g', Key.char 'y', Key.char 'y']
  let s_p ← runKeys s_yy [Key.char 'G', Key.char 'p']
  assertBuffer "p pastes below" s_p "line1\nline2\nline3\nline1\n"

  let s_P ← runKeys s_yy [Key.char 'g', Key.char 'g', Key.char 'P']
  assertBuffer "P pastes above" s_P "line1\nline1\nline2\nline3"

  let s_indent ← runKeys s0 ([Key.char 'i'] ++ keys "  indented\nx" ++ [Key.esc] ++ [Key.char 'g', Key.char 'g', Key.char 'y', Key.char 'y', Key.char 'j', Key.char 'p'])
  assertCursor "linewise paste moves to first non-blank" s_indent 2 2

  -- paste should not overwrite register
  let s_reg0 ← runKeys s0 ([Key.char 'i'] ++ keys "one\ntwo" ++ [Key.esc] ++ [Key.char 'g', Key.char 'g', Key.char 'y', Key.char 'y'])
  let regBefore := s_reg0.clipboard
  let s_regP ← runKeys s_reg0 [Key.char 'j', Key.char 'p']
  match (regBefore, s_regP.clipboard) with
  | (some before, some after) =>
      assertEqual "paste keeps register kind" before.kind after.kind
      assertEqual "paste keeps register text" before.text after.text
  | _ => assertEqual "paste keeps register" true false

  -- charwise y/p from normal mode
  let s_char0 ← runKeys s0 ([Key.char 'i'] ++ keys "hello" ++ [Key.esc] ++ [Key.char '0'])
  let s_charY ← runKeys s_char0 [Key.char 'v', Key.char 'l', Key.char 'y']
  let s_charP ← runKeys s_charY [Key.char '$', Key.char 'p']
  assertBuffer "charwise paste in normal mode" s_charP "hellohe"
  assertCursor "charwise paste cursor at end" s_charP 0 6

  let s_charP2 ← runKeys s_charY [Key.char '0', Key.char 'P']
  assertBuffer "charwise P pastes before cursor" s_charP2 "hehello"
  assertCursor "charwise P cursor at end" s_charP2 0 1

def testVisual : IO Unit := do
  IO.println "  Testing Visual Mode..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "highlight me" ++ [Key.esc] ++ [Key.char '0'])

  -- v, d
  let s_v ← runKeys s1 [Key.char 'v', Key.char 'l', Key.char 'd']
  assertBuffer "visual d deletes selection" s_v "ghlight me"
  match s_v.clipboard with
  | some reg =>
      assertEqual "visual d register kind" RegisterKind.charwise reg.kind
      assertEqual "visual d register text" "hi" reg.text
  | none => assertEqual "visual d register set" true false

  -- v, y, p
  let s_vy ← runKeys s1 [Key.char 'v', Key.char 'e', Key.char 'y']
  let s_vyp ← runKeys s_vy [Key.char '$', Key.char 'p']
  assertBuffer "visual y yanks selection" s_vyp "highlight mehighlight"

  let s_char0 ← runKeys s0 ([Key.char 'i'] ++ keys "abc" ++ [Key.esc] ++ [Key.char '0'])
  let s_charY ← runKeys s_char0 [Key.char 'l', Key.char 'v', Key.char 'y']
  let s_charP ← runKeys s_charY [Key.char '$', Key.char 'p']
  assertBuffer "charwise paste appends" s_charP "abcb"
  assertCursor "charwise paste cursor at end" s_charP 0 3

  let s_charP2 ← runKeys s_charY [Key.char '0', Key.char 'P']
  assertBuffer "charwise P inserts before" s_charP2 "babc"
  assertCursor "charwise P cursor at end" s_charP2 0 0

  -- visual block yank/paste cursor position
  let s_blk0 ← runKeys s0 ([Key.char 'i'] ++ keys "abcd\nefgh" ++ [Key.esc] ++ [Key.char 'g', Key.char 'g', Key.char '0'])
  let s_blkY ← runKeys s_blk0 [Key.char 'l', Key.char 'V', Key.char 'l', Key.char 'j', Key.char 'y']
  let s_blkP ← runKeys s_blkY [Key.char 'g', Key.char 'g', Key.char '0', Key.char 'p']
  assertBuffer "visual block y/p inserts block" s_blkP "abcbcd\nefgfgh"
  assertCursor "visual block paste cursor at block start" s_blkP 0 1

  let s_blkP2 ← runKeys s_blkY [Key.char 'g', Key.char 'g', Key.char '0', Key.char 'P']
  assertBuffer "visual block P inserts block" s_blkP2 "bcabcd\nfgefgh"
  assertCursor "visual block P cursor at block start" s_blkP2 0 0

  let s_blkD0 ← runKeys s0 ([Key.char 'i'] ++ keys "abcd\nefgh" ++ [Key.esc] ++ [Key.char 'g', Key.char 'g', Key.char '0'])
  let s_blkD ← runKeys s_blkD0 [Key.char 'l', Key.char 'V', Key.char 'l', Key.char 'j', Key.char 'd']
  assertBuffer "visual block d deletes block" s_blkD "ad\neh"
  match s_blkD.clipboard with
  | some reg =>
      assertEqual "visual block d register kind" RegisterKind.blockwise reg.kind
      assertEqual "visual block d register text" "bc\nfg" reg.text
  | none => assertEqual "visual block d register set" true false

  -- linewise yank/paste (via yy + P)
  let s_line0 ← runKeys s0 ([Key.char 'i'] ++ keys "aa\nbb\ncc" ++ [Key.esc] ++ [Key.char 'g', Key.char 'g'])
  let s_lineY ← runKeys s_line0 [Key.char 'y', Key.char 'y']
  let s_lineP ← runKeys s_lineY [Key.char 'j', Key.char 'P']
  assertBuffer "linewise paste above keeps lines" s_lineP "aa\naa\nbb\ncc"

  let s_lineP2 ← runKeys s_lineY [Key.char 'j', Key.char 'p']
  assertBuffer "linewise paste below keeps lines" s_lineP2 "aa\nbb\naa\ncc"

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

def testSearch : IO Unit := do
  IO.println "  Testing Search..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "hello world\nhello again\n" ++ [Key.esc])

  let s2 ← runKeys s1 ([Key.char '/'] ++ keys "hello" ++ [Key.enter])
  assertCursor "/hello finds first match" s2 0 0

  let s3 ← runKeys s2 [Key.char 'n']
  assertCursor "n finds next match" s3 1 0

  let s4 ← runKeys s3 [Key.char 'N']
  assertCursor "N finds previous match" s4 0 0

  let s5 ← runKeys s4 ([Key.char '?'] ++ keys "world" ++ [Key.enter])
  assertCursor "?world searches backward" s5 0 6

def testCommandSubstitute : IO Unit := do
  IO.println "  Testing Command Substitute..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "foo bar\nfoo baz\nbar foo\n" ++ [Key.esc] ++ keys "gg0")
  let s2 ← runKeys s1 ([Key.char ':'] ++ keys "s/foo/xxx/" ++ [Key.enter])
  assertBuffer ":s replaces first match on current line" s2 "xxx bar\nfoo baz\nbar foo\n"

  let s3 := ViE.initialState
  let s4 ← runKeys s3 ([Key.char 'i'] ++ keys "foo foo\nfoo foo\n" ++ [Key.esc] ++ keys "gg0")
  let s5 ← runKeys s4 ([Key.char ':'] ++ keys "%s/foo/yyy/" ++ [Key.enter])
  assertBuffer ":%s replaces first match per line" s5 "yyy foo\nyyy foo\n"

  let s6 := ViE.initialState
  let s7 ← runKeys s6 ([Key.char 'i'] ++ keys "foo bar\nfoo baz\nbar foo\n" ++ [Key.esc] ++ keys "gg0")
  let s8 ← runKeys s7 ([Key.char ':'] ++ keys "%s/foo/yyy/g" ++ [Key.enter])
  assertBuffer ":%s with g replaces all matches" s8 "yyy bar\nyyy baz\nbar yyy\n"

def testCommandGlobal : IO Unit := do
  IO.println "  Testing Command Global..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "a\nfoo1\nb\nfoo2\n" ++ [Key.esc] ++ keys "gg0")
  let s2 ← runKeys s1 ([Key.char ':'] ++ keys "g/foo/ d" ++ [Key.enter])
  assertBuffer ":g/pat/ d deletes matching lines" s2 "a\nb\n"

  let s3 := ViE.initialState
  let s4 ← runKeys s3 ([Key.char 'i'] ++ keys "foo foo\nbar foo\nfoo bar\n" ++ [Key.esc] ++ keys "gg0")
  let s5 ← runKeys s4 ([Key.char ':'] ++ keys "g/foo/ s/foo/xxx/" ++ [Key.enter])
  assertBuffer ":g/pat/ s replaces first match per line" s5 "xxx foo\nbar xxx\nxxx bar\n"

  let s6 := ViE.initialState
  let s7 ← runKeys s6 ([Key.char 'i'] ++ keys "keep1\nfoo\nkeep2\n" ++ [Key.esc] ++ keys "gg0")
  let s8 ← runKeys s7 ([Key.char ':'] ++ keys "v/foo/ d" ++ [Key.enter])
  assertBuffer ":v/pat/ d deletes non-matching lines" s8 "foo\n"

def testCommandBloom : IO Unit := do
  IO.println "  Testing Command Bloom..."
  let s0 := ViE.initialState
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys "hello bloom\nbloom hello\n" ++ [Key.esc] ++ keys "gg0")
  let s2 ← runKeys s1 ([Key.char ':'] ++ keys "bloom /bloom" ++ [Key.enter])
  assertCursor ":bloom moves to first match" s2 0 6
  let s3 ← runKeys s2 ([Key.char ':'] ++ keys "bloom /nomatch" ++ [Key.enter])
  assertEqual ":bloom not found message" "Pattern not found: nomatch" s3.message

def test : IO Unit := do
  IO.println "Starting Expanded Keybind Tests..."
  testMotions
  testEditing
  testOperators
  testVisual
  testCounted
  testWorkgroupSwitch
  testSearch
  testCommandSubstitute
  testCommandGlobal
  testCommandBloom
  IO.println "All Expanded Keybind Tests passed!"

end Test.Keybinds
