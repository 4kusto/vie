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

def findEntryIndex (entries : List FileEntry) (name : String) : Option Nat :=
  let rec loop (rest : List FileEntry) (idx : Nat) : Option Nat :=
    match rest with
    | [] => none
    | e :: tail =>
        if e.name == name then
          some idx
        else
          loop tail (idx + 1)
  loop entries 0

def findEntryIndexByPath (entries : List FileEntry) (path : String) : Option Nat :=
  let rec loop (rest : List FileEntry) (idx : Nat) : Option Nat :=
    match rest with
    | [] => none
    | e :: tail =>
        if e.path == path then
          some idx
        else
          loop tail (idx + 1)
  loop entries 0

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

  let s_tab_insert ← runKeys s0 [Key.char 'i', Key.char '\t']
  assertCursor "Tab advances cursor to next tab stop in insert mode" s_tab_insert 0 4

  let s_tab_backspace ← runKeys s0 [Key.char 'i', Key.char '\t', Key.backspace]
  assertBuffer "Tab backspace deletes tab in insert mode" s_tab_backspace ""
  assertCursor "Tab backspace restores cursor column" s_tab_backspace 0 0

  let s_tab ← runKeys s0 [Key.char 'i', Key.char '\t', Key.esc]
  assertBuffer "Tab inserts in insert mode" s_tab "\t"
  assertCursor "Esc after tab returns to tab char in normal mode" s_tab 0 0

  let s0_tab8 := { s0 with config := { s0.config with tabStop := 8 } }
  let s_tab8 ← runKeys s0_tab8 [Key.char 'i', Key.char '\t']
  assertCursor "Tab follows custom tabStop in insert mode" s_tab8 0 8

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

def testVimCompatMotions : IO Unit := do
  IO.println "  Testing Vim Compatibility Motions..."
  let s0 := { ViE.initialState with windowHeight := 12, windowWidth := 80 }
  let lines := String.intercalate "\n" ((List.range 30).map (fun i => s!"  line{i}")) ++ "\n"
  let s1 ← runKeys s0 ([Key.char 'i'] ++ keys lines ++ [Key.esc] ++ keys "gg0")

  let sCd ← runKeys s1 [Key.ctrl 'd']
  assertCursor "Ctrl-d scrolls half page down" sCd 5 0

  let sCu ← runKeys sCd [Key.ctrl 'u']
  assertCursor "Ctrl-u scrolls half page up" sCu 0 0

  let sCf ← runKeys s1 [Key.ctrl 'f']
  assertCursor "Ctrl-f scrolls one page down" sCf 10 0

  let sCb ← runKeys sCf [Key.ctrl 'b']
  assertCursor "Ctrl-b scrolls one page up" sCb 0 0

  let sCe ← runKeys s1 [Key.ctrl 'e']
  let (ceRow, _) := sCe.getScroll
  assertEqual "Ctrl-e scrolls window down by one line" 1 ceRow.val

  let sCy ← runKeys sCe [Key.ctrl 'y']
  let (cyRow, _) := sCy.getScroll
  assertEqual "Ctrl-y scrolls window up by one line" 0 cyRow.val

  let sH ← runKeys sCf [Key.char 'H']
  assertCursor "H moves to top line of screen" sH 10 2

  let sM ← runKeys sCf [Key.char 'M']
  assertCursor "M moves to middle line of screen" sM 15 2

  let sL ← runKeys sCf [Key.char 'L']
  assertCursor "L moves to bottom line of screen" sL 19 2

  let sF0 ← runKeys s0 ([Key.char 'i'] ++ keys "abcaXcaYca" ++ [Key.esc] ++ [Key.char '0'])
  let sF1 ← runKeys sF0 [Key.char 'f', Key.char 'a']
  assertCursor "fa finds next character" sF1 0 3
  let sF2 ← runKeys sF1 [Key.char ';']
  assertCursor "; repeats last f motion" sF2 0 6
  let sF3 ← runKeys sF2 [Key.char ',']
  assertCursor ", reverses last f motion" sF3 0 3
  let sT1 ← runKeys sF3 [Key.char 't', Key.char 'a']
  assertCursor "ta moves before target" sT1 0 5
  let sT2 ← runKeys sT1 [Key.char ';']
  assertCursor "; repeats last t motion" sT2 0 8

  let sPct0 ← runKeys s0 ([Key.char 'i'] ++ keys "(a[b]c)" ++ [Key.esc] ++ [Key.char '0'])
  let sPct1 ← runKeys sPct0 [Key.char '%']
  assertCursor "% jumps to matching bracket" sPct1 0 6
  let sPct2 ← runKeys sPct1 [Key.ctrl 'o']
  assertCursor "Ctrl-o jumps back in jump list" sPct2 0 0
  let sPct3 ← runKeys sPct2 [Key.char '\t']
  assertCursor "Ctrl-i (Tab) jumps forward in jump list" sPct3 0 6

  let sStar0 := ViE.initialState
  let sStar1 ← runKeys sStar0 ([Key.char 'i'] ++ keys "foo bar\nfoo baz\nbar foo\n" ++ [Key.esc] ++ keys "gg0")
  let sStar2 ← runKeys sStar1 [Key.char '*']
  assertCursor "* searches next word under cursor" sStar2 1 0
  let sStar3 ← runKeys sStar2 [Key.char '#']
  assertCursor "# searches previous word under cursor" sStar3 0 0

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

  let s2Prompt ← runKeys s2 [Key.char '/']
  let promptCleared :=
    match s2Prompt.searchState with
    | none => true
    | some _ => false
  assertEqual "Starting new search prompt clears old search highlight state" true promptCleared

  let s2e ← runKeys s2 [Key.enter]
  assertCursor "Enter after search jumps to next match" s2e 1 0
  assertBuffer "Enter after search does not insert newline" s2e "hello world\nhello again\n"

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

def testUiCommands : IO Unit := do
  IO.println "  Testing UI Commands..."
  let s0 := ViE.initialState

  let s1 ← runKeys s0 ([Key.char ':'] ++ keys "float hello" ++ [Key.enter])
  assertEqual ":float shows overlay" true s1.floatingOverlay.isSome

  let s2 ← runKeys s1 [Key.esc]
  assertEqual "Esc closes overlay" false s2.floatingOverlay.isSome

  let s3 ← runKeys s0 ([Key.char ':'] ++ keys "float alpha\\nbeta" ++ [Key.enter])
  match s3.floatingOverlay with
  | some overlay =>
      assertEqual ":float parses newline escape (line count)" 2 overlay.lines.size
      assertEqual ":float parses newline escape (line 1)" "alpha" overlay.lines[0]!
      assertEqual ":float parses newline escape (line 2)" "beta" overlay.lines[1]!
  | none =>
      assertEqual ":float newline overlay exists" true false

  let s4 ← runKeys s3 ([Key.char ':'] ++ keys "nofloat" ++ [Key.enter])
  assertEqual ":nofloat clears overlay" false s4.floatingOverlay.isSome

  let s5 ← runKeys s0 ([Key.char ':'] ++ keys "redraw" ++ [Key.enter])
  assertEqual ":redraw sets message" "redraw" s5.message
  assertEqual ":redraw marks dirty" true s5.dirty

  let s6 ← runKeys s0 ([Key.char ':'] ++ keys "redraw!" ++ [Key.enter])
  assertEqual ":redraw! alias works" "redraw" s6.message

  let s7 ← runKeys s0 [Key.ctrl 'l']
  assertEqual "Ctrl-l redraw marks dirty" true s7.dirty

  let s8 ← runKeys s0 ([Key.char ':'] ++ keys "float --title Note --width 32 hello world" ++ [Key.enter])
  match s8.floatingOverlay with
  | some overlay =>
      assertEqual ":float --title sets title" "Note" overlay.title
      assertEqual ":float --width sets width" 32 overlay.maxWidth
      assertEqual ":float with options keeps text" "hello world" overlay.lines[0]!
  | none =>
      assertEqual ":float with options shows overlay" true false

  let s9 ← runKeys s0 ([Key.char ':'] ++ keys "float --title=Panel --width=28 hi" ++ [Key.enter])
  match s9.floatingOverlay with
  | some overlay =>
      assertEqual ":float --title= sets title" "Panel" overlay.title
      assertEqual ":float --width= sets width" 28 overlay.maxWidth
  | none =>
      assertEqual ":float with inline options shows overlay" true false

  let s10 ← runKeys s0 ([Key.char ':'] ++ keys "float --width nope hi" ++ [Key.enter])
  assertEqual ":float invalid width message" "Invalid float width: nope" s10.message

  let s11 ← runKeys s0 ([Key.char 'i'] ++ keys "abc" ++ [Key.esc] ++ [Key.char ':'] ++ keys "float guard" ++ [Key.enter])
  let s12 ← runKeys s11 [Key.char 'i']
  assertEqual "floating overlay enters insert mode" Mode.insert s12.mode
  let s13 ← runKeys s12 (keys "X" ++ [Key.enter] ++ keys "Y")
  match s13.floatingOverlay with
  | some overlay =>
      assertEqual "floating overlay writes text" "guardX" overlay.lines[0]!
      assertEqual "floating overlay writes next line" "Y" overlay.lines[1]!
  | none =>
      assertEqual "floating overlay remains open while editing" true false
  let s14 ← runKeys s13 [Key.esc]
  assertEqual "Esc exits floating overlay insert mode" Mode.normal s14.mode
  let s15 ← runKeys s14 [Key.enter]
  assertEqual "Enter closes floating overlay" false s15.floatingOverlay.isSome

  let sMsg0 := { s0 with message := "Error: sample message", dirty := true }
  let sMsg1 ← runKeys sMsg0 [Key.enter]
  assertEqual "Enter closes message float" "" sMsg1.message

  let sMsg2 := { s0 with message := "Cannot write preview buffer", dirty := true }
  let sMsg3 ← runKeys sMsg2 [Key.esc]
  assertEqual "Esc closes message float" "" sMsg3.message

  let sPrompt0 ← runKeys s0 ([Key.char ':'] ++ keys "ws list" ++ [Key.enter])
  let sPrompt1 := sPrompt0.updateActiveView fun v => { v with cursor := { row := ⟨2⟩, col := 0 } }
  let sPrompt2 ← runKeys sPrompt1 [Key.enter]
  assertEqual "Workspace explorer New opens floating input" true sPrompt2.floatingOverlay.isSome
  assertEqual "Workspace explorer New sets floating command prefix" (some "ws new ") sPrompt2.floatingInputCommand
  let sPrompt3 ← runKeys sPrompt2 (keys "TmpWS" ++ [Key.enter])
  assertEqual "Workspace explorer floating input submits with Enter" "TmpWS" sPrompt3.getCurrentWorkspace.name
  assertEqual "Workspace explorer floating input closes after submit" false sPrompt3.floatingOverlay.isSome

  let sWsCmd0 ← runKeys s0 ([Key.char ':'] ++ keys "ws new" ++ [Key.enter])
  assertEqual ":ws new opens floating input" true sWsCmd0.floatingOverlay.isSome
  assertEqual ":ws new floating command prefix" (some "ws new ") sWsCmd0.floatingInputCommand
  let sWsCmd1 ← runKeys sWsCmd0 (keys "CmdWorkspace" ++ [Key.enter])
  assertEqual ":ws new floating input submits name" "CmdWorkspace" sWsCmd1.getCurrentWorkspace.name

  let sWgCmd0 ← runKeys s0 ([Key.char ':'] ++ keys "wg new" ++ [Key.enter])
  assertEqual ":wg new opens floating input" true sWgCmd0.floatingOverlay.isSome
  assertEqual ":wg new floating command prefix" (some "wg new ") sWgCmd0.floatingInputCommand
  let sWgCmd1 ← runKeys sWgCmd0 (keys "CmdGroup" ++ [Key.enter])
  assertEqual ":wg new floating input submits name" "CmdGroup" sWgCmd1.getCurrentWorkgroup.name

  let stamp ← IO.monoMsNow
  let tmpRoot := s!"/tmp/vie-explorer-create-{stamp}"
  IO.FS.createDirAll tmpRoot
  let sExp0 := { s0 with windowHeight := 30, windowWidth := 100 }
  let sExp1 ← runKeys sExp0 ([Key.char ':'] ++ keys s!"ex list {tmpRoot}" ++ [Key.enter])
  let explorerOpt := sExp1.explorers.find? (fun (id, _) => id == sExp1.getActiveBuffer.id)
  match explorerOpt with
  | none =>
      assertEqual "Explorer create test has active explorer" true false
  | some (_, explorer) =>
      let newFileIdx := (findEntryIndex explorer.entries "[New File]").getD 0
      let sExp2 := sExp1.updateActiveView fun v => { v with cursor := { row := ⟨2 + newFileIdx⟩, col := 0 } }
      let sExp3 ← runKeys sExp2 [Key.enter]
      assertEqual "Explorer [New File] opens floating input" true sExp3.floatingOverlay.isSome
      assertEqual "Explorer [New File] sets command prefix" (some s!"mkfile {tmpRoot}/") sExp3.floatingInputCommand
      let sExp4 ← runKeys sExp3 (keys "alpha.txt" ++ [Key.enter])
      let fileCreated ← (System.FilePath.mk s!"{tmpRoot}/alpha.txt").pathExists
      assertEqual "Explorer [New File] creates file" true fileCreated
      let explorerOpt2 := sExp4.explorers.find? (fun (id, _) => id == sExp4.getActiveBuffer.id)
      match explorerOpt2 with
      | none =>
          assertEqual "Explorer refreshed after file create" true false
      | some (_, explorer2) =>
          assertEqual "Explorer list includes created file" true (findEntryIndex explorer2.entries "alpha.txt").isSome

      let newDirIdx := (findEntryIndex explorer.entries "[New Directory]").getD 1
      let sExp5 := sExp4.updateActiveView fun v => { v with cursor := { row := ⟨2 + newDirIdx⟩, col := 0 } }
      let sExp6 ← runKeys sExp5 [Key.enter]
      assertEqual "Explorer [New Directory] opens floating input" true sExp6.floatingOverlay.isSome
      assertEqual "Explorer [New Directory] sets command prefix" (some s!"mkdir {tmpRoot}/") sExp6.floatingInputCommand
      let sExp7 ← runKeys sExp6 (keys "subdir" ++ [Key.enter])
      let createdDirPath := System.FilePath.mk s!"{tmpRoot}/subdir"
      let dirExists ← createdDirPath.pathExists
      let dirIsDir ← if dirExists then createdDirPath.isDir else pure false
      assertEqual "Explorer [New Directory] creates directory" true dirIsDir
      let explorerOpt3 := sExp7.explorers.find? (fun (id, _) => id == sExp7.getActiveBuffer.id)
      match explorerOpt3 with
      | none =>
          assertEqual "Explorer refreshed after directory create" true false
      | some (_, explorer3) =>
          assertEqual "Explorer list includes created directory" true (findEntryIndex explorer3.entries "subdir").isSome

  let s16 ← runKeys s0 ([Key.char ':'] ++ keys "vs" ++ [Key.enter])
  let ws16 := s16.getCurrentWorkspace
  assertEqual "split creates second window" true (ws16.nextWindowId >= 2)

  let s17 ← runKeys s16 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let ws17 := s17.getCurrentWorkspace
  assertEqual ":floatwin on marks active window floating" true (ws17.isFloatingWindow ws17.activeWindowId)

  let s18 ← runKeys s17 ([Key.char ':'] ++ keys "floatwin off" ++ [Key.enter])
  let ws18 := s18.getCurrentWorkspace
  assertEqual ":floatwin off clears floating flag" false (ws18.isFloatingWindow ws18.activeWindowId)

  let s19 ← runKeys s18 ([Key.char ':'] ++ keys "floatwin" ++ [Key.enter])
  let ws19 := s19.getCurrentWorkspace
  assertEqual ":floatwin toggles floating flag" true (ws19.isFloatingWindow ws19.activeWindowId)

  let sFloatMove0 := { s0 with windowHeight := 24, windowWidth := 80 }
  let sFloatMove1 ← runKeys sFloatMove0 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let floatMoveId := sFloatMove1.getCurrentWorkspace.activeWindowId
  let beforeFloatMove := sFloatMove1.getFloatingWindowBounds floatMoveId
  let sFloatMove2 ← runKeys sFloatMove1 [Key.alt 'L']
  let afterFloatMove := sFloatMove2.getFloatingWindowBounds floatMoveId
  match beforeFloatMove, afterFloatMove with
  | some (_, left0, _, _), some (_, left1, _, _) =>
      assertEqual "Alt-Shift-l moves floating window right" (left0 + 1) left1
  | _, _ =>
      assertEqual "Alt-Shift-l moves floating window right" true false

  let sFloatMoveGrp0 := { s0 with windowHeight := 24, windowWidth := 80 }
  let sFloatMoveGrp1 ← runKeys sFloatMoveGrp0 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let sFloatMoveGrp2 ← runKeys sFloatMoveGrp1 ([Key.char ':'] ++ keys "vsplit" ++ [Key.enter])
  let moveGrpIds := sFloatMoveGrp2.getCurrentWorkspace.getFloatingWindowIds.toList
  let beforeGrp := moveGrpIds.filterMap (fun wid => (sFloatMoveGrp2.getFloatingWindowBounds wid).map (fun b => (wid, b)))
  let sFloatMoveGrp3 ← runKeys sFloatMoveGrp2 [Key.alt 'J']
  let afterGrp := moveGrpIds.filterMap (fun wid => (sFloatMoveGrp3.getFloatingWindowBounds wid).map (fun b => (wid, b)))
  let movedAllDown :=
    moveGrpIds.all (fun wid =>
      match beforeGrp.find? (fun (id, _) => id == wid), afterGrp.find? (fun (id, _) => id == wid) with
      | some (_, (top0, _, _, _)), some (_, (top1, _, _, _)) => top1 == top0 + 1
      | _, _ => false)
  assertEqual "Alt-Shift-j moves all panes in active floating subtree down" true movedAllDown

  let sFloatVs0 := { s0 with windowHeight := 24, windowWidth := 80 }
  let sFloatVs1 ← runKeys sFloatVs0 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let sFloatVs2 ← runKeys sFloatVs1 ([Key.char ':'] ++ keys "vsplit" ++ [Key.enter])
  let wsFloatVs2 := sFloatVs2.getCurrentWorkspace
  let floatingIdsVs := wsFloatVs2.getFloatingWindowIds.toList
  assertEqual "vsplit in floating window keeps new pane floating" true (floatingIdsVs.length >= 2)
  match floatingIdsVs with
  | a :: b :: _ =>
      let sideBySide :=
        match sFloatVs2.getFloatingWindowBounds a, sFloatVs2.getFloatingWindowBounds b with
        | some (t1, l1, h1, w1), some (t2, l2, h2, w2) =>
            t1 == t2 && h1 == h2 && ((l1 + w1 == l2) || (l2 + w2 == l1))
        | _, _ => false
      assertEqual "vsplit in floating window keeps pair side-by-side" true sideBySide
  | _ =>
      assertEqual "vsplit in floating window keeps pair side-by-side" true false

  let sFloatSp0 := { s0 with windowHeight := 24, windowWidth := 80 }
  let sFloatSp1 ← runKeys sFloatSp0 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let sFloatSp2 ← runKeys sFloatSp1 ([Key.char ':'] ++ keys "split" ++ [Key.enter])
  let wsFloatSp2 := sFloatSp2.getCurrentWorkspace
  let floatingIdsSp := wsFloatSp2.getFloatingWindowIds.toList
  assertEqual "split in floating window keeps new pane floating" true (floatingIdsSp.length >= 2)
  match floatingIdsSp with
  | a :: b :: _ =>
      let stacked :=
        match sFloatSp2.getFloatingWindowBounds a, sFloatSp2.getFloatingWindowBounds b with
        | some (t1, l1, h1, w1), some (t2, l2, h2, w2) =>
            l1 == l2 && w1 == w2 && ((t1 + h1 == t2) || (t2 + h2 == t1))
        | _, _ => false
      assertEqual "split in floating window keeps pair stacked" true stacked
  | _ =>
      assertEqual "split in floating window keeps pair stacked" true false

  let sFloatMix0 := { s0 with windowHeight := 24, windowWidth := 80 }
  let sFloatMix1 ← runKeys sFloatMix0 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let sFloatMix2 ← runKeys sFloatMix1 ([Key.char ':'] ++ keys "vsplit" ++ [Key.enter])
  let sFloatMix3 ← runKeys sFloatMix2 ([Key.char ':'] ++ keys "split" ++ [Key.enter])
  let wsFloatMix3 := sFloatMix3.getCurrentWorkspace
  let floatingIdsMix := wsFloatMix3.getFloatingWindowIds.toList
  assertEqual "vsplit then split in floating window keeps three panes floating" 3 floatingIdsMix.length
  let boundsMix := floatingIdsMix.filterMap (fun wid => sFloatMix3.getFloatingWindowBounds wid)
  assertEqual "vsplit then split in floating window resolves bounds for all panes" 3 boundsMix.length
  let overlaps (a b : Nat × Nat × Nat × Nat) : Bool :=
    let (ta, la, ha, wa) := a
    let (tb, lb, hb, wb) := b
    la < lb + wb && lb < la + wa && ta < tb + hb && tb < ta + ha
  let rec hasOverlap (xs : List (Nat × Nat × Nat × Nat)) : Bool :=
    match xs with
    | [] => false
    | x :: rest => rest.any (fun y => overlaps x y) || hasOverlap rest
  assertEqual "vsplit then split in floating window panes do not overlap" false (hasOverlap boundsMix)

  let sFloatDeep0 := { s0 with windowHeight := 24, windowWidth := 80 }
  let sFloatDeep1 ← runKeys sFloatDeep0 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let sFloatDeep2 ← runKeys sFloatDeep1 ([Key.char ':'] ++ keys "vs" ++ [Key.enter])
  let sFloatDeep3 ← runKeys sFloatDeep2 ([Key.char ':'] ++ keys "hs" ++ [Key.enter])
  let sFloatDeep4 ← runKeys sFloatDeep3 ([Key.char ':'] ++ keys "vs" ++ [Key.enter])
  let wsFloatDeep4 := sFloatDeep4.getCurrentWorkspace
  let floatingIdsDeep := wsFloatDeep4.getFloatingWindowIds.toList
  assertEqual "vs -> hs -> vs in floating window creates four panes" 4 floatingIdsDeep.length
  let boundsDeep := floatingIdsDeep.filterMap (fun wid => sFloatDeep4.getFloatingWindowBounds wid)
  assertEqual "vs -> hs -> vs in floating window resolves bounds for all panes" 4 boundsDeep.length
  assertEqual "vs -> hs -> vs in floating window panes do not overlap" false (hasOverlap boundsDeep)
  let sideBySideTouch (a b : Nat × Nat × Nat × Nat) : Bool :=
    let (t1, l1, h1, w1) := a
    let (t2, l2, h2, w2) := b
    ((l1 + w1 == l2) || (l2 + w2 == l1)) && (t1 < t2 + h2 && t2 < t1 + h1)
  let stackedTouch (a b : Nat × Nat × Nat × Nat) : Bool :=
    let (t1, l1, h1, w1) := a
    let (t2, l2, h2, w2) := b
    ((t1 + h1 == t2) || (t2 + h2 == t1)) && (l1 < l2 + w2 && l2 < l1 + w1)
  let rec hasPairWith
      (pred : (Nat × Nat × Nat × Nat) → (Nat × Nat × Nat × Nat) → Bool)
      (xs : List (Nat × Nat × Nat × Nat)) : Bool :=
    match xs with
    | [] => false
    | x :: rest => rest.any (fun y => pred x y) || hasPairWith pred rest
  assertEqual "vs -> hs -> vs in floating window keeps horizontal adjacency" true (hasPairWith sideBySideTouch boundsDeep)
  assertEqual "vs -> hs -> vs in floating window keeps vertical adjacency" true (hasPairWith stackedTouch boundsDeep)

  let longLine := "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  let longText := String.intercalate "\n" [longLine, longLine, longLine, longLine, longLine, longLine, longLine, longLine, longLine, longLine, longLine, longLine] ++ "\n"
  let s20 := { s0 with windowHeight := 14, windowWidth := 40 }
  let s21 ← runKeys s20 ([Key.char 'i'] ++ keys longText ++ [Key.esc] ++ keys "gg0")
  let s22 ← runKeys s21 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let s23 ← runKeys s22 [Key.char '1', Key.char '0', Key.char 'j']
  let (sRow23, _) := s23.getScroll
  assertEqual "floating window vertical scroll follows cursor" true (sRow23.val > 0)

  let s24 ← runKeys s23 [Key.char '3', Key.char '5', Key.char 'l']
  let (_, sCol24) := s24.getScroll
  assertEqual "floating window horizontal scroll follows cursor" true (sCol24.val > 0)

  let s25 ← runKeys s0 ([Key.char 'i'] ++ keys "abcd\n" ++ [Key.esc] ++ keys "gg0")
  let s26 ← runKeys s25 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let s27 ← runKeys s26 [Key.char 'v', Key.char 'l', Key.char 'd']
  assertBuffer "visual mode edits active floating window buffer" s27 "cd\n"

  let s28 ← runKeys s0 ([Key.char 'i'] ++ keys "abcd\nefgh\n" ++ [Key.esc] ++ keys "gg0")
  let s29 ← runKeys s28 ([Key.char ':'] ++ keys "floatwin on" ++ [Key.enter])
  let s30 ← runKeys s29 [Key.char 'l', Key.char 'V', Key.char 'l', Key.char 'j', Key.char 'd']
  assertBuffer "visual block edits active floating window buffer" s30 "ad\neh\n"

def testBufferExplorerCommand : IO Unit := do
  IO.println "  Testing Buffer Explorer..."
  let s0 := ViE.initialState
  let stamp ← IO.monoMsNow
  let tmpRoot := s!"/tmp/vie-buffer-explorer-{stamp}"
  IO.FS.createDirAll tmpRoot
  let bufAPath := s!"{tmpRoot}/bufA.txt"
  let bufBPath := s!"{tmpRoot}/bufB.txt"
  IO.FS.writeFile bufAPath "alpha\n"
  IO.FS.writeFile bufBPath "beta\n"
  let sBuf0 := { s0 with windowHeight := 30, windowWidth := 100 }
  let sBuf1 ← runKeys sBuf0 ([Key.char ':'] ++ keys s!"e {bufAPath}" ++ [Key.enter])
  let sBuf2 ← runKeys sBuf1 ([Key.char ':'] ++ keys s!"e {bufBPath}" ++ [Key.enter])
  let targetBufIdOpt := sBuf2.getCurrentWorkspace.buffers.find? (fun b => b.filename == some bufAPath) |>.map (fun b => b.id)
  assertEqual "Buffer explorer target buffer exists" true targetBufIdOpt.isSome
  let targetBufId := targetBufIdOpt.getD 0

  let sBuf3 ← runKeys sBuf2 ([Key.char ':'] ++ keys "buf list" ++ [Key.enter])
  assertEqual ":buf list opens buffer explorer" true ((sBuf3.getActiveBuffer.filename.getD "").startsWith "explorer://buffers")
  let explorerBufId := sBuf3.getActiveBuffer.id
  let explorerBufOpt := sBuf3.explorers.find? (fun (id, _) => id == explorerBufId)
  match explorerBufOpt with
  | none =>
      assertEqual "Buffer explorer registered" true false
  | some (_, explorerBuf) =>
      let targetPath := s!"buffer://{targetBufId}"
      let targetIdxOpt := findEntryIndexByPath explorerBuf.entries targetPath
      assertEqual "Buffer explorer contains target buffer entry" true targetIdxOpt.isSome
      let targetIdx := targetIdxOpt.getD 0
      let sBuf4 := sBuf3.updateActiveView fun v => { v with cursor := { row := ⟨2 + targetIdx⟩, col := 0 } }
      let sBuf5 ← runKeys sBuf4 [Key.enter]
      assertEqual "Buffer explorer Enter switches active buffer" (some bufAPath) sBuf5.getActiveBuffer.filename
      assertEqual "Buffer explorer closes after selection" false (sBuf5.explorers.any (fun (id, _) => id == explorerBufId))

  let sBufCompat ← runKeys sBuf2 ([Key.char ':'] ++ keys "buffers" ++ [Key.enter])
  assertEqual ":buffers alias opens buffer explorer" true ((sBufCompat.getActiveBuffer.filename.getD "").startsWith "explorer://buffers")

  let sBufAlias ← runKeys sBuf2 ([Key.char ':'] ++ keys "ls" ++ [Key.enter])
  assertEqual ":ls alias opens buffer explorer" true ((sBufAlias.getActiveBuffer.filename.getD "").startsWith "explorer://buffers")

def testExplorerCommandAliases : IO Unit := do
  IO.println "  Testing Explorer Command Names..."
  let s0 := ViE.initialState
  let stamp ← IO.monoMsNow
  let tmpRoot := s!"/tmp/vie-ex-alias-{stamp}"
  IO.FS.createDirAll tmpRoot
  IO.FS.writeFile s!"{tmpRoot}/x.txt" "x\n"

  let s1 ← runKeys s0 ([Key.char ':'] ++ keys s!"ex list {tmpRoot}" ++ [Key.enter])
  assertEqual ":ex list opens file explorer" true ((s1.getActiveBuffer.filename.getD "").startsWith "explorer://")

  let s2 ← runKeys s0 ([Key.char ':'] ++ keys s!"ee {tmpRoot}" ++ [Key.enter])
  assertEqual ":ee alias opens file explorer" true ((s2.getActiveBuffer.filename.getD "").startsWith "explorer://")

  let s3 ← runKeys s0 ([Key.char ':'] ++ keys "wgex" ++ [Key.enter])
  assertEqual ":wgex alias opens workgroup explorer" (some "explorer://workgroups") s3.getActiveBuffer.filename

def test : IO Unit := do
  IO.println "Starting Expanded Keybind Tests..."
  testMotions
  testEditing
  testOperators
  testVisual
  testCounted
  testVimCompatMotions
  testWorkgroupSwitch
  testSearch
  testCommandSubstitute
  testCommandGlobal
  testCommandBloom
  testUiCommands
  testBufferExplorerCommand
  testExplorerCommandAliases
  IO.println "All Expanded Keybind Tests passed!"

end Test.Keybinds
