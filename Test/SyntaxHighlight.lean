import ViE.UI.Search
import Test.Utils
import Bliku.Tui.Syntax

open Test.Utils

namespace Test.SyntaxHighlight

private def firstRangeOf (line : String) (pat : String) : Option (Nat × Nat) :=
  (ViE.UI.findAllMatchesBytes line.toUTF8 pat.toUTF8)[0]?

def testLean : IO Unit := do
  let line := "def x := 42 -- comment"
  let spans := Bliku.Tui.Syntax.highlightLine (some "Main.lean") line
  let (defS, defE) := (firstRangeOf line "def").getD (0, 0)
  let (numS, numE) := (firstRangeOf line "42").getD (0, 0)
  let (comS, comE) := (firstRangeOf line "-- comment").getD (0, 0)
  assertEqual "Lean keyword style" (Bliku.Tui.Syntax.defaultPalette.faceFor .keyword)
    (Bliku.Tui.Syntax.faceForByteRange Bliku.Tui.Syntax.defaultPalette spans defS defE)
  assertEqual "Lean number style" (Bliku.Tui.Syntax.defaultPalette.faceFor .numberLiteral)
    (Bliku.Tui.Syntax.faceForByteRange Bliku.Tui.Syntax.defaultPalette spans numS numE)
  assertEqual "Lean comment style" (Bliku.Tui.Syntax.defaultPalette.faceFor .comment)
    (Bliku.Tui.Syntax.faceForByteRange Bliku.Tui.Syntax.defaultPalette spans comS comE)

def testMarkdown : IO Unit := do
  let line := "Use `code` and [link](url)"
  let spans := Bliku.Tui.Syntax.highlightLine (some "README.md") line
  let (codeS, codeE) := (firstRangeOf line "`code`").getD (0, 0)
  let (linkS, linkE) := (firstRangeOf line "[link](url)").getD (0, 0)
  assertEqual "Markdown code style" (Bliku.Tui.Syntax.defaultPalette.faceFor .code)
    (Bliku.Tui.Syntax.faceForByteRange Bliku.Tui.Syntax.defaultPalette spans codeS codeE)
  assertEqual "Markdown link style" (Bliku.Tui.Syntax.defaultPalette.faceFor .link)
    (Bliku.Tui.Syntax.faceForByteRange Bliku.Tui.Syntax.defaultPalette spans linkS linkE)

def test : IO Unit := do
  IO.println "Starting SyntaxHighlight Test..."
  testLean
  testMarkdown
  IO.println "SyntaxHighlight Test passed!"

end Test.SyntaxHighlight
