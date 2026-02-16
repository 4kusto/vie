import ViE.UI.Syntax
import ViE.UI.Search
import Test.Utils

open Test.Utils

namespace Test.SyntaxHighlight

private def firstRangeOf (line : String) (pat : String) : Option (Nat × Nat) :=
  (ViE.UI.findAllMatchesBytes line.toUTF8 pat.toUTF8)[0]?

def testLean : IO Unit := do
  let line := "def x := 42 -- comment"
  let spans := ViE.UI.Syntax.highlightLine (some "Main.lean") line
  let (defS, defE) := (firstRangeOf line "def").getD (0, 0)
  let (numS, numE) := (firstRangeOf line "42").getD (0, 0)
  let (comS, comE) := (firstRangeOf line "-- comment").getD (0, 0)
  assertEqual "Lean keyword style" (some ViE.UI.Syntax.leanKeywordStyle) (ViE.UI.Syntax.styleForByteRange spans defS defE)
  assertEqual "Lean number style" (some ViE.UI.Syntax.leanNumberStyle) (ViE.UI.Syntax.styleForByteRange spans numS numE)
  assertEqual "Lean comment style" (some ViE.UI.Syntax.leanCommentStyle) (ViE.UI.Syntax.styleForByteRange spans comS comE)

def testMarkdown : IO Unit := do
  let line := "Use `code` and [link](url)"
  let spans := ViE.UI.Syntax.highlightLine (some "README.md") line
  let (codeS, codeE) := (firstRangeOf line "`code`").getD (0, 0)
  let (linkS, linkE) := (firstRangeOf line "[link](url)").getD (0, 0)
  assertEqual "Markdown code style" (some ViE.UI.Syntax.markdownCodeStyle) (ViE.UI.Syntax.styleForByteRange spans codeS codeE)
  assertEqual "Markdown link style" (some ViE.UI.Syntax.markdownLinkStyle) (ViE.UI.Syntax.styleForByteRange spans linkS linkE)

def test : IO Unit := do
  IO.println "Starting SyntaxHighlight Test..."
  testLean
  testMarkdown
  IO.println "SyntaxHighlight Test passed!"

end Test.SyntaxHighlight
