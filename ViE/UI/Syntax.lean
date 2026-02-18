import ViE.UI.Syntax.Types
import ViE.UI.Syntax.Lean
import ViE.UI.Syntax.Markdown

namespace ViE.UI.Syntax

def highlightLine (filename : Option String) (line : String) : Array Span :=
  match detectLanguage filename with
  | .plain => #[]
  | .lean => highlightLeanLine line
  | .markdown => highlightMarkdownLine line

end ViE.UI.Syntax
