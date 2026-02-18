import ViE.Color
import ViE.UI.Search

namespace ViE.UI.Syntax

inductive Language where
  | plain
  | lean
  | markdown
  deriving Repr, BEq, Inhabited

structure Span where
  startByte : Nat
  endByte : Nat
  style : String
  deriving Repr, BEq, Inhabited

def leanKeywordStyle : String := ViE.Color.toFg ViE.Color.Color.brightBlue
def leanCommentStyle : String := ViE.Color.toFg ViE.Color.Color.brightBlack
def leanStringStyle : String := ViE.Color.toFg ViE.Color.Color.brightGreen
def leanNumberStyle : String := ViE.Color.toFg ViE.Color.Color.brightMagenta

def markdownHeadingStyle : String := ViE.Color.toFg ViE.Color.Color.brightCyan
def markdownCodeStyle : String := ViE.Color.toFg ViE.Color.Color.brightYellow
def markdownLinkStyle : String := ViE.Color.toFg ViE.Color.Color.brightBlue
def markdownEmphasisStyle : String := ViE.Color.toFg ViE.Color.Color.brightMagenta

def detectLanguage (filename : Option String) : Language :=
  match filename with
  | none => .plain
  | some name =>
      if name.endsWith ".lean" then .lean
      else if name.endsWith ".md" || name.endsWith ".markdown" then .markdown
      else .plain

def styleForByteRange (spans : Array Span) (byteStart byteEnd : Nat) : Option String :=
  let rec loop (i : Nat) : Option String :=
    if i >= spans.size then
      none
    else
      let s := spans[i]!
      if ViE.UI.overlapsByteRange (s.startByte, s.endByte) byteStart byteEnd then
        some s.style
      else
        loop (i + 1)
  loop 0

end ViE.UI.Syntax
