import ViE.Color
import ViE.UI.Search

namespace ViE.UI.Syntax

open ViE

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

private def isAsciiLower (n : Nat) : Bool := 97 <= n && n <= 122
private def isAsciiUpper (n : Nat) : Bool := 65 <= n && n <= 90
private def isAsciiDigit (n : Nat) : Bool := 48 <= n && n <= 57
private def isIdentStart (b : UInt8) : Bool :=
  let n := b.toNat
  isAsciiLower n || isAsciiUpper n || n == 95
private def isIdentCont (b : UInt8) : Bool :=
  let n := b.toNat
  isIdentStart b || isAsciiDigit n || n == 39

private def leanKeywords : Array String := #[
  "abbrev", "axiom", "by", "class", "constant", "def", "deriving", "do",
  "else", "end", "example", "from", "have", "if", "import", "in", "inductive",
  "instance", "let", "match", "mutual", "namespace", "open", "opaque", "private",
  "protected", "set_option", "show", "structure", "syntax", "termination_by",
  "theorem", "unsafe", "variable", "where", "with"
]

def detectLanguage (filename : Option String) : Language :=
  match filename with
  | none => .plain
  | some name =>
      if name.endsWith ".lean" then .lean
      else if name.endsWith ".md" || name.endsWith ".markdown" then .markdown
      else .plain

private def tokenizeLean (line : String) : Array Span := Id.run do
  let bytes := line.toUTF8
  let n := bytes.size
  let mut spans : Array Span := #[]
  let mut i := 0

  while i < n do
    let b := bytes[i]!
    if b == 34 then
      let mut j := i + 1
      let mut escaped := false
      let mut closed := false
      while j < n && !closed do
        let c := bytes[j]!
        if escaped then
          escaped := false
          j := j + 1
        else if c == 92 then
          escaped := true
          j := j + 1
        else if c == 34 then
          closed := true
          j := j + 1
        else
          j := j + 1
      spans := spans.push { startByte := i, endByte := j, style := leanStringStyle }
      i := j
    else if i + 1 < n && bytes[i]! == 45 && bytes[i + 1]! == 45 then
      spans := spans.push { startByte := i, endByte := n, style := leanCommentStyle }
      i := n
    else if i + 1 < n && bytes[i]! == 47 && bytes[i + 1]! == 45 then
      spans := spans.push { startByte := i, endByte := n, style := leanCommentStyle }
      i := n
    else if isAsciiDigit b.toNat then
      let mut j := i + 1
      while j < n do
        let c := bytes[j]!.toNat
        if isAsciiDigit c || c == 95 || c == 46 || c == 120 || c == 111 || c == 98 ||
           (65 <= c && c <= 70) || (97 <= c && c <= 102) then
          j := j + 1
        else
          break
      spans := spans.push { startByte := i, endByte := j, style := leanNumberStyle }
      i := j
    else if isIdentStart b then
      let mut j := i + 1
      while j < n && isIdentCont (bytes[j]!) do
        j := j + 1
      let tok := String.fromUTF8! (bytes.extract i j)
      if leanKeywords.contains tok then
        spans := spans.push { startByte := i, endByte := j, style := leanKeywordStyle }
      i := j
    else
      i := i + 1
  return spans

private def isMarkdownHeading (bytes : ByteArray) : Bool := Id.run do
  let n := bytes.size
  let mut i := 0
  while i < n && bytes[i]! == 32 do
    i := i + 1
  if i >= n || bytes[i]! != 35 then
    return false
  let mut j := i
  while j < n && bytes[j]! == 35 do
    j := j + 1
  return j < n && bytes[j]! == 32

private def isMarkdownFence (bytes : ByteArray) : Bool :=
  (bytes.size >= 3 && bytes[0]! == 96 && bytes[1]! == 96 && bytes[2]! == 96) ||
  (bytes.size >= 3 && bytes[0]! == 126 && bytes[1]! == 126 && bytes[2]! == 126)

private def tokenizeMarkdown (line : String) : Array Span := Id.run do
  let bytes := line.toUTF8
  let n := bytes.size
  if isMarkdownHeading bytes then
    return #[{ startByte := 0, endByte := n, style := markdownHeadingStyle }]
  if isMarkdownFence bytes then
    return #[{ startByte := 0, endByte := n, style := markdownCodeStyle }]

  let mut spans : Array Span := #[]
  let mut i := 0
  while i < n do
    if bytes[i]! == 96 then
      let mut j := i + 1
      while j < n && bytes[j]! != 96 do
        j := j + 1
      if j < n then
        spans := spans.push { startByte := i, endByte := j + 1, style := markdownCodeStyle }
        i := j + 1
      else
        i := i + 1
    else if bytes[i]! == 91 then
      let mut j := i + 1
      while j < n && bytes[j]! != 93 do
        j := j + 1
      if j + 1 < n && bytes[j]! == 93 && bytes[j + 1]! == 40 then
        let mut k := j + 2
        while k < n && bytes[k]! != 41 do
          k := k + 1
        if k < n then
          spans := spans.push { startByte := i, endByte := k + 1, style := markdownLinkStyle }
          i := k + 1
        else
          i := i + 1
      else
        i := i + 1
    else if bytes[i]! == 42 || bytes[i]! == 95 then
      let delim := bytes[i]!
      let mut j := i + 1
      while j < n && bytes[j]! != delim do
        j := j + 1
      if j < n && j > i + 1 then
        spans := spans.push { startByte := i, endByte := j + 1, style := markdownEmphasisStyle }
        i := j + 1
      else
        i := i + 1
    else
      i := i + 1
  return spans

def highlightLine (filename : Option String) (line : String) : Array Span :=
  match detectLanguage filename with
  | .plain => #[]
  | .lean => tokenizeLean line
  | .markdown => tokenizeMarkdown line

def styleForByteRange (spans : Array Span) (byteStart byteEnd : Nat) : Option String :=
  let rec loop (i : Nat) : Option String :=
    if i >= spans.size then
      none
    else
      let s := spans[i]!
      if overlapsByteRange (s.startByte, s.endByte) byteStart byteEnd then
        some s.style
      else
        loop (i + 1)
  loop 0

end ViE.UI.Syntax
