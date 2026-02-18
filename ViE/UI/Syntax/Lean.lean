import ViE.UI.Syntax.Types

namespace ViE.UI.Syntax

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

def highlightLeanLine (line : String) : Array Span := Id.run do
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

end ViE.UI.Syntax
