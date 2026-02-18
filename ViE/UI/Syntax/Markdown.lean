import ViE.UI.Syntax.Types

namespace ViE.UI.Syntax

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

def highlightMarkdownLine (line : String) : Array Span := Id.run do
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

end ViE.UI.Syntax
