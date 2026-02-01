namespace ViE.Unicode

/-- Ranges of characters that have a visual width of 2 (Fullwidth/Wide).
    Based on EastAsianWidth.txt (Wide or Fullwidth). -/
def wideRanges : List (Nat × Nat) := [
  (0x1100, 0x115F), -- Hangul Jamo
  (0x2329, 0x232A), -- Angle brackets
  (0x2E80, 0x303E), -- CJK Radicals / Punctuation
  (0x3040, 0x3247), -- Hiragana, Katakana, Enclosed
  (0x3250, 0x4DBF), -- Enclosed CJK / CJK Extension A
  (0x4E00, 0xA4C6), -- CJK Unified Ideographs / Yi
  (0xA960, 0xA97C), -- Hangul Jamo Extended-A
  (0xAC00, 0xD7A3), -- Hangul Syllables
  (0xF900, 0xFAFF), -- CJK Compatibility Ideographs
  (0xFE10, 0xFE19), -- Vertical forms
  (0xFE30, 0xFE6F), -- CJK Compatibility Forms
  (0xFF01, 0xFF60), -- Fullwidth Forms
  (0xFFE0, 0xFFE6), -- Fullwidth currency/signs
  (0x1F300, 0x1F64F), -- Miscellaneous Symbols and Pictographs (Emojis)
  (0x1F900, 0x1F9FF)  -- Supplemental Symbols and Pictographs (some, generic range)
]

/-- Check if a character code is in a wide range. -/
def isWide (c : Nat) : Bool :=
  wideRanges.any fun (start, stop) => c >= start && c <= stop

/-- Get the visual width of a character.
    Returns 2 for wide characters, 0 for null/combining (simplified), 1 for others. -/
def charWidth (c : Char) : Nat :=
  let n := c.toNat
  if n == 0 then 0 -- Null is 0 width? Or usually displayed as something?
                 -- Usually invalid in text, but let's say 0.
  else if n < 0x20 then 2 -- Control characters shown as ^A
  else if n == 0x7F then 2 -- DEL shown as ^?
  else if isWide n then 2
  else 1

/-- Get the display string for a character.
    - Control characters (0x00-0x1F) -> "^A" notation.
    - 0x7F -> "^?"
    - Others -> character itself as string. -/
def getDisplayString (c : Char) : String :=
  let n := c.toNat
  if n < 0x20 then
    -- 0x01 is ^A (A is 0x41). 0x01 + 0x40 = 0x41.
    -- 0x00 is ^@.
    let base := (n + 0x40).toUInt8
    "^" ++ (Char.ofNat base.toNat).toString
  else if n == 0x7F then
    "^?"
  else
    c.toString

/-- Calculate the total visual width of a string. -/
def stringWidth (s : String) : Nat :=
  s.foldl (fun acc c => acc + charWidth c) 0

/-- Calculate the total visual width of a substring. -/
def substringWidth (s : Substring.Raw) : Nat :=
  s.foldl (fun acc c => acc + charWidth c) 0

/-- Get the byte length of a UTF-8 sequence starting with `b`.
    Returns 0 if `b` is a continuation byte or invalid start. -/
def utf8ByteLength (b : UInt8) : Nat :=
  if b < 0x80 then 1
  else if (b &&& 0xE0) == 0xC0 then 2
  else if (b &&& 0xF0) == 0xE0 then 3
  else if (b &&& 0xF8) == 0xF0 then 4
  else 0 -- Invalid or continuation

/-- Count newlines in a byte array slice efficiently -/
def countNewlines (data : ByteArray) (start : Nat) (len : Nat) : Nat :=
  let endPos := start + len
  let rec loop (i : Nat) (count : Nat) : Nat :=
    if i >= endPos then count
    else
      if data[i]! == 10 then loop (i + 1) (count + 1) -- 10 is \n
      else loop (i + 1) count
  loop start 0

/-- Count UTF-8 characters in a byte array range. -/
def countChars (bytes : ByteArray) (start len : Nat) : Nat :=
  let stop := start + len
  let rec loop (i : Nat) (cnt : Nat) : Nat :=
    if i >= stop then cnt
    else
      let b := bytes[i]!
      if (b &&& 0xC0) != 0x80 then
        loop (i + 1) (cnt + 1)
      else
        loop (i + 1) cnt
  loop start 0


end ViE.Unicode
