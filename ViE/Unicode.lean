namespace ViE.Unicode

/-- Ranges of characters that have a visual width of 2 (Fullwidth/Wide).
    Based on EastAsianWidth.txt (Wide or Fullwidth). -/
def wideRangesBmp : Array (Nat × Nat) := #[
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
  (0xFFE0, 0xFFE6)  -- Fullwidth currency/signs
]

def wideRangesSupplemental : Array (Nat × Nat) := #[
  (0x1F300, 0x1F64F), -- Miscellaneous Symbols and Pictographs (Emojis)
  (0x1F900, 0x1F9FF)  -- Supplemental Symbols and Pictographs (some, generic range)
]

/-- Check if a character code is in a wide range. -/
def isWide (c : Nat) : Bool :=
  if c < 0x1100 then
    false
  else
  let ranges := if c <= 0xFFFF then wideRangesBmp else wideRangesSupplemental
  let rec loop (lo hi : Nat) : Bool :=
    if h : lo < hi then
      let mid := (lo + hi) / 2
      let (start, stop) := ranges[mid]!
      if c < start then
        loop lo mid
      else if c > stop then
        loop (mid + 1) hi
      else
        true
    else
      false
    termination_by hi - lo
  loop 0 ranges.size

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

/-- Count newlines in a byte array slice. -/
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


/-- Convert a display column to a character index (0-based).
    If the column is in the middle of a wide character, it snaps to that character's index. -/
def displayColToCharIndex (s : String) (col : Nat) : Nat :=
  let rec loop (cs : List Char) (idx width : Nat) : Nat :=
    match cs with
    | [] => idx
    | c :: rest =>
      let w := charWidth c
      if width + w > col then
        idx
      else
        loop rest (idx + 1) (width + w)
  loop s.toList 0 0

/-- Display width of the first `idx` characters in a string. -/
def displayWidthAtCharIndex (s : String) (idx : Nat) : Nat :=
  let rec loop (cs : List Char) (i acc : Nat) : Nat :=
    match cs with
    | [] => acc
    | c :: rest =>
      if i >= idx then
        acc
      else
        loop rest (i + 1) (acc + charWidth c)
  loop s.toList 0 0

/-- Convert a display column to a UTF-8 byte offset within a string. -/
def displayColToByteOffset (s : String) (col : Nat) : Nat :=
  let rec loop (cs : List Char) (byteAcc widthAcc : Nat) : Nat :=
    match cs with
    | [] => byteAcc
    | c :: rest =>
      let w := charWidth c
      let b := c.toString.toUTF8.size
      if widthAcc + w > col then
        byteAcc
      else
        loop rest (byteAcc + b) (widthAcc + w)
  loop s.toList 0 0

/-- Build an index mapping display columns to UTF-8 byte offsets at character boundaries.
    The result includes the starting boundary (0,0) and the final boundary (totalWidth,totalBytes). -/
def buildDisplayByteIndex (s : String) : Array (Nat × Nat) :=
  let rec loop (cs : List Char) (disp bytes : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
    match cs with
    | [] => acc
    | c :: rest =>
      let w := charWidth c
      let b := c.toString.toUTF8.size
      let disp' := disp + w
      let bytes' := bytes + b
      loop rest disp' bytes' (acc.push (disp', bytes'))
  loop s.toList 0 0 #[(0, 0)]

/-- Convert a display column to a UTF-8 byte offset using a precomputed index. -/
def displayColToByteOffsetFromIndex (idx : Array (Nat × Nat)) (col : Nat) : Nat :=
  if idx.isEmpty then
    0
  else
    let rec loop (lo hi : Nat) (best : Nat) : Nat :=
      if h : lo < hi then
        let mid := (lo + hi) / 2
        let (disp, bytes) := idx[mid]!
        if col < disp then
          loop lo mid best
        else
          loop (mid + 1) hi bytes
      else
        best
      termination_by hi - lo
    loop 0 idx.size 0

/-- Compute the next display column (advancing by one character). -/
def nextDisplayCol (s : String) (col : Nat) : Nat :=
  let idx := displayColToCharIndex s col
  let startWidth := displayWidthAtCharIndex s idx
  if col < startWidth then
    startWidth
  else
    let chars := s.toList
    if idx < chars.length then
      let w := charWidth (chars[idx]!)
      startWidth + w
    else
      col

/-- Compute the previous display column (moving back by one character). -/
def prevDisplayCol (s : String) (col : Nat) : Nat :=
  if col == 0 then
    0
  else
    let idx := displayColToCharIndex s col
    let startWidth := displayWidthAtCharIndex s idx
    if col > startWidth then
      startWidth
    else if idx == 0 then
      0
    else
      displayWidthAtCharIndex s (idx - 1)

/-- Drop `width` display columns from the start of a substring. -/
def dropByDisplayWidth (s : Substring.Raw) (width : Nat) : Substring.Raw :=
  let rec loop (i : String.Pos.Raw) (acc : Nat) : Substring.Raw :=
    if h : i.byteIdx < s.bsize then
      let c := s.get i
      let w := charWidth c
      if acc + w > width then
        s.extract i ⟨s.bsize⟩
      else
        let i' := s.next i
        have := Nat.sub_lt_sub_left h (Substring.Raw.lt_next s i h)
        loop i' (acc + w)
    else
      s.extract i ⟨s.bsize⟩
    termination_by s.bsize - i.1
  loop 0 0

/-- Take characters from substring until visual width limit is reached. -/
def takeByDisplayWidth (s : Substring.Raw) (width : Nat) : String :=
  let rec loop (i : String.Pos.Raw) (currW : Nat) (acc : String) : String :=
    if h : i.byteIdx < s.bsize then
      let c := s.get i
      let w := charWidth c
      if currW + w <= width then
        let i' := s.next i
        have := Nat.sub_lt_sub_left h (Substring.Raw.lt_next s i h)
        loop i' (currW + w) (acc ++ getDisplayString c)
      else
        acc
    else
      acc
    termination_by s.bsize - i.1
  loop 0 0 ""

end ViE.Unicode
