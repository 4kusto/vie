-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.Types

namespace ViE

/-- Convert String to Line (Array Char) -/
def stringToLine (s : String) : Line :=
  s.toList.toArray

/-- Convert Line (Array Char) to String -/
def lineToString (line : Line) : String :=
  String.ofList line.toList

/-- Helper to safely get a line as String. -/
def getLine (buffer : TextBuffer) (n : Row) : Option String :=
  if h : n.val < buffer.size then
    some (lineToString buffer[n.val])
  else
    none

end ViE
