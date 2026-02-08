import ViE.Unicode

namespace ViE.Terminal

/-- Enable raw mode using stty.
    This relies on the availability of the `stty` command in the environment. -/
def enableRawMode : IO Unit := do
  -- We ignore the output.
  -- Explicitly target /dev/tty because IO.Process might redirect stdin
  -- min 0 time 0 for non-blocking read
  let _ ← IO.Process.run { cmd := "stty", args := #["-F", "/dev/tty", "raw", "-echo", "min", "0", "time", "0"] }
  return ()

/-- Disable raw mode using stty. -/
def disableRawMode : IO Unit := do
  let _ ← IO.Process.run { cmd := "stty", args := #["-F", "/dev/tty", "sane"] }
  return ()

/-- Clear the screen and position cursor at top-left. -/
def clearScreen : IO Unit := do
  IO.print "\x1b[2J"
  IO.print "\x1b[H"

/-- Get window size (rows, cols) using stty size. -/
def getWindowSize : IO (Nat × Nat) := do
  let out ← IO.Process.run { cmd := "stty", args := #["-F", "/dev/tty", "size"] }
  let parts := out.trimAscii.toString.splitOn " "
  match parts with
  | [rows, cols] =>
    let r := rows.toNat!
    let c := cols.toNat!
    return (r, c)
  | _ => return (24, 80) -- Fallback

/-- Move cursor to specific row and column (0-indexed). -/
def moveCursor (row col : Nat) : IO Unit := do
  -- ANSI escape codes are 1-indexed.
  IO.print s!"\x1b[{row + 1};{col + 1}H"

def moveCursorStr (row col : Nat) : String :=
  s!"\x1b[{row + 1};{col + 1}H"

/-- Hide cursor. -/
def hideCursor : IO Unit := do
  IO.print "\x1b[?25l"

def hideCursorStr : String := "\x1b[?25l"

/-- Show cursor. -/
def showCursor : IO Unit := do
  IO.print "\x1b[?25h"

def showCursorStr : String := "\x1b[?25h"

/-- Clear from cursor to end of line. -/
def clearLineStr : String := "\x1b[K"

/-- Home cursor. -/
def homeCursorStr : String := "\x1b[H"

/-- Clear entire screen. -/
def clearScreenStr : String := "\x1b[2J"

/-- Read a single byte from stdin.
    Returns none on EOF or if no input available. -/
def readKey : IO (Option Char) := do
  let stdin ← IO.getStdin
  let b1_arr ← stdin.read 1
  if b1_arr.size == 0 then
    return none

  let b1 := b1_arr[0]!
  let len := ViE.Unicode.utf8ByteLength b1

  if len == 1 then
    return some (Char.ofNat b1.toNat)
  else if len == 0 then
    -- Invalid start byte, ignore
    return none
  else
    -- Read remaining bytes (blocking for completion of valid UTF-8 char)
    -- If we got the first byte of a multi-byte sequence, the rest should be there immediately.
    let rest ← stdin.read (len - 1).toUSize
    if rest.size != len - 1 then return none

    let b1n := b1.toNat

    if len == 2 then
        let b2 := rest[0]!.toNat
        let u := ((b1n &&& 0x1F) <<< 6) ||| (b2 &&& 0x3F)
        return some (Char.ofNat u)
    else if len == 3 then
        let b2 := rest[0]!.toNat
        let b3 := rest[1]!.toNat
        let u := ((b1n &&& 0x0F) <<< 12) ||| ((b2 &&& 0x3F) <<< 6) ||| (b3 &&& 0x3F)
        return some (Char.ofNat u)
    else if len == 4 then
        let b2 := rest[0]!.toNat
        let b3 := rest[1]!.toNat
        let b4 := rest[2]!.toNat
        let u := ((b1n &&& 0x07) <<< 18) ||| ((b2 &&& 0x3F) <<< 12) ||| ((b3 &&& 0x3F) <<< 6) ||| (b4 &&& 0x3F)
        return some (Char.ofNat u)
    else
        return none

end ViE.Terminal
