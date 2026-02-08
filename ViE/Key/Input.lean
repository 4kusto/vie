import ViE.State
import ViE.Types

namespace ViE.Key

def flushEscSequence (seq : String) : List Key :=
  seq.toList.map (fun ch => if ch == '\x1b' then Key.esc else Key.char ch)

def isAsciiInRange (ch : Char) (lo hi : Nat) : Bool :=
  let n := ch.toNat
  lo <= n && n <= hi

def isCsiParamChar (ch : Char) : Bool :=
  ch.isDigit || ch == ';' || ch == '?' || ch == ':' || ch == '<' || ch == '=' || ch == '>'

def isCsiFinalChar (ch : Char) : Bool :=
  isAsciiInRange ch 0x40 0x7e

def decodeCsiFinal (ch : Char) : Key :=
  match ch with
  | 'A' => Key.up
  | 'B' => Key.down
  | 'C' => Key.right
  | 'D' => Key.left
  | 'H' => Key.unknown 'H'
  | 'F' => Key.unknown 'F'
  | _ => Key.unknown ch

def withPending (state : EditorState) (pending : String) (currentTime : Nat) : EditorState :=
  { state with inputState := { state.inputState with pendingKeys := pending, lastInputTime := currentTime } }

def clearPending (state : EditorState) : EditorState :=
  { state with inputState := { state.inputState with pendingKeys := "" } }

/-- Parse a character into a list of keys, handling escape sequences statefully. -/
def parseKey (state : EditorState) (c : Char) (currentTime : Nat) : (EditorState × List Key) :=
  if state.inputState.pendingKeys.length > 0 then
    let pending := state.inputState.pendingKeys.push c
    match pending with
    | "\x1b" =>
      (withPending state pending currentTime, [])
    | "\x1b[" =>
      (withPending state pending currentTime, [])
    | _ =>
      match pending.toList with
      | ['\x1b', ch] =>
        if ch == '[' then
          (withPending state pending currentTime, [])
        else
          (clearPending state, [Key.alt ch])
      | _ =>
        if pending.startsWith "\x1b[" then
          let chars := pending.toList
          let last := chars.getLastD '\x00'
          if isCsiFinalChar last then
            (clearPending state, [decodeCsiFinal last])
          else if isCsiParamChar last && pending.length <= 12 then
            (withPending state pending currentTime, [])
          else if pending.length > 12 then
            (clearPending state, flushEscSequence pending)
          else
            (clearPending state, flushEscSequence pending)
        else
          (clearPending state, flushEscSequence pending)
  else
    if c == '\x1b' then
       (withPending state "\x1b" currentTime, [])
    else
       let k := match c with
        | '\x01' => Key.ctrl 'a'
        | '\x02' => Key.ctrl 'b'
        | '\x03' => Key.ctrl 'c'
        | '\x04' => Key.ctrl 'd'
        | '\x05' => Key.ctrl 'e'
        | '\x06' => Key.ctrl 'f'
        | '\x07' => Key.ctrl 'g'
        | '\x08' => Key.ctrl 'h'
        | '\x09' => Key.ctrl 'i'
        | '\x0b' => Key.ctrl 'k'
        | '\x0c' => Key.ctrl 'l'
        | '\x0e' => Key.ctrl 'n'
        | '\x0f' => Key.ctrl 'o'
        | '\x10' => Key.ctrl 'p'
        | '\x11' => Key.ctrl 'q'
        | '\x12' => Key.ctrl 'r'
        | '\x13' => Key.ctrl 's'
        | '\x14' => Key.ctrl 't'
        | '\x15' => Key.ctrl 'u'
        | '\x16' => Key.ctrl 'v'
        | '\x17' => Key.ctrl 'w'
        | '\x18' => Key.ctrl 'x'
        | '\x19' => Key.ctrl 'y'
        | '\x1a' => Key.ctrl 'z'
        | '\x7f' => Key.backspace
        | '\x0a' | '\x0d' => Key.enter
        | _ => Key.char c
       (state, [k])

/-- Check for escape sequence timeout. -/
def checkTimeout (state : EditorState) (currentTime : Nat) : (EditorState × List Key) :=
  if state.inputState.pendingKeys.length > 0 then
    if currentTime - state.inputState.lastInputTime > 50 then
       let keys := flushEscSequence state.inputState.pendingKeys
       (clearPending state, keys)
    else
       (state, [])
  else
    (state, [])

end ViE.Key
