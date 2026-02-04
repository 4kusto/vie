import ViE.State
import ViE.Types

namespace ViE.Key

/-- Parse a character into a list of keys, handling escape sequences statefully. -/
def parseKey (state : EditorState) (c : Char) (currentTime : Nat) : (EditorState × List Key) :=
  -- If we have pending keys (escape sequence in progress)
  if state.inputState.pendingKeys.length > 0 then
    let pending := state.inputState.pendingKeys.push c
    -- Check for known sequences
    match pending with
    | "\x1b" =>
      ({ state with inputState := { state.inputState with pendingKeys := pending, lastInputTime := currentTime } }, [])
    | "\x1b[" =>
       -- CSI sequence starter, keep waiting
       ({ state with inputState := { state.inputState with pendingKeys := pending, lastInputTime := currentTime } }, [])
    | "\x1b[A" => ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.up])
    | "\x1b[B" => ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.down])
    | "\x1b[C" => ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.right])
    | "\x1b[D" => ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.left])
    | "\x1b[H" => ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.unknown 'H']) -- Home?
    | "\x1b[F" => ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.unknown 'F']) -- End?
    | _ =>
       -- Treat ESC + <char> as Alt combination when it's a single character and not CSI.
       match pending.toList with
       | ['\x1b', ch] =>
         if ch != '[' then
           ({ state with inputState := { state.inputState with pendingKeys := "" } }, [Key.alt ch])
         else
           ({ state with inputState := { state.inputState with pendingKeys := pending, lastInputTime := currentTime } }, [])
       | _ =>
       -- Unknown sequence or incomplete?
       -- If length is long enough (e.g. 3 chars) and no match, flush as individual keys?
       -- Or check if it starts with valid prefix.
       if pending.startsWith "\x1b[" && pending.length < 5 then
          ({ state with inputState := { state.inputState with pendingKeys := pending, lastInputTime := currentTime } }, [])
       else
          -- Flush everything as individual characters
          -- (Note: this simplifies, strictly we should map char-by-char)
          let keys := pending.toList.map (fun x => if x == '\x1b' then Key.esc else Key.char x)
          ({ state with inputState := { state.inputState with pendingKeys := "" } }, keys)
  else
    -- No pending keys
    if c == '\x1b' then
       -- Start escape sequence
       ({ state with inputState := { state.inputState with pendingKeys := "\x1b", lastInputTime := currentTime } }, [])
    else
       -- Normal character (using logic similar to old fromChar)
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
    if currentTime - state.inputState.lastInputTime > 50 then -- 50ms timeout
       -- Timeout! Flush pending keys as is.
       let keys := state.inputState.pendingKeys.toList.map (fun x => if x == '\x1b' then Key.esc else Key.char x)
       ({ state with inputState := { state.inputState with pendingKeys := "" } }, keys)
    else
       (state, [])
  else
    (state, [])

end ViE.Key
