namespace ViE.Color

/-- Represents terminal colors. -/
inductive Color
  | black | red | green | yellow | blue | magenta | cyan | white
  | brightBlack | brightRed | brightGreen | brightYellow | brightBlue | brightMagenta | brightCyan | brightWhite
  | rgb (r g b : UInt8)
  | grayscale (level : UInt8) -- 0-23 (maps to 232-255)
  | default
  deriving Repr, BEq, Inhabited

/-- Convert Color to FG ANSI string -/
def toFg (c : Color) : String :=
  match c with
  | .black => "\x1b[30m"
  | .red => "\x1b[31m"
  | .green => "\x1b[32m"
  | .yellow => "\x1b[33m"
  | .blue => "\x1b[34m"
  | .magenta => "\x1b[35m"
  | .cyan => "\x1b[36m"
  | .white => "\x1b[37m"
  | .brightBlack => "\x1b[90m"
  | .brightRed => "\x1b[91m"
  | .brightGreen => "\x1b[92m"
  | .brightYellow => "\x1b[93m"
  | .brightBlue => "\x1b[94m"
  | .brightMagenta => "\x1b[95m"
  | .brightCyan => "\x1b[96m"
  | .brightWhite => "\x1b[97m"
  | .rgb r g b => s!"\x1b[38;2;{r};{g};{b}m"
  | .grayscale level =>
      let idx := 232 + (if level > 23 then 23 else level)
      s!"\x1b[38;5;{idx}m"
  | .default => "\x1b[39m"

/-- Convert Color to BG ANSI string -/
def toBg (c : Color) : String :=
  match c with
  | .black => "\x1b[40m"
  | .red => "\x1b[41m"
  | .green => "\x1b[42m"
  | .yellow => "\x1b[43m"
  | .blue => "\x1b[44m"
  | .magenta => "\x1b[45m"
  | .cyan => "\x1b[46m"
  | .white => "\x1b[47m"
  | .brightBlack => "\x1b[100m"
  | .brightRed => "\x1b[101m"
  | .brightGreen => "\x1b[102m"
  | .brightYellow => "\x1b[103m"
  | .brightBlue => "\x1b[104m"
  | .brightMagenta => "\x1b[105m"
  | .brightCyan => "\x1b[106m"
  | .brightWhite => "\x1b[107m"
  | .rgb r g b => s!"\x1b[48;2;{r};{g};{b}m"
  | .grayscale level =>
      let idx := 232 + (if level > 23 then 23 else level)
      s!"\x1b[48;5;{idx}m"
  | .default => "\x1b[49m"

def reset : String := "\x1b[0m"

/-- Helper to parse hex string like "#RRGGBB" or "RRGGBB". -/
def fromHex (hex : String) : Option Color :=
  let s := if hex.startsWith "#" then hex.drop 1 else hex
  if s.positions.count != 6 then none
  else
    let rStr := s.take 2
    let gStr := (s.drop 2).take 2
    let bStr := (s.drop 4).take 2
    match (String.toNat? ("0x" ++ rStr)), (String.toNat? ("0x" ++ gStr)), (String.toNat? ("0x" ++ bStr)) with
    | some r, some g, some b =>
       if r < 256 && g < 256 && b < 256 then
         some (.rgb r.toUInt8 g.toUInt8 b.toUInt8)
       else none
    | _, _, _ => none

end ViE.Color
