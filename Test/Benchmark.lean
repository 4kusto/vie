import ViE.State.Config
import ViE.Config
import ViE.Command.Impl
import ViE.Key.Map
import ViE.State.Edit
import ViE.State.Search
import ViE.Data.PieceTable.Tree
import ViE.UI

namespace ViE.Benchmark

open ViE

/-- Mock Config for Benchmarking -/
def makeBenchConfig (buildLeafBits : Option Bool := none) : Config :=
  let base := ViE.defaultConfig
  let settings :=
    match buildLeafBits with
    | some v => { base with searchBloomBuildLeafBits := v }
    | none => base
  {
    settings := settings
    commands := ViE.Command.defaultCommandMap
    bindings := ViE.Key.makeKeyMap ViE.Command.defaultCommandMap
  }

structure BenchOptions where
  iterations : Nat := 1000
  render : Bool := true
  cases : List String := []
  textLines : Nat := 200
  lineLen : Nat := 80
  warmup : Nat := 0
  buildLeafBits : Option Bool := none
  listOnly : Bool := false

def parseArgs (args : List String) : BenchOptions :=
  let rec loop (opts : BenchOptions) (args : List String) : BenchOptions :=
    match args with
    | [] => opts
    | "--no-render" :: rest => loop { opts with render := false } rest
    | "--case" :: name :: rest => loop { opts with cases := opts.cases ++ [name] } rest
    | "--lines" :: n :: rest =>
        match n.toNat? with
        | some v => loop { opts with textLines := v } rest
        | none => loop opts rest
    | "--line-len" :: n :: rest =>
        match n.toNat? with
        | some v => loop { opts with lineLen := v } rest
        | none => loop opts rest
    | "--warmup" :: n :: rest =>
        match n.toNat? with
        | some v => loop { opts with warmup := v } rest
        | none => loop opts rest
    | "--bloom-leaf-bits" :: rest => loop { opts with buildLeafBits := some true } rest
    | "--no-bloom-leaf-bits" :: rest => loop { opts with buildLeafBits := some false } rest
    | "--list" :: rest => loop { opts with listOnly := true } rest
    | arg :: rest =>
        match arg.toNat? with
        | some v => loop { opts with iterations := v } rest
        | none => loop opts rest
  loop {} args

/-- Simple timer helper -/
def timeCase (label : String) (iterations : Nat) (f : IO Unit) : IO Unit := do
  let t0 ← IO.monoMsNow
  f
  let t1 ← IO.monoMsNow
  let ms := t1 - t0
  let opsPerSec := if ms == 0 then 0 else (iterations * 1000) / ms
  IO.println s!"[bench] {label}: {ms} ms ({opsPerSec} ops/s)"

/-- Build a simple multi-line ASCII buffer for search benchmarks. -/
def buildText (lines : Nat) (lineLen : Nat) : String :=
  let line := String.ofList (List.replicate lineLen 'a')
  String.intercalate "\n" (List.replicate lines line)

/-- Insert a needle in the middle of text for search benchmarks. -/
def buildSearchText (lines : Nat) (lineLen : Nat) (needle : String) : String :=
  let baseLine := String.ofList (List.replicate lineLen 'a')
  let mid := lines / 2
  let leftLen := lineLen / 2
  let rightLen := if lineLen > leftLen + needle.length then lineLen - leftLen - needle.length else 0
  let needleLine :=
    (String.ofList (List.replicate leftLen 'a')) ++
    needle ++
    (String.ofList (List.replicate rightLen 'a'))
  let linesArr := Id.run do
    let mut arr := Array.replicate lines baseLine
    if mid < arr.size then
      arr := arr.set! mid needleLine
    return arr
  String.intercalate "\n" linesArr.toList

/-- Case: Large insert workload (EditorState). -/
def benchInsert (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  for i in [0:iterations] do
    s := s.insertChar 'a'
    if i % 100 == 0 then
      s := s.commitEdit

/-- Case: Mixed small edits/movements. -/
def benchEditMix (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  for _ in [0:iterations] do
    s := s.insertChar 'a'
    s := s.moveCursorLeft
    s := s.insertChar 'b'
    s := s.moveCursorRight

/-- Case: Clipboard (yank/paste). -/
def benchClipboard (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  s := s.insertChar 'x'
  for _ in [0:iterations/50] do
    s := s.yankCurrentLine
    s := s.pasteBelow

/-- Case: Workgroup churn. -/
def benchWorkgroups (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  for i in [0:iterations/200] do
    s := ← ViE.Command.cmdWg ["new", s!"BenchGroup {i}"] s
    s := s.insertChar 'w'
  for _ in [0:iterations/200] do
    s := ← ViE.Command.cmdWg ["close"] s

/-- Case: Window splits/cycles. -/
def benchWindows (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  for _ in [0:iterations/500] do
    s := ViE.Window.splitWindow s true
    s := ViE.Window.splitWindow s false
    s := s.insertChar 'v'
    s := ViE.Window.cycleWindow s
  for _ in [0:iterations/200] do
    s := ViE.Window.closeActiveWindow s

/-- Case: Undo/Redo stress. -/
def benchUndoRedo (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  for i in [0:iterations] do
    s := s.insertChar 'a'
    if i % 50 == 0 then
      s := s.commitEdit
  for _ in [0:iterations/10] do
    s := s.undo
  for _ in [0:iterations/10] do
    s := s.redo

/-- Case: Search workload (PieceTable). -/
def benchSearch (iterations : Nat) (useBloom : Bool) (lines lineLen : Nat) (buildLeafBits : Bool) (cacheMax : Nat) : IO Unit := do
  let needle := "needle"
  let text := buildSearchText lines lineLen needle
  let pt := PieceTable.fromString text buildLeafBits
  let pattern := needle.toUTF8
  let mut offset := 0
  let mut cache : Lean.RBMap Nat ByteArray compare := Lean.RBMap.empty
  let mut order : Array Nat := #[]
  for _ in [0:iterations] do
    let (res, cache', order') := PieceTree.searchNext pt.tree pt pattern offset searchChunkSize useBloom cache order cacheMax
    cache := cache'
    order := order'
    offset := match res with
      | some r => r + 1
      | none => 0

/-- Case: Render workload. -/
def benchRender (iterations : Nat) : IO Unit := do
  let mut s := ViE.initialState
  for _ in [0:iterations/20] do
    s := s.insertChar 'a'
  let _ ← ViE.UI.render s


def availableCases : List String :=
  [ "insert", "edit", "clipboard", "workgroups", "windows", "undo", "search-bloom", "search-linear", "render" ]

/-- Run benchmark cases. -/
def runBenchmark (opts : BenchOptions) : IO Unit := do
  let buildLeafBits := opts.buildLeafBits.getD ViE.defaultConfig.searchBloomBuildLeafBits
  let config := makeBenchConfig (some buildLeafBits)
  let cacheMax := config.settings.searchBloomCacheMax
  let cases := if opts.cases.isEmpty then availableCases else opts.cases

  IO.println s!"Starting benchmark: iter={opts.iterations}, render={opts.render}"

  if opts.warmup > 0 then
    IO.println s!"Warmup: {opts.warmup} iterations"
    for _ in [0:opts.warmup] do
      let mut s := ViE.initialState
      s := s.insertChar 'a'
      let _ ← pure s

  for c in cases do
    match c with
    | "insert" => timeCase "insert" opts.iterations (benchInsert opts.iterations)
    | "edit" => timeCase "edit" opts.iterations (benchEditMix opts.iterations)
    | "clipboard" => timeCase "clipboard" opts.iterations (benchClipboard opts.iterations)
    | "workgroups" => timeCase "workgroups" opts.iterations (benchWorkgroups opts.iterations)
    | "windows" => timeCase "windows" opts.iterations (benchWindows opts.iterations)
    | "undo" => timeCase "undo/redo" opts.iterations (benchUndoRedo opts.iterations)
    | "search-bloom" =>
        timeCase "search-bloom" opts.iterations (benchSearch opts.iterations true opts.textLines opts.lineLen buildLeafBits cacheMax)
    | "search-linear" =>
        timeCase "search-linear" opts.iterations (benchSearch opts.iterations false opts.textLines opts.lineLen buildLeafBits cacheMax)
    | "render" =>
        if opts.render then
          timeCase "render" opts.iterations (benchRender opts.iterations)
        else
          IO.println "[bench] render skipped (--no-render)"
    | other =>
        IO.println s!"[bench] Unknown case: {other}"

  IO.println "Benchmark completed."

end ViE.Benchmark

/-- CLI entrypoint. -/
def main (args : List String) : IO Unit := do
  let opts := ViE.Benchmark.parseArgs args
  if opts.listOnly then
    IO.println "Available cases:"
    IO.println (String.intercalate ", " ViE.Benchmark.availableCases)
  else
    ViE.Benchmark.runBenchmark opts
