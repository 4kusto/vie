-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.State.Config
import ViE.Config
import ViE.Command.Impl
import ViE.Key.Map
import ViE.State.Edit
import ViE.State.Search
import ViE.Data.PieceTable.Tree
import ViE.BlikuAdapter

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
  let _ ← ViE.BlikuAdapter.render s

/-- Generate large text content of specified size (in bytes). -/
def buildLargeText (sizeBytes : Nat) : String :=
  let lineLen := 80
  let line := String.ofList (List.replicate lineLen 'a') ++ "\n"
  let lineBytes := line.utf8ByteSize
  let numLines := sizeBytes / lineBytes
  String.intercalate "" (List.replicate numLines line)

/-- Case: Load large file (1MB). -/
def benchLoadLarge1MB (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (1024 * 1024)  -- 1MB
  let _ := PieceTable.fromString text buildLeafBits
  pure ()

/-- Case: Load large file (10MB). -/
def benchLoadLarge10MB (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (10 * 1024 * 1024)  -- 10MB
  let _ := PieceTable.fromString text buildLeafBits
  pure ()

/-- Case: Load large file (100MB). -/
def benchLoadLarge100MB (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (100 * 1024 * 1024)  -- 100MB
  let _ := PieceTable.fromString text buildLeafBits
  pure ()

/-- Case: Insert at middle of large file (1MB). -/
def benchInsertMidLarge1MB (iterations : Nat) (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (1024 * 1024)
  let pt := PieceTable.fromString text buildLeafBits
  let midOffset := pt.tree.stats.bytes.toNat / 2
  let mut checksum := 0
  -- Consume split results so optimizer cannot erase this loop.
  for _ in [0:iterations] do
    let (l, r) := PieceTree.split pt.tree midOffset pt
    checksum := checksum + l.stats.bytes.toNat + r.stats.bytes.toNat
  if checksum == 0 then
    IO.println "Zero bytes?"

/-- Case: Insert at middle of large file (10MB). -/
def benchInsertMidLarge10MB (iterations : Nat) (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (10 * 1024 * 1024)
  let pt := PieceTable.fromString text buildLeafBits
  let midOffset := pt.tree.stats.bytes.toNat / 2
  let mut checksum := 0
  -- Consume split results so optimizer cannot erase this loop.
  for _ in [0:iterations] do
    let (l, r) := PieceTree.split pt.tree midOffset pt
    checksum := checksum + l.stats.bytes.toNat + r.stats.bytes.toNat
  if checksum == 0 then
    IO.println "Zero bytes?"

/-- Case: Split operation on large file (1MB). -/
def benchSplitLarge1MB (iterations : Nat) (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (1024 * 1024)
  let pt := PieceTable.fromString text buildLeafBits
  let midOffset := pt.tree.stats.bytes.toNat / 2
  let mut checksum := 0
  for _ in [0:iterations] do
    let (l, r) := PieceTree.split pt.tree midOffset pt
    checksum := checksum + l.stats.bytes.toNat + r.stats.bytes.toNat
  if checksum == 0 then
    IO.println "Zero bytes?"

/-- Case: Split operation on large file (10MB). -/
def benchSplitLarge10MB (iterations : Nat) (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (10 * 1024 * 1024)
  let pt := PieceTable.fromString text buildLeafBits
  let midOffset := pt.tree.stats.bytes.toNat / 2
  let mut checksum := 0
  for _ in [0:iterations] do
    let (l, r) := PieceTree.split pt.tree midOffset pt
    checksum := checksum + l.stats.bytes.toNat + r.stats.bytes.toNat
  if checksum == 0 then
    IO.println "Zero bytes?"

/-- Case: GetBytes operation on large file (1MB). -/
def benchGetBytesLarge1MB (iterations : Nat) (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (1024 * 1024)
  let pt := PieceTable.fromString text buildLeafBits
  let chunkSize := 1024  -- 1KB chunks
  let mut checksum := 0
  for i in [0:iterations] do
    let offset := (i * chunkSize) % pt.tree.stats.bytes.toNat
    let bytes := PieceTree.getBytes pt.tree offset chunkSize pt
    checksum := checksum + bytes.size
  if checksum == 0 then
    IO.println "Zero bytes?"

/-- Case: GetBytes operation on large file (10MB). -/
def benchGetBytesLarge10MB (iterations : Nat) (buildLeafBits : Bool) : IO Unit := do
  let text := buildLargeText (10 * 1024 * 1024)
  let pt := PieceTable.fromString text buildLeafBits
  let chunkSize := 1024  -- 1KB chunks
  let mut checksum := 0
  for i in [0:iterations] do
    let offset := (i * chunkSize) % pt.tree.stats.bytes.toNat
    let bytes := PieceTree.getBytes pt.tree offset chunkSize pt
    checksum := checksum + bytes.size
  if checksum == 0 then
    IO.println "Zero bytes?"


def availableCases : List String :=
  [ "insert", "edit", "clipboard", "workgroups", "windows", "undo", "search-bloom", "search-linear", "render",
    "load-1mb", "load-10mb", "load-100mb",
    "insert-mid-1mb", "insert-mid-10mb",
    "split-1mb", "split-10mb",
    "getbytes-1mb", "getbytes-10mb" ]

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
    | "load-1mb" =>
        let text := buildLargeText (1024 * 1024)
        timeCase "load-1mb" opts.iterations (for _ in [0:opts.iterations] do
          let pt := PieceTable.fromString text buildLeafBits
          if pt.tree.stats.bytes == 0 then IO.println "Zero bytes?" -- force usage
        )
    | "load-10mb" =>
        let text := buildLargeText (10 * 1024 * 1024)
        timeCase "load-10mb" opts.iterations (for _ in [0:opts.iterations] do
          let pt := PieceTable.fromString text buildLeafBits
          if pt.tree.stats.bytes == 0 then IO.println "Zero bytes?"
        )
    | "load-100mb" =>
        let text := buildLargeText (100 * 1024 * 1024)
        timeCase "load-100mb" opts.iterations (for _ in [0:opts.iterations] do
          let pt := PieceTable.fromString text buildLeafBits
          if pt.tree.stats.bytes == 0 then IO.println "Zero bytes?"
        )
    | "insert-mid-1mb" => timeCase "insert-mid-1mb" opts.iterations (benchInsertMidLarge1MB opts.iterations buildLeafBits)
    | "insert-mid-10mb" => timeCase "insert-mid-10mb" opts.iterations (benchInsertMidLarge10MB opts.iterations buildLeafBits)
    | "split-1mb" => timeCase "split-1mb" opts.iterations (benchSplitLarge1MB opts.iterations buildLeafBits)
    | "split-10mb" => timeCase "split-10mb" opts.iterations (benchSplitLarge10MB opts.iterations buildLeafBits)
    | "getbytes-1mb" => timeCase "getbytes-1mb" opts.iterations (benchGetBytesLarge1MB opts.iterations buildLeafBits)
    | "getbytes-10mb" => timeCase "getbytes-10mb" opts.iterations (benchGetBytesLarge10MB opts.iterations buildLeafBits)
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
