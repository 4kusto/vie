import ViE.State.Config
import ViE.Config
import ViE.Command.Impl
import ViE.Key.Map
import ViE.State.Edit
import ViE.UI

namespace ViE.Benchmark

open ViE

/-- Mock Config for Benchmarking -/
def makeBenchConfig : Config := {
  settings := ViE.defaultConfig
  commands := ViE.Command.defaultCommandMap
  bindings := ViE.Key.makeKeyMap ViE.Command.defaultCommandMap
}

/-- Simulate a heavy editing session -/
def runBenchmark (iterations : Nat) : IO Unit := do
  let _config := makeBenchConfig
  let mut s := ViE.initialState

  -- 1. Initial Large Insertion
  IO.println s!"Starting benchmark with {iterations} iterations..."
  for i in [0:iterations] do
    s := s.insertChar 'a'
    if i % 100 == 0 then
      s := s.commitEdit

  -- 2. Random Access / Movement
  for _ in [0:iterations/10] do
    s := s.moveCursorUp
    s := s.moveCursorLeft
    s := s.insertChar 'b'

  -- 3. Clipboard (Yank / Paste)
  IO.println "Benchmarking Clipboard..."
  for _ in [0:iterations/100] do
    s := s.yankCurrentLine
    s := s.pasteBelow

  -- 4. Workgroups (New / Switch / Close)
  IO.println "Benchmarking Workgroups..."
  for i in [0:iterations/500] do
    s := ← ViE.Command.cmdWg ["new", s!"BenchGroup {i}"] s
    s := s.insertChar 'w'

  -- Close them back (stress test closing)
  for _ in [0:iterations/500] do
    s := ← ViE.Command.cmdWg ["close"] s

  -- 5. Windows (Split / Cycle / Close)
  IO.println "Benchmarking Windows..."
  -- Note: Limit total windows to avoid extreme UI depth in benchmark
  for _ in [0:iterations/1000] do
    s := ViE.Window.splitWindow s true  -- Vertical split
    s := ViE.Window.splitWindow s false -- Horizontal split
    s := s.insertChar 'v'
    s := ViE.Window.cycleWindow s

  -- Close windows
  for _ in [0:iterations/500] do
    s := ViE.Window.closeActiveWindow s

  -- 6. Undo / Redo stress
  IO.println "Benchmarking Undo/Redo..."
  for _ in [0:iterations/20] do
    s := s.undo

  -- 7. Render Simulation (Crucial for B+ tree traversal check)
  -- We don't actually print to TTY to avoid I/O bottlenecks in perf
  let _ ← ViE.UI.render s

  IO.println "Benchmark completed."

end ViE.Benchmark

def main (args : List String) : IO Unit := do
  let iter := args[0]? |>.bind String.toNat? |>.getD 1000
  ViE.Benchmark.runBenchmark iter
