import Lake
open Lake DSL

package vie where
  version := v!"0.1.0"
  buildType := .release
  testDriver := "test"

require bliku from git "https://github.com/4kusto/bliku" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib ViE

lean_lib Test

lean_lib Proof

@[default_target]
lean_exe vie where
  root := `Main

lean_exe test where
  root := `Test

lean_exe bench where
  root := `Test.Benchmark

lean_exe proof where
  root := `Proof.Main
