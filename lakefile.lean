import Lake
open Lake DSL

package vie where
  version := v!"0.1.0"
  buildType := .release
  testDriver := "test"

require bliku from git "https://github.com/4kusto/bliku"

lean_lib ViE

lean_lib Test

@[default_target]
lean_exe vie where
  root := `Main

lean_exe test where
  root := `Test

lean_exe bench where
  root := `Test.Benchmark
