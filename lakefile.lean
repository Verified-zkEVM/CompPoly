import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.29.1"

@[default_target]
lean_lib CompPoly

lean_lib CompPolyTests where
  srcDir := "tests"

lean_exe CompPolyBench where
  srcDir := "bench"
