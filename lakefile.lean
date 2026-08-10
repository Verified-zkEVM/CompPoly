import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.32.0"

@[default_target]
lean_lib CompPoly

lean_lib CompPolyTests where
  srcDir := "tests"

lean_lib CompPolyBenchLib where
  srcDir := "bench"
  globs := #[Glob.submodules `CompPolyBench]

lean_exe CompPolyBench where
  srcDir := "bench"

/-- Kernel-level axiom / `sorry` accounting with a committed regression baseline
(`scripts/axiom_baseline.json`). Runtime-imports the built CompPoly oleans, so run it
after `lake build`. See `scripts/AxiomSweep.lean`. -/
lean_exe axiomsweep where
  srcDir := "scripts"
  root := `AxiomSweep
  supportInterpreter := true
