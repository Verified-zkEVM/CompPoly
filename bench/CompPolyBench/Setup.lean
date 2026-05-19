/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.Basic
import CompPolyBench.Fields.Binary.AdditiveNTT.Impl
import CompPolyBench.Multilinear.Basic
import CompPolyBench.Multivariate.CMvPolynomial
import CompPolyBench.Univariate

/-!
# Benchmark Suite Setup

Top-level orchestration for the compiled benchmark executable.
-/

namespace CompPolyBench

/-- Run the complete benchmark suite and write reports. -/
def run : IO UInt32 := do
  let runId ← makeRunId
  let hardware ← collectRunnerHardware
  let mut gen := mkStdGen seed
  let mut groups := #[]
  let (univariateGroups, gen') ← runUnivariate gen
  gen := gen'
  groups := appendGroups groups univariateGroups
  let (multivariateGroups, gen') ← runMultivariate gen
  gen := gen'
  groups := appendGroups groups multivariateGroups
  let (multilinearGroups, gen') ← runMultilinear gen
  gen := gen'
  groups := appendGroups groups multilinearGroups
  let (bivariateGroups, gen') ← runBivariate gen
  gen := gen'
  groups := appendGroups groups bivariateGroups
  let (nttGroups, _) ← runAdditiveNtt gen
  groups := appendGroups groups nttGroups
  let records := flattenGroups groups
  let results := resultsPath runId
  let report := reportPath runId
  IO.FS.writeFile results (renderJsonl records)
  IO.FS.writeFile report (renderMarkdown hardware groups)
  IO.println s!"wrote `{records.size}` benchmark records in `{groups.size}` groups for run `{runId}`"
  pure 0

end CompPolyBench
