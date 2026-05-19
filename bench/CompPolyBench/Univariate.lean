/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Basic
import CompPolyBench.Univariate.BatchEval
import CompPolyBench.Univariate.NTT.FastMul
import CompPolyBench.Univariate.NTT.FastMulLow

/-!
# Univariate Benchmarks
-/

namespace CompPolyBench

/-- Run all univariate benchmarks. -/
def runUnivariate (gen : StdGen) : IO (Array BenchGroup × StdGen) := do
  let (basicGroups, gen) ← runUnivariateBasic gen
  let (fastMulGroups, gen) ← runUnivariateNttFastMul gen
  let (fastMulLowGroups, gen) ← runUnivariateNttFastMulLow gen
  let (batchGroups, gen) ← runUnivariateBatchEval gen
  let groups := appendGroups (appendGroups (appendGroups basicGroups fastMulGroups) fastMulLowGroups)
    batchGroups
  pure (groups, gen)

end CompPolyBench
