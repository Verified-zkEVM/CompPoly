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

/-- Benchmark group metadata for all univariate benchmark modules. -/
def univariateGroupInfos : List BenchGroupInfo :=
  univariateBasicGroupInfos ++ univariateBatchEvalGroupInfos ++
    univariateNttFastMulGroupInfos ++ univariateNttFastMulLowGroupInfos

/-- Runnable univariate benchmark tasks. -/
def univariateTasks : List BenchTask :=
  univariateBasicTasks ++ univariateBatchEvalTasks ++
    univariateNttFastMulTasks ++ univariateNttFastMulLowTasks

/-- Run all univariate benchmarks. -/
def runUnivariate (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateTasks preset selection gen

end CompPolyBench
