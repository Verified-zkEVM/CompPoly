/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Basic
import CompPolyBench.Univariate.BatchEval
import CompPolyBench.Univariate.EuclideanAlgorithm
import CompPolyBench.Univariate.ManyEval
import CompPolyBench.Univariate.NTT.FastMul
import CompPolyBench.Univariate.NTT.FastMulLow
import CompPolyBench.Univariate.Roots.FiniteField

/-!
# Univariate Benchmarks
-/

namespace CompPolyBench

/-- Benchmark group metadata for all univariate benchmark modules. -/
def univariateGroupInfos : List BenchGroupInfo :=
  [
    univariateBasicGroupInfos,
    univariateBatchEvalGroupInfos,
    univariateEuclideanAlgorithmGroupInfos,
    univariateManyEvalGroupInfos,
    univariateNttFastMulGroupInfos,
    univariateNttFastMulLowGroupInfos,
    univariateFiniteFieldRootGroupInfos
  ].flatten

/-- Runnable univariate benchmark tasks. -/
def univariateTasks : List BenchTask :=
  [
    univariateBasicTasks,
    univariateBatchEvalTasks,
    univariateEuclideanAlgorithmTasks,
    univariateManyEvalTasks,
    univariateNttFastMulTasks,
    univariateNttFastMulLowTasks,
    univariateFiniteFieldRootTasks
  ].flatten

/-- Run selected univariate benchmarks. -/
def runUnivariate (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateTasks preset selection gen

end CompPolyBench
