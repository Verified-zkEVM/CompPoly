/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Univariate.Basic
public import CompPolyBench.Univariate.BatchEval
public import CompPolyBench.Univariate.ManyEval
public import CompPolyBench.Univariate.NTT.FastMul
public import CompPolyBench.Univariate.NTT.FastMulLow
public import CompPolyBench.Univariate.Roots.FiniteField

/-!
# Univariate Benchmarks
-/

public section

namespace CompPolyBench

/-- Benchmark group metadata for all univariate benchmark modules. -/
def univariateGroupInfos : List BenchGroupInfo :=
  univariateBasicGroupInfos ++ univariateBatchEvalGroupInfos ++
    univariateManyEvalGroupInfos ++ univariateNttFastMulGroupInfos ++
    univariateNttFastMulLowGroupInfos ++ univariateFiniteFieldRootGroupInfos

/-- Runnable univariate benchmark tasks. -/
def univariateTasks : List BenchTask :=
  univariateBasicTasks ++ univariateBatchEvalTasks ++
    univariateManyEvalTasks ++ univariateNttFastMulTasks ++
    univariateNttFastMulLowTasks ++ univariateFiniteFieldRootTasks

/-- Run selected univariate benchmarks. -/
def runUnivariate (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateTasks preset selection gen

end CompPolyBench
