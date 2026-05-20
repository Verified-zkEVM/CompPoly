/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Multilinear.Basic

/-!
# Multilinear Benchmarks
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Multilinear.Basic`. -/
def multilinearGroupInfos : List BenchGroupInfo := [
  ⟨"multilinear-coeff-babybear", "Multilinear coefficient-form evaluation (BabyBear)"⟩,
  ⟨"multilinear-hypercube-babybear", "Multilinear hypercube-form evaluation (BabyBear)"⟩,
  ⟨"multilinear-coeff-goldilocks", "Multilinear coefficient-form evaluation (Goldilocks)"⟩,
  ⟨"multilinear-hypercube-goldilocks",
    "Multilinear hypercube-form evaluation (Goldilocks)"⟩
]

/-- Run BabyBear coefficient-form multilinear evaluation benchmarks. -/
private def runBabyBearMultilinearCoeff (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (coeffs, gen) := (babyBearVector 256 false).run gen
  let (points, gen) := (babyBearPoints 256).run gen
  let coeffPoly : CMlPolynomial BabyBear.Field 8 := CMlPolynomial.ofArray coeffs 8
  let evalPoint (offset : Nat) : Vector BabyBear.Field 8 :=
    Vector.ofFn fun j => points.getD ((offset + j.val) % points.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 120000 17000 3500
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let coeffEval ← runTimed
    "multilinear-coeff-eval" "CMlPolynomial" "eval" "BabyBear.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup measured
    (fun i => CMlPolynomial.eval coeffPoly (evalPoint (i % 32)))
    checksumBabyBear (checksumIterations := checksumIterations)
  let coeffHorner ← runTimed
    "multilinear-coeff-horner" "CMlPolynomial" "evalHorner" "BabyBear.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup hornerMeasured
    (fun i => CMlPolynomial.evalHorner coeffPoly (evalPoint (i % 32)))
    checksumBabyBear (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-coeff-babybear",
    title := "Multilinear coefficient-form evaluation (BabyBear)",
    records := #[coeffEval, coeffHorner]
  }, gen)

/-- Run BabyBear hypercube-form multilinear evaluation benchmarks. -/
private def runBabyBearMultilinearHypercube (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (evals, gen) := (babyBearVector 256 false).run gen
  let (points, gen) := (babyBearPoints 256).run gen
  let evalPoly : CMlPolynomialEval BabyBear.Field 8 := CMlPolynomialEval.ofArray evals 8
  let evalPoint (offset : Nat) : Vector BabyBear.Field 8 :=
    Vector.ofFn fun j => points.getD ((offset + j.val) % points.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let mleMeasured := preset.selectNat 90000 13000 2500
  let checksumIterations := groupChecksumIterations measured [mleMeasured]
  let hypercubeEval ← runTimed
    "multilinear-hypercube-eval" "CMlPolynomialEval" "eval" "BabyBear.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup measured
    (fun i => CMlPolynomialEval.eval evalPoly (evalPoint (i % 32)))
    checksumBabyBear (checksumIterations := checksumIterations)
  let hypercubeMle ← runTimed
    "multilinear-hypercube-mle" "CMlPolynomialEval" "evalMle" "BabyBear.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup mleMeasured
    (fun i => CMlPolynomialEval.evalMle evalPoly (evalPoint (i % 32)))
    checksumBabyBear (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-hypercube-babybear",
    title := "Multilinear hypercube-form evaluation (BabyBear)",
    records := #[hypercubeEval, hypercubeMle]
  }, gen)

/-- Run Goldilocks coefficient-form multilinear evaluation benchmarks. -/
private def runGoldilocksMultilinearCoeff (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (goldilocksCoeffs, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let (goldilocksPoints, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let goldilocksCoeffPoly : CMlPolynomial Goldilocks.Field 8 :=
    CMlPolynomial.ofArray goldilocksCoeffs 8
  let goldilocksEvalPoint (offset : Nat) : Vector Goldilocks.Field 8 :=
    Vector.ofFn fun j => goldilocksPoints.getD ((offset + j.val) % goldilocksPoints.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 32000 4500 900
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let goldilocksCoeffEval ← runTimed
    "multilinear-coeff-eval-goldilocks" "CMlPolynomial" "eval" "Goldilocks.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup measured
    (fun i => CMlPolynomial.eval goldilocksCoeffPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  let goldilocksCoeffHorner ← runTimed
    "multilinear-coeff-horner-goldilocks" "CMlPolynomial" "evalHorner" "Goldilocks.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup hornerMeasured
    (fun i => CMlPolynomial.evalHorner goldilocksCoeffPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-coeff-goldilocks",
    title := "Multilinear coefficient-form evaluation (Goldilocks)",
    records := #[goldilocksCoeffEval, goldilocksCoeffHorner]
  }, gen)

/-- Run Goldilocks hypercube-form multilinear evaluation benchmarks. -/
private def runGoldilocksMultilinearHypercube (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (goldilocksEvals, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let (goldilocksPoints, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let goldilocksEvalPoly : CMlPolynomialEval Goldilocks.Field 8 :=
    CMlPolynomialEval.ofArray goldilocksEvals 8
  let goldilocksEvalPoint (offset : Nat) : Vector Goldilocks.Field 8 :=
    Vector.ofFn fun j => goldilocksPoints.getD ((offset + j.val) % goldilocksPoints.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let mleMeasured := preset.selectNat 25000 3500 700
  let checksumIterations := groupChecksumIterations measured [mleMeasured]
  let goldilocksHypercubeEval ← runTimed
    "multilinear-hypercube-eval-goldilocks" "CMlPolynomialEval" "eval" "Goldilocks.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup measured
    (fun i => CMlPolynomialEval.eval goldilocksEvalPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  let goldilocksHypercubeMle ← runTimed
    "multilinear-hypercube-mle-goldilocks" "CMlPolynomialEval" "evalMle" "Goldilocks.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup mleMeasured
    (fun i => CMlPolynomialEval.evalMle goldilocksEvalPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-hypercube-goldilocks",
    title := "Multilinear hypercube-form evaluation (Goldilocks)",
    records := #[goldilocksHypercubeEval, goldilocksHypercubeMle]
  }, gen)

/-- Runnable multilinear benchmark tasks. -/
def multilinearTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"multilinear-coeff-babybear", "Multilinear coefficient-form evaluation (BabyBear)"⟩
    runBabyBearMultilinearCoeff,
  BenchTask.fromGroupRunner
    ⟨"multilinear-hypercube-babybear", "Multilinear hypercube-form evaluation (BabyBear)"⟩
    runBabyBearMultilinearHypercube,
  BenchTask.fromGroupRunner
    ⟨"multilinear-coeff-goldilocks", "Multilinear coefficient-form evaluation (Goldilocks)"⟩
    runGoldilocksMultilinearCoeff,
  BenchTask.fromGroupRunner
    ⟨"multilinear-hypercube-goldilocks",
      "Multilinear hypercube-form evaluation (Goldilocks)"⟩
    runGoldilocksMultilinearHypercube
]

/-- Run coefficient-form and hypercube-form multilinear evaluation benchmarks. -/
def runMultilinear (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks multilinearTasks preset selection gen

end CompPolyBench
