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
private def runBabyBearMultilinearCoeff (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (coeffs, gen) := (babyBearVector 256 false).run gen
  let (points, gen) := (babyBearPoints 256).run gen
  let coeffPoly : CMlPolynomial BabyBear.Field 8 := CMlPolynomial.ofArray coeffs 8
  let evalPoint (offset : Nat) : Vector BabyBear.Field 8 :=
    Vector.ofFn fun j => points.getD ((offset + j.val) % points.size) 0
  let coeffEval ← runTimed
    "multilinear-coeff-eval" "CMlPolynomial" "eval" "BabyBear.Field"
    "8 vars, 256 coefficients, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomial.eval coeffPoly (evalPoint (i % 32)))
    checksumBabyBear
  let coeffHorner ← runTimed
    "multilinear-coeff-horner" "CMlPolynomial" "evalHorner" "BabyBear.Field"
    "8 vars, 256 coefficients, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomial.evalHorner coeffPoly (evalPoint (i % 32)))
    checksumBabyBear
  pure ({
    groupKey := "multilinear-coeff-babybear",
    title := "Multilinear coefficient-form evaluation (BabyBear)",
    records := #[coeffEval, coeffHorner]
  }, gen)

/-- Run BabyBear hypercube-form multilinear evaluation benchmarks. -/
private def runBabyBearMultilinearHypercube (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (evals, gen) := (babyBearVector 256 false).run gen
  let (points, gen) := (babyBearPoints 256).run gen
  let evalPoly : CMlPolynomialEval BabyBear.Field 8 := CMlPolynomialEval.ofArray evals 8
  let evalPoint (offset : Nat) : Vector BabyBear.Field 8 :=
    Vector.ofFn fun j => points.getD ((offset + j.val) % points.size) 0
  let hypercubeEval ← runTimed
    "multilinear-hypercube-eval" "CMlPolynomialEval" "eval" "BabyBear.Field"
    "8 vars, 256 hypercube values, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomialEval.eval evalPoly (evalPoint (i % 32)))
    checksumBabyBear
  let hypercubeMle ← runTimed
    "multilinear-hypercube-mle" "CMlPolynomialEval" "evalMle" "BabyBear.Field"
    "8 vars, 256 hypercube values, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomialEval.evalMle evalPoly (evalPoint (i % 32)))
    checksumBabyBear
  pure ({
    groupKey := "multilinear-hypercube-babybear",
    title := "Multilinear hypercube-form evaluation (BabyBear)",
    records := #[hypercubeEval, hypercubeMle]
  }, gen)

/-- Run Goldilocks coefficient-form multilinear evaluation benchmarks. -/
private def runGoldilocksMultilinearCoeff (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (goldilocksCoeffs, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let (goldilocksPoints, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let goldilocksCoeffPoly : CMlPolynomial Goldilocks.Field 8 :=
    CMlPolynomial.ofArray goldilocksCoeffs 8
  let goldilocksEvalPoint (offset : Nat) : Vector Goldilocks.Field 8 :=
    Vector.ofFn fun j => goldilocksPoints.getD ((offset + j.val) % goldilocksPoints.size) 0
  let goldilocksCoeffEval ← runTimed
    "multilinear-coeff-eval-goldilocks" "CMlPolynomial" "eval" "Goldilocks.Field"
    "8 vars, 256 coefficients, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomial.eval goldilocksCoeffPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod
  let goldilocksCoeffHorner ← runTimed
    "multilinear-coeff-horner-goldilocks" "CMlPolynomial" "evalHorner" "Goldilocks.Field"
    "8 vars, 256 coefficients, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomial.evalHorner goldilocksCoeffPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod
  pure ({
    groupKey := "multilinear-coeff-goldilocks",
    title := "Multilinear coefficient-form evaluation (Goldilocks)",
    records := #[goldilocksCoeffEval, goldilocksCoeffHorner]
  }, gen)

/-- Run Goldilocks hypercube-form multilinear evaluation benchmarks. -/
private def runGoldilocksMultilinearHypercube (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (goldilocksEvals, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let (goldilocksPoints, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let goldilocksEvalPoly : CMlPolynomialEval Goldilocks.Field 8 :=
    CMlPolynomialEval.ofArray goldilocksEvals 8
  let goldilocksEvalPoint (offset : Nat) : Vector Goldilocks.Field 8 :=
    Vector.ofFn fun j => goldilocksPoints.getD ((offset + j.val) % goldilocksPoints.size) 0
  let goldilocksHypercubeEval ← runTimed
    "multilinear-hypercube-eval-goldilocks" "CMlPolynomialEval" "eval" "Goldilocks.Field"
    "8 vars, 256 hypercube values, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomialEval.eval goldilocksEvalPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod
  let goldilocksHypercubeMle ← runTimed
    "multilinear-hypercube-mle-goldilocks" "CMlPolynomialEval" "evalMle" "Goldilocks.Field"
    "8 vars, 256 hypercube values, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomialEval.evalMle goldilocksEvalPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod
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
def runMultilinear (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks multilinearTasks selection gen

end CompPolyBench
