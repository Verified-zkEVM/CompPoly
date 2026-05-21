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
  ⟨"multilinear-coeff-koalabear", "Multilinear coefficient-form evaluation (KoalaBear)"⟩,
  ⟨"multilinear-hypercube-koalabear", "Multilinear hypercube-form evaluation (KoalaBear)"⟩,
  ⟨"multilinear-coeff-goldilocks", "Multilinear coefficient-form evaluation (Goldilocks)"⟩,
  ⟨"multilinear-hypercube-goldilocks",
    "Multilinear hypercube-form evaluation (Goldilocks)"⟩
]

/-- Run KoalaBear coefficient-form multilinear evaluation benchmarks. -/
private def runKoalaBearMultilinearCoeff (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (coeffs, gen) := (koalaBearVector 256 false).run gen
  let (points, gen) := (koalaBearPoints 256).run gen
  let coeffPoly : CMlPolynomial KoalaBear.Field 8 := CMlPolynomial.ofArray coeffs 8
  let evalPoint (offset : Nat) : Vector KoalaBear.Field 8 :=
    Vector.ofFn fun j ↦ points.getD ((offset + j.val) % points.size) 0
  let fastCoeffs := koalaBearFastArray coeffs
  let fastPoints := koalaBearFastArray points
  let fastCoeffPoly : CMlPolynomial KoalaBear.Fast.Element 8 := CMlPolynomial.ofArray fastCoeffs 8
  let fastEvalPoint (offset : Nat) : Vector KoalaBear.Fast.Element 8 :=
    Vector.ofFn fun j ↦ fastPoints.getD ((offset + j.val) % fastPoints.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 120000 17000 3500
  let fastMeasured := preset.selectNat 7000 1000 200
  let fastHornerMeasured := preset.selectNat 245000 35000 7000
  let checksumIterations := groupChecksumIterations measured [
    hornerMeasured, fastMeasured, fastHornerMeasured
  ]
  let coeffEval ← runTimed
    "multilinear-coeff-eval" "CMlPolynomial" "eval" "KoalaBear.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup measured
    (fun i ↦ CMlPolynomial.eval coeffPoly (evalPoint (i % 32)))
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastCoeffEval ← runTimed
    "multilinear-coeff-eval-fast" "CMlPolynomial" "eval" "KoalaBear.Fast.Element"
    "8 vars, 256 coefficients, 32 points" preset warmup fastMeasured
    (fun i ↦ CMlPolynomial.eval fastCoeffPoly (fastEvalPoint (i % 32)))
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  let coeffHorner ← runTimed
    "multilinear-coeff-horner" "CMlPolynomial" "evalHorner" "KoalaBear.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup hornerMeasured
    (fun i ↦ CMlPolynomial.evalHorner coeffPoly (evalPoint (i % 32)))
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastCoeffHorner ← runTimed
    "multilinear-coeff-horner-fast" "CMlPolynomial" "evalHorner"
    "KoalaBear.Fast.Element"
    "8 vars, 256 coefficients, 32 points" preset warmup fastHornerMeasured
    (fun i ↦ CMlPolynomial.evalHorner fastCoeffPoly (fastEvalPoint (i % 32)))
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-coeff-koalabear",
    title := "Multilinear coefficient-form evaluation (KoalaBear)",
    records := #[coeffEval, coeffHorner, fastCoeffEval, fastCoeffHorner]
  }, gen)

/-- Run KoalaBear hypercube-form multilinear evaluation benchmarks. -/
private def runKoalaBearMultilinearHypercube (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (evals, gen) := (koalaBearVector 256 false).run gen
  let (points, gen) := (koalaBearPoints 256).run gen
  let evalPoly : CMlPolynomialEval KoalaBear.Field 8 := CMlPolynomialEval.ofArray evals 8
  let evalPoint (offset : Nat) : Vector KoalaBear.Field 8 :=
    Vector.ofFn fun j ↦ points.getD ((offset + j.val) % points.size) 0
  let fastEvals := koalaBearFastArray evals
  let fastPoints := koalaBearFastArray points
  let fastEvalPoly : CMlPolynomialEval KoalaBear.Fast.Element 8 :=
    CMlPolynomialEval.ofArray fastEvals 8
  let fastEvalPoint (offset : Nat) : Vector KoalaBear.Fast.Element 8 :=
    Vector.ofFn fun j ↦ fastPoints.getD ((offset + j.val) % fastPoints.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let mleMeasured := preset.selectNat 90000 13000 2500
  let fastMeasured := preset.selectNat 8400 1200 240
  let fastMleMeasured := preset.selectNat 280000 40000 8000
  let checksumIterations := groupChecksumIterations measured [
    mleMeasured, fastMeasured, fastMleMeasured
  ]
  let hypercubeEval ← runTimed
    "multilinear-hypercube-eval" "CMlPolynomialEval" "eval" "KoalaBear.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup measured
    (fun i ↦ CMlPolynomialEval.eval evalPoly (evalPoint (i % 32)))
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastHypercubeEval ← runTimed
    "multilinear-hypercube-eval-fast" "CMlPolynomialEval" "eval"
    "KoalaBear.Fast.Element"
    "8 vars, 256 hypercube values, 32 points" preset warmup fastMeasured
    (fun i ↦ CMlPolynomialEval.eval fastEvalPoly (fastEvalPoint (i % 32)))
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  let hypercubeMle ← runTimed
    "multilinear-hypercube-mle" "CMlPolynomialEval" "evalMle" "KoalaBear.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup mleMeasured
    (fun i ↦ CMlPolynomialEval.evalMle evalPoly (evalPoint (i % 32)))
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastHypercubeMle ← runTimed
    "multilinear-hypercube-mle-fast" "CMlPolynomialEval" "evalMle"
    "KoalaBear.Fast.Element"
    "8 vars, 256 hypercube values, 32 points" preset warmup fastMleMeasured
    (fun i ↦ CMlPolynomialEval.evalMle fastEvalPoly (fastEvalPoint (i % 32)))
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-hypercube-koalabear",
    title := "Multilinear hypercube-form evaluation (KoalaBear)",
    records := #[hypercubeEval, hypercubeMle, fastHypercubeEval, fastHypercubeMle]
  }, gen)

/-- Run Goldilocks coefficient-form multilinear evaluation benchmarks. -/
private def runGoldilocksMultilinearCoeff (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (goldilocksCoeffs, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let (goldilocksPoints, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let goldilocksCoeffPoly : CMlPolynomial Goldilocks.Field 8 :=
    CMlPolynomial.ofArray goldilocksCoeffs 8
  let goldilocksEvalPoint (offset : Nat) : Vector Goldilocks.Field 8 :=
    Vector.ofFn fun j ↦ goldilocksPoints.getD ((offset + j.val) % goldilocksPoints.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 32000 4500 900
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let goldilocksCoeffEval ← runTimed
    "multilinear-coeff-eval-goldilocks" "CMlPolynomial" "eval" "Goldilocks.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup measured
    (fun i ↦ CMlPolynomial.eval goldilocksCoeffPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  let goldilocksCoeffHorner ← runTimed
    "multilinear-coeff-horner-goldilocks" "CMlPolynomial" "evalHorner" "Goldilocks.Field"
    "8 vars, 256 coefficients, 32 points" preset warmup hornerMeasured
    (fun i ↦ CMlPolynomial.evalHorner goldilocksCoeffPoly (goldilocksEvalPoint (i % 32)))
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
    Vector.ofFn fun j ↦ goldilocksPoints.getD ((offset + j.val) % goldilocksPoints.size) 0
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let mleMeasured := preset.selectNat 25000 3500 700
  let checksumIterations := groupChecksumIterations measured [mleMeasured]
  let goldilocksHypercubeEval ← runTimed
    "multilinear-hypercube-eval-goldilocks" "CMlPolynomialEval" "eval" "Goldilocks.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup measured
    (fun i ↦ CMlPolynomialEval.eval goldilocksEvalPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  let goldilocksHypercubeMle ← runTimed
    "multilinear-hypercube-mle-goldilocks" "CMlPolynomialEval" "evalMle" "Goldilocks.Field"
    "8 vars, 256 hypercube values, 32 points" preset warmup mleMeasured
    (fun i ↦ CMlPolynomialEval.evalMle goldilocksEvalPoly (goldilocksEvalPoint (i % 32)))
    checksumZMod (checksumIterations := checksumIterations)
  pure ({
    groupKey := "multilinear-hypercube-goldilocks",
    title := "Multilinear hypercube-form evaluation (Goldilocks)",
    records := #[goldilocksHypercubeEval, goldilocksHypercubeMle]
  }, gen)

/-- Runnable multilinear benchmark tasks. -/
def multilinearTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"multilinear-coeff-koalabear", "Multilinear coefficient-form evaluation (KoalaBear)"⟩
    runKoalaBearMultilinearCoeff,
  BenchTask.fromGroupRunner
    ⟨"multilinear-hypercube-koalabear", "Multilinear hypercube-form evaluation (KoalaBear)"⟩
    runKoalaBearMultilinearHypercube,
  BenchTask.fromGroupRunner
    ⟨"multilinear-coeff-goldilocks", "Multilinear coefficient-form evaluation (Goldilocks)"⟩
    runGoldilocksMultilinearCoeff,
  BenchTask.fromGroupRunner
    ⟨"multilinear-hypercube-goldilocks",
      "Multilinear hypercube-form evaluation (Goldilocks)"⟩
    runGoldilocksMultilinearHypercube
]

/-- Run selected coefficient-form and hypercube-form multilinear evaluation benchmarks. -/
def runMultilinear (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks multilinearTasks preset selection gen

end CompPolyBench
