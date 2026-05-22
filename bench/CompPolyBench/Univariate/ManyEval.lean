/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Common
import CompPoly.Univariate.ManyEval

/-!
# Benchmarks for `CompPoly.Univariate.ManyEval`
-/

open CompPoly

namespace CompPolyBench

/-- Number of polynomials used by many-polynomial evaluation benchmarks. -/
private def manyEvalPolyCount : Nat := 512

/-- Number of coefficient slots per polynomial in many-polynomial benchmarks. -/
private def manyEvalCoeffSlots : Nat := 4096

/-- Input-shape label for one-point many-polynomial evaluation. -/
private def manyEvalOnePointShape : String :=
  s!"{manyEvalPolyCount} dense polys, degree<{manyEvalCoeffSlots}, one shared point"

/-- Build canonical polynomials from one flat coefficient array. -/
private def cpolysOfFlatArray {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (polyCount coeffSlots : Nat) (coeffs : Array R) : Array (CPolynomial R) := Id.run do
  let mut polys := #[]
  for j in [0:polyCount] do
    let mut polyCoeffs := #[]
    for i in [0:coeffSlots] do
      polyCoeffs := polyCoeffs.push (coeffs.getD (j * coeffSlots + i) 0)
    polys := polys.push (cpolyOfArray polyCoeffs)
  return polys

/-- Benchmark group metadata for `CompPoly.Univariate.ManyEval`. -/
def univariateManyEvalGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-many-one-point-koalabear",
    "Univariate many-polynomial one-point evaluation (KoalaBear)"⟩
]

/-- Benchmark runner for KoalaBear many-polynomial one-point evaluation. -/
private def runKoalaBearManyEvalOnePoint (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let coeffCount := manyEvalPolyCount * manyEvalCoeffSlots
  let (coeffs, gen) := (koalaBearArray coeffCount false).run gen
  let (points, gen) := (koalaBearPoints 1).run gen
  let polys := cpolysOfFlatArray manyEvalPolyCount manyEvalCoeffSlots coeffs
  let x := points.getD 0 0
  let fastCoeffs := koalaBearFastArray coeffs
  let fastPoints := koalaBearFastArray points
  let fastPolys := cpolysOfFlatArray manyEvalPolyCount manyEvalCoeffSlots fastCoeffs
  let fastX := fastPoints.getD 0 0
  let warmup := preset.selectNat 1 1 0
  let hornerMeasured := preset.selectNat 110 15 3
  let sharedPowersMeasured := preset.selectNat 110 15 3
  let fastHornerMeasured := preset.selectNat 1200 170 35
  let fastSharedPowersMeasured := preset.selectNat 2100 300 60
  let checksumIterations := groupChecksumIterations hornerMeasured [
    sharedPowersMeasured, fastHornerMeasured, fastSharedPowersMeasured
  ]
  let horner ← runTimed
    "univariate-many-one-point-horner" "Array CPolynomial" "evalManyHorner"
    "KoalaBear.Field" manyEvalOnePointShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalManyHorner polys x)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let sharedPowers ← runTimed
    "univariate-many-one-point-shared-powers-row-major" "Array CPolynomial"
    "evalManySharedPowers" "KoalaBear.Field" manyEvalOnePointShape preset warmup
    sharedPowersMeasured
    (fun _ ↦ CPolynomial.evalManySharedPowers polys x)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastHorner ← runTimed
    "univariate-many-one-point-horner-fast" "Array CPolynomial" "evalManyHorner"
    "KoalaBear.Fast.Field" manyEvalOnePointShape preset warmup fastHornerMeasured
    (fun _ ↦ CPolynomial.evalManyHorner fastPolys fastX)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let fastSharedPowers ← runTimed
    "univariate-many-one-point-shared-powers-row-major-fast" "Array CPolynomial"
    "evalManySharedPowers" "KoalaBear.Fast.Field" manyEvalOnePointShape preset warmup
    fastSharedPowersMeasured
    (fun _ ↦ CPolynomial.evalManySharedPowers fastPolys fastX)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-many-one-point-koalabear",
    title := "Univariate many-polynomial one-point evaluation (KoalaBear)",
    records := #[horner, sharedPowers, fastHorner, fastSharedPowers]
  }, gen)

/-- Benchmark suite entries for `CompPoly.Univariate.ManyEval`. -/
def univariateManyEvalTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-many-one-point-koalabear",
      "Univariate many-polynomial one-point evaluation (KoalaBear)"⟩
    runKoalaBearManyEvalOnePoint
]

/-- Execute selected many-polynomial evaluation benchmarks. -/
def runUnivariateManyEval (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateManyEvalTasks preset selection gen

end CompPolyBench
