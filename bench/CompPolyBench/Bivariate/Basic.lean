/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.Basic
import CompPoly.Fields.BN254

/-!
# Bivariate Benchmarks
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Bivariate.Basic`. -/
def bivariateGroupInfos : List BenchGroupInfo := [
  ⟨"bivariate-full-babybear", "Bivariate full evaluation (BabyBear)"⟩,
  ⟨"bivariate-full-goldilocks", "Bivariate full evaluation (Goldilocks)"⟩,
  ⟨"bivariate-full-bn254", "Bivariate full evaluation (BN254)"⟩
]

/-- Shared input-shape label for bivariate evaluation benchmarks. -/
private def bivariateInputShape : String :=
  "xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points"

/-- Build a bivariate polynomial from generated coefficients. -/
private def buildCBivariate {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (terms : Array R) : CBivariate R :=
  Id.run do
    let mut p : CBivariate R := 0
    for i in [0:terms.size] do
      let xDegree := i % 8
      let yDegree := i / 8
      p := p + CBivariate.monomialXY xDegree yDegree (terms.getD i 0)
    pure p

/-- Run bivariate full-evaluation benchmarks over a generic prime `ZMod` field. -/
private def runBivariateZMod (modulus : Nat) [Fact (Nat.Prime modulus)]
    (key nameSuffix fieldName fieldTitle : String)
    (largeHornerYxMeasured mediumHornerYxMeasured smallHornerYxMeasured : Nat)
    (largeHornerXyMeasured mediumHornerXyMeasured smallHornerXyMeasured : Nat)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (terms, gen) := (zmodArray modulus 512 true).run gen
  let (points, gen) := (zmodArray modulus 64 false).run gen
  let poly := buildCBivariate terms
  let evalPoint (i : Nat) : ZMod modulus × ZMod modulus :=
    let offset := 2 * (i % 32)
    (points.getD (offset % points.size) 0, points.getD ((offset + 1) % points.size) 0)
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerYxMeasured :=
    preset.selectNat largeHornerYxMeasured mediumHornerYxMeasured smallHornerYxMeasured
  let hornerXyMeasured :=
    preset.selectNat largeHornerXyMeasured mediumHornerXyMeasured smallHornerXyMeasured
  let checksumIterations := groupChecksumIterations measured [
    hornerYxMeasured, hornerXyMeasured
  ]
  let naive ← runTimed
    ("bivariate-full-eval-naive" ++ nameSuffix) "CBivariate" "evalEval" fieldName
    bivariateInputShape preset warmup measured
    (fun i ↦
      let point := evalPoint i
      CBivariate.evalEval point.1 point.2 poly)
    checksumZMod (checksumIterations := checksumIterations)
  let hornerYx ← runTimed
    ("bivariate-full-eval-horner-yx" ++ nameSuffix) "CBivariate" "evalEvalHornerYThenX"
    fieldName bivariateInputShape preset warmup hornerYxMeasured
    (fun i ↦
      let point := evalPoint i
      CBivariate.evalEvalHornerYThenX point.1 point.2 poly)
    checksumZMod (checksumIterations := checksumIterations)
  let hornerXy ← runTimed
    ("bivariate-full-eval-horner-xy" ++ nameSuffix) "CBivariate" "evalEvalHornerXThenY"
    fieldName bivariateInputShape preset warmup hornerXyMeasured
    (fun i ↦
      let point := evalPoint i
      CBivariate.evalEvalHornerXThenY point.1 point.2 poly)
    checksumZMod (checksumIterations := checksumIterations)
  pure ({
      groupKey := key,
      title := "Bivariate full evaluation (" ++ fieldTitle ++ ")",
      records := #[naive, hornerYx, hornerXy] }, gen)

/-- Run the BabyBear bivariate full-evaluation benchmark. -/
private def runBabyBearBivariate (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (terms, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 64).run gen
  let p := buildCBivariate terms
  let evalPoint (i : Nat) : BabyBear.Field × BabyBear.Field :=
    let offset := 2 * (i % 32)
    (points.getD (offset % points.size) 0, points.getD ((offset + 1) % points.size) 0)
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerYxMeasured := preset.selectNat 11000 1600 300
  let hornerXyMeasured := preset.selectNat 100000 14000 3000
  let checksumIterations := groupChecksumIterations measured [
    hornerYxMeasured, hornerXyMeasured
  ]
  let naive ← runTimed
    "bivariate-full-eval-naive" "CBivariate" "evalEval" "BabyBear.Field"
    bivariateInputShape preset warmup measured
    (fun i ↦
      let point := evalPoint i
      CBivariate.evalEval point.1 point.2 p)
    checksumBabyBear (checksumIterations := checksumIterations)
  let hornerYx ← runTimed
    "bivariate-full-eval-horner-yx" "CBivariate" "evalEvalHornerYThenX" "BabyBear.Field"
    bivariateInputShape preset warmup hornerYxMeasured
    (fun i ↦
      let point := evalPoint i
      CBivariate.evalEvalHornerYThenX point.1 point.2 p)
    checksumBabyBear (checksumIterations := checksumIterations)
  let hornerXy ← runTimed
    "bivariate-full-eval-horner-xy" "CBivariate" "evalEvalHornerXThenY" "BabyBear.Field"
    bivariateInputShape preset warmup hornerXyMeasured
    (fun i ↦
      let point := evalPoint i
      CBivariate.evalEvalHornerXThenY point.1 point.2 p)
    checksumBabyBear (checksumIterations := checksumIterations)
  pure ({
    groupKey := "bivariate-full-babybear",
    title := "Bivariate full evaluation (BabyBear)",
    records := #[naive, hornerYx, hornerXy]
  }, gen)

/-- Run the Goldilocks bivariate full-evaluation benchmark. -/
private def runGoldilocksBivariate (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runBivariateZMod
    Goldilocks.fieldSize "bivariate-full-goldilocks" "-goldilocks" "Goldilocks.Field"
    "Goldilocks" 12000 1700 350 30000 4500 900 preset gen

/-- Run the BN254 bivariate full-evaluation benchmark. -/
private def runBn254Bivariate (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runBivariateZMod
    BN254.scalarFieldSize "bivariate-full-bn254" "-bn254" "BN254.ScalarField" "BN254"
    12000 1700 350 27000 4000 800 preset gen

/-- Runnable bivariate benchmark tasks. -/
def bivariateTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"bivariate-full-babybear", "Bivariate full evaluation (BabyBear)"⟩
    runBabyBearBivariate,
  BenchTask.fromGroupRunner
    ⟨"bivariate-full-goldilocks", "Bivariate full evaluation (Goldilocks)"⟩
    runGoldilocksBivariate,
  BenchTask.fromGroupRunner
    ⟨"bivariate-full-bn254", "Bivariate full evaluation (BN254)"⟩
    runBn254Bivariate
]

/-- Run selected bivariate full-evaluation benchmarks. -/
def runBivariate (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks bivariateTasks preset selection gen

end CompPolyBench
