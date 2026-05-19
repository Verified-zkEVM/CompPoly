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
private def runBivariateZMod (p : Nat) [Fact (Nat.Prime p)]
    (key nameSuffix fieldName fieldTitle : String) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (terms, gen) := (zmodArray p 512 true).run gen
  let (points, gen) := (zmodArray p 64 false).run gen
  let poly := buildCBivariate terms
  let evalPoint (i : Nat) : ZMod p × ZMod p :=
    let offset := 2 * (i % 32)
    (points.getD (offset % points.size) 0, points.getD ((offset + 1) % points.size) 0)
  let naive ← runTimed
    ("bivariate-full-eval-naive" ++ nameSuffix) "CBivariate" "evalEval" fieldName
    bivariateInputShape warmupIterations measuredIterations
    (fun i =>
      let point := evalPoint i
      CBivariate.evalEval point.1 point.2 poly)
    checksumZMod
  let hornerYx ← runTimed
    ("bivariate-full-eval-horner-yx" ++ nameSuffix) "CBivariate" "evalEvalHornerYThenX"
    fieldName bivariateInputShape warmupIterations measuredIterations
    (fun i =>
      let point := evalPoint i
      CBivariate.evalEvalHornerYThenX point.1 point.2 poly)
    checksumZMod
  let hornerXy ← runTimed
    ("bivariate-full-eval-horner-xy" ++ nameSuffix) "CBivariate" "evalEvalHornerXThenY"
    fieldName bivariateInputShape warmupIterations measuredIterations
    (fun i =>
      let point := evalPoint i
      CBivariate.evalEvalHornerXThenY point.1 point.2 poly)
    checksumZMod
  pure ({
      groupKey := key,
      title := "Bivariate full evaluation (" ++ fieldTitle ++ ")",
      records := #[naive, hornerYx, hornerXy] }, gen)

/-- Run the BabyBear bivariate full-evaluation benchmark. -/
private def runBabyBearBivariate (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (terms, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 64).run gen
  let p := buildCBivariate terms
  let evalPoint (i : Nat) : BabyBear.Field × BabyBear.Field :=
    let offset := 2 * (i % 32)
    (points.getD (offset % points.size) 0, points.getD ((offset + 1) % points.size) 0)
  let naive ← runTimed
    "bivariate-full-eval-naive" "CBivariate" "evalEval" "BabyBear.Field"
    bivariateInputShape warmupIterations measuredIterations
    (fun i =>
      let point := evalPoint i
      CBivariate.evalEval point.1 point.2 p)
    checksumBabyBear
  let hornerYx ← runTimed
    "bivariate-full-eval-horner-yx" "CBivariate" "evalEvalHornerYThenX" "BabyBear.Field"
    bivariateInputShape warmupIterations measuredIterations
    (fun i =>
      let point := evalPoint i
      CBivariate.evalEvalHornerYThenX point.1 point.2 p)
    checksumBabyBear
  let hornerXy ← runTimed
    "bivariate-full-eval-horner-xy" "CBivariate" "evalEvalHornerXThenY" "BabyBear.Field"
    bivariateInputShape warmupIterations measuredIterations
    (fun i =>
      let point := evalPoint i
      CBivariate.evalEvalHornerXThenY point.1 point.2 p)
    checksumBabyBear
  pure ({
    groupKey := "bivariate-full-babybear",
    title := "Bivariate full evaluation (BabyBear)",
    records := #[naive, hornerYx, hornerXy]
  }, gen)

/-- Run the Goldilocks bivariate full-evaluation benchmark. -/
private def runGoldilocksBivariate (gen : StdGen) : IO (BenchGroup × StdGen) := do
  runBivariateZMod
    Goldilocks.fieldSize "bivariate-full-goldilocks" "-goldilocks" "Goldilocks.Field"
    "Goldilocks" gen

/-- Run the BN254 bivariate full-evaluation benchmark. -/
private def runBn254Bivariate (gen : StdGen) : IO (BenchGroup × StdGen) := do
  runBivariateZMod
    BN254.scalarFieldSize "bivariate-full-bn254" "-bn254" "BN254.ScalarField" "BN254" gen

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

/-- Run the bivariate full-evaluation benchmark. -/
def runBivariate (selection : BenchSelection) (gen : StdGen) : IO (Array BenchGroup × StdGen) := do
  runSelectedTasks bivariateTasks selection gen

end CompPolyBench
