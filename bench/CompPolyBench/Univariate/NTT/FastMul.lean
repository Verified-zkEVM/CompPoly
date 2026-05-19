/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Common
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Univariate.NTTFast.FastMul
import CompPoly.Univariate.NTTFast.Plan

/-!
# Benchmarks for `CompPoly.Univariate.NTT.FastMul`
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Univariate.NTT.FastMul`. -/
def univariateNttFastMulGroupInfos : List BenchGroupInfo := [
  ⟨"babybear-univariate-mul", "BabyBear univariate multiplication"⟩,
  ⟨"koalabear-univariate-mul", "KoalaBear univariate multiplication"⟩
]

/-- Benchmark BabyBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runBabyBearUnivariateMul (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (mulLhsCoeffs, gen) := (babyBearArray univariateMulCoeffSlots false).run gen
  let (mulRhsCoeffs, gen) := (babyBearArray univariateMulCoeffSlots false).run gen
  let mulLhsPoly := cpolyOfArray mulLhsCoeffs
  let mulRhsPoly := cpolyOfArray mulRhsCoeffs
  let babyBearMulNttFastPlan := CPolynomial.NTTFast.Plan.ofDomain babyBearMulNttDomain
  let babyBearMulNaive ← runTimed
    "univariate-mul-naive" "CPolynomial" "mul" "BabyBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => mulLhsPoly * mulRhsPoly)
    (checksumCPolynomial checksumBabyBear)
  let babyBearMulNtt ← runTimed
    "univariate-mul-ntt" "CPolynomial" (univariateMulNttMethod "FastMul.fastMulImpl")
    "BabyBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => CPolynomial.NTT.FastMul.fastMulImpl babyBearMulNttDomain mulLhsPoly mulRhsPoly)
    (checksumCPolynomial checksumBabyBear)
  let babyBearMulNttFast ← runTimed
    "univariate-mul-ntt-fast" "CPolynomial" (univariateMulNttMethod "NTTFast.fastMulImpl")
    "BabyBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => CPolynomial.NTTFast.fastMulImpl babyBearMulNttDomain mulLhsPoly mulRhsPoly)
    (checksumCPolynomial checksumBabyBear)
  let babyBearMulNttFastPlanRecord ← runTimed
    "univariate-mul-ntt-fast-plan" "CPolynomial"
    (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward")
    "BabyBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => CPolynomial.NTTFast.Plan.fastMulImpl babyBearMulNttFastPlan mulLhsPoly
      mulRhsPoly)
    (checksumCPolynomial checksumBabyBear)
  pure ({
    groupKey := "babybear-univariate-mul",
    title := "BabyBear univariate multiplication",
    records := #[babyBearMulNaive, babyBearMulNtt, babyBearMulNttFast,
      babyBearMulNttFastPlanRecord]
  }, gen)

/-- Benchmark KoalaBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runKoalaBearUnivariateMul (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (koalaMulLhsCoeffs, gen) := (koalaBearArray univariateMulCoeffSlots false).run gen
  let (koalaMulRhsCoeffs, gen) := (koalaBearArray univariateMulCoeffSlots false).run gen
  let koalaMulLhsPoly := cpolyOfArray koalaMulLhsCoeffs
  let koalaMulRhsPoly := cpolyOfArray koalaMulRhsCoeffs
  let koalaBearMulNttFastPlan := CPolynomial.NTTFast.Plan.ofDomain koalaBearMulNttDomain
  let koalaMulNaive ← runTimed
    "univariate-mul-naive-koalabear" "CPolynomial" "mul" "KoalaBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => koalaMulLhsPoly * koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear)
  let koalaMulNtt ← runTimed
    "univariate-mul-ntt-koalabear" "CPolynomial"
    (univariateMulNttMethod "FastMul.fastMulImpl")
    "KoalaBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => CPolynomial.NTT.FastMul.fastMulImpl koalaBearMulNttDomain koalaMulLhsPoly
      koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear)
  let koalaMulNttFast ← runTimed
    "univariate-mul-ntt-fast-koalabear" "CPolynomial"
    (univariateMulNttMethod "NTTFast.fastMulImpl")
    "KoalaBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => CPolynomial.NTTFast.fastMulImpl koalaBearMulNttDomain koalaMulLhsPoly
      koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear)
  let koalaMulNttFastPlanRecord ← runTimed
    "univariate-mul-ntt-fast-plan-koalabear" "CPolynomial"
    (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward")
    "KoalaBear.Field"
    univariateMulShape mulWarmupIterations mulMeasuredIterations
    (fun _ => CPolynomial.NTTFast.Plan.fastMulImpl koalaBearMulNttFastPlan koalaMulLhsPoly
      koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear)
  pure ({
    groupKey := "koalabear-univariate-mul",
    title := "KoalaBear univariate multiplication",
    records := #[koalaMulNaive, koalaMulNtt, koalaMulNttFast, koalaMulNttFastPlanRecord]
  }, gen)

/-- Runnable `CompPoly.Univariate.NTT.FastMul` benchmark tasks. -/
def univariateNttFastMulTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"babybear-univariate-mul", "BabyBear univariate multiplication"⟩
    runBabyBearUnivariateMul,
  BenchTask.fromGroupRunner
    ⟨"koalabear-univariate-mul", "KoalaBear univariate multiplication"⟩
    runKoalaBearUnivariateMul
]

/-- Benchmark direct univariate multiplication and root-of-unity NTT variants. -/
def runUnivariateNttFastMul (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulTasks selection gen

end CompPolyBench
