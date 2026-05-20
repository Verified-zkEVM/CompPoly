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
  ⟨"univariate-mul-babybear", "Univariate multiplication (BabyBear)"⟩,
  ⟨"univariate-mul-koalabear", "Univariate multiplication (KoalaBear)"⟩
]

/-- Benchmark BabyBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runBabyBearUnivariateMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mulLhsCoeffs, gen) := (babyBearArray univariateMulCoeffSlots false).run gen
  let (mulRhsCoeffs, gen) := (babyBearArray univariateMulCoeffSlots false).run gen
  let mulLhsPoly := cpolyOfArray mulLhsCoeffs
  let mulRhsPoly := cpolyOfArray mulRhsCoeffs
  let babyBearMulNttFastPlan := CPolynomial.NTTFast.Plan.ofDomain babyBearMulNttDomain
  let warmup := mulWarmupIterations preset
  let measured := mulMeasuredIterations preset
  let nttMeasured := preset.selectNat 200 30 5
  let nttFastMeasured := preset.selectNat 800 120 25
  let nttFastPlanMeasured := preset.selectNat 850 120 25
  let checksumIterations := groupChecksumIterations measured [
    nttMeasured, nttFastMeasured, nttFastPlanMeasured
  ]
  let babyBearMulNaive ← runTimed
    "univariate-mul-naive" "CPolynomial" "mul" "BabyBear.Field"
    univariateMulShape preset warmup measured
    (fun _ => mulLhsPoly * mulRhsPoly)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let babyBearMulNtt ← runTimed
    "univariate-mul-ntt" "CPolynomial" (univariateMulNttMethod "FastMul.fastMulImpl")
    "BabyBear.Field"
    univariateMulShape preset warmup nttMeasured
    (fun _ => CPolynomial.NTT.FastMul.fastMulImpl babyBearMulNttDomain mulLhsPoly mulRhsPoly)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let babyBearMulNttFast ← runTimed
    "univariate-mul-ntt-fast" "CPolynomial" (univariateMulNttMethod "NTTFast.fastMulImpl")
    "BabyBear.Field"
    univariateMulShape preset warmup nttFastMeasured
    (fun _ => CPolynomial.NTTFast.fastMulImpl babyBearMulNttDomain mulLhsPoly mulRhsPoly)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let babyBearMulNttFastPlanRecord ← runTimed
    "univariate-mul-ntt-fast-plan" "CPolynomial"
    (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward")
    "BabyBear.Field"
    univariateMulShape preset warmup nttFastPlanMeasured
    (fun _ => CPolynomial.NTTFast.Plan.fastMulImpl babyBearMulNttFastPlan mulLhsPoly
      mulRhsPoly)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-mul-babybear",
    title := "Univariate multiplication (BabyBear)",
    records := #[babyBearMulNaive, babyBearMulNtt, babyBearMulNttFast,
      babyBearMulNttFastPlanRecord]
  }, gen)

/-- Benchmark KoalaBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runKoalaBearUnivariateMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (koalaMulLhsCoeffs, gen) := (koalaBearArray univariateMulCoeffSlots false).run gen
  let (koalaMulRhsCoeffs, gen) := (koalaBearArray univariateMulCoeffSlots false).run gen
  let koalaMulLhsPoly := cpolyOfArray koalaMulLhsCoeffs
  let koalaMulRhsPoly := cpolyOfArray koalaMulRhsCoeffs
  let koalaBearMulNttFastPlan := CPolynomial.NTTFast.Plan.ofDomain koalaBearMulNttDomain
  let warmup := mulWarmupIterations preset
  let measured := mulMeasuredIterations preset
  let nttMeasured := preset.selectNat 200 30 5
  let nttFastMeasured := preset.selectNat 700 100 20
  let nttFastPlanMeasured := preset.selectNat 800 120 25
  let checksumIterations := groupChecksumIterations measured [
    nttMeasured, nttFastMeasured, nttFastPlanMeasured
  ]
  let koalaMulNaive ← runTimed
    "univariate-mul-naive-koalabear" "CPolynomial" "mul" "KoalaBear.Field"
    univariateMulShape preset warmup measured
    (fun _ => koalaMulLhsPoly * koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let koalaMulNtt ← runTimed
    "univariate-mul-ntt-koalabear" "CPolynomial"
    (univariateMulNttMethod "FastMul.fastMulImpl")
    "KoalaBear.Field"
    univariateMulShape preset warmup nttMeasured
    (fun _ => CPolynomial.NTT.FastMul.fastMulImpl koalaBearMulNttDomain koalaMulLhsPoly
      koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let koalaMulNttFast ← runTimed
    "univariate-mul-ntt-fast-koalabear" "CPolynomial"
    (univariateMulNttMethod "NTTFast.fastMulImpl")
    "KoalaBear.Field"
    univariateMulShape preset warmup nttFastMeasured
    (fun _ => CPolynomial.NTTFast.fastMulImpl koalaBearMulNttDomain koalaMulLhsPoly
      koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let koalaMulNttFastPlanRecord ← runTimed
    "univariate-mul-ntt-fast-plan-koalabear" "CPolynomial"
    (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward")
    "KoalaBear.Field"
    univariateMulShape preset warmup nttFastPlanMeasured
    (fun _ => CPolynomial.NTTFast.Plan.fastMulImpl koalaBearMulNttFastPlan koalaMulLhsPoly
      koalaMulRhsPoly)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-mul-koalabear",
    title := "Univariate multiplication (KoalaBear)",
    records := #[koalaMulNaive, koalaMulNtt, koalaMulNttFast, koalaMulNttFastPlanRecord]
  }, gen)

/-- Runnable `CompPoly.Univariate.NTT.FastMul` benchmark tasks. -/
def univariateNttFastMulTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-babybear", "Univariate multiplication (BabyBear)"⟩
    runBabyBearUnivariateMul,
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-koalabear", "Univariate multiplication (KoalaBear)"⟩
    runKoalaBearUnivariateMul
]

/-- Benchmark direct univariate multiplication and root-of-unity NTT variants. -/
def runUnivariateNttFastMul (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulTasks preset selection gen

end CompPolyBench
