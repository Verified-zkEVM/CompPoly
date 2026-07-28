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
  ⟨"univariate-mul-koalabear", "Univariate multiplication (KoalaBear)"⟩
]

/-- Display and checksum operations associated with a benchmark field. -/
private structure BenchField (F : Type*) where
  id : String
  checksum : F → Nat

/-- Benchmark KoalaBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runKoalaBearUnivariateMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mulLhsCoeffs, gen) := (koalaBearArray univariateMulCoeffSlots false).run gen
  let (mulRhsCoeffs, gen) := (koalaBearArray univariateMulCoeffSlots false).run gen
  let mulLhsPoly := cpolyOfArray mulLhsCoeffs
  let mulRhsPoly := cpolyOfArray mulRhsCoeffs
  let fastMulLhsCoeffs := koalaBearFastArray mulLhsCoeffs
  let fastMulRhsCoeffs := koalaBearFastArray mulRhsCoeffs
  let fastMulLhsPoly := cpolyOfArray fastMulLhsCoeffs
  let fastMulRhsPoly := cpolyOfArray fastMulRhsCoeffs
  let canonicalPlan := CPolynomial.NTTFast.Plan.ofDomain koalaBearMulNttDomain
  let fastPlan := CPolynomial.NTTFast.Plan.ofDomain koalaBearFastMulNttDomain
  let canonicalField : BenchField KoalaBear.Field :=
    ⟨"KoalaBear.Field", checksumKoalaBear⟩
  let fastField : BenchField KoalaBear.Fast.Field :=
    ⟨"KoalaBear.Fast.Field", checksumKoalaBearFast⟩
  let canonicalChecksum := checksumCPolynomial canonicalField.checksum
  let fastChecksum := checksumCPolynomial fastField.checksum
  let warmup := mulWarmupIterations preset
  let measured := mulMeasuredIterations preset
  let nttMeasured := preset.selectNat 200 30 5
  let nttFastMeasured := preset.selectNat 800 120 25
  let nttFastPlanMeasured := preset.selectNat 850 120 25
  let fastMeasured := preset.selectNat 210 30 6
  let fastNttMeasured := preset.selectNat 630 90 18
  let fastNttFastMeasured := preset.selectNat 2450 350 70
  let fastNttFastPlanMeasured := preset.selectNat 2450 350 70
  let checksumIterations := groupChecksumIterations measured [
    nttMeasured, nttFastMeasured, nttFastPlanMeasured, fastMeasured, fastNttMeasured,
    fastNttFastMeasured, fastNttFastPlanMeasured
  ]
  let canonicalNaive ← runTimed
    "univariate-mul-naive" "CPolynomial" "mul" canonicalField.id
    univariateMulShape preset warmup measured
    (fun _ ↦ mulLhsPoly * mulRhsPoly) canonicalChecksum
    (checksumIterations := checksumIterations)
  let fastNaive ← runTimed
    "univariate-mul-naive-fast" "CPolynomial" "mul" fastField.id
    univariateMulShape preset warmup fastMeasured
    (fun _ ↦ fastMulLhsPoly * fastMulRhsPoly) fastChecksum
    (checksumIterations := checksumIterations)
  let canonicalNtt ← runTimed
    "univariate-mul-ntt" "CPolynomial" (univariateMulNttMethod "FastMul.fastMulImpl")
    canonicalField.id univariateMulShape preset warmup nttMeasured
    (fun _ ↦
      CPolynomial.NTT.FastMul.fastMulImpl koalaBearMulNttDomain mulLhsPoly mulRhsPoly)
    canonicalChecksum (checksumIterations := checksumIterations)
  let fastNtt ← runTimed
    "univariate-mul-ntt-koalabear-fast" "CPolynomial"
    (univariateMulNttMethod "FastMul.fastMulImpl") fastField.id
    univariateMulShape preset warmup fastNttMeasured
    (fun _ ↦ CPolynomial.NTT.FastMul.fastMulImpl koalaBearFastMulNttDomain
      fastMulLhsPoly fastMulRhsPoly)
    fastChecksum (checksumIterations := checksumIterations)
  let canonicalNttFast ← runTimed
    "univariate-mul-ntt-fast" "CPolynomial" (univariateMulNttMethod "NTTFast.fastMulImpl")
    canonicalField.id univariateMulShape preset warmup nttFastMeasured
    (fun _ ↦
      CPolynomial.NTTFast.fastMulImpl koalaBearMulNttDomain mulLhsPoly mulRhsPoly)
    canonicalChecksum (checksumIterations := checksumIterations)
  let fastNttFast ← runTimed
    "univariate-mul-ntt-fast-koalabear-fast" "CPolynomial"
    (univariateMulNttMethod "NTTFast.fastMulImpl") fastField.id
    univariateMulShape preset warmup fastNttFastMeasured
    (fun _ ↦ CPolynomial.NTTFast.fastMulImpl koalaBearFastMulNttDomain
      fastMulLhsPoly fastMulRhsPoly)
    fastChecksum (checksumIterations := checksumIterations)
  let canonicalNttFastPlan ← runTimed
    "univariate-mul-ntt-fast-plan" "CPolynomial"
    (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward")
    canonicalField.id univariateMulShape preset warmup nttFastPlanMeasured
    (fun _ ↦ CPolynomial.NTTFast.Plan.fastMulImpl canonicalPlan mulLhsPoly mulRhsPoly)
    canonicalChecksum (checksumIterations := checksumIterations)
  let fastNttFastPlan ← runTimed
    "univariate-mul-ntt-fast-plan-fast" "CPolynomial"
    (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward")
    fastField.id univariateMulShape preset warmup fastNttFastPlanMeasured
    (fun _ ↦ CPolynomial.NTTFast.Plan.fastMulImpl fastPlan fastMulLhsPoly fastMulRhsPoly)
    fastChecksum (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-mul-koalabear",
    title := "Univariate multiplication (KoalaBear)",
    records := #[canonicalNaive, canonicalNtt, canonicalNttFast, canonicalNttFastPlan,
      fastNaive, fastNtt, fastNttFast, fastNttFastPlan]
  }, gen)

/-- Runnable `CompPoly.Univariate.NTT.FastMul` benchmark tasks. -/
def univariateNttFastMulTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-koalabear", "Univariate multiplication (KoalaBear)"⟩
    runKoalaBearUnivariateMul
]

/-- Run selected direct univariate multiplication and root-of-unity NTT benchmarks. -/
def runUnivariateNttFastMul (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulTasks preset selection gen

end CompPolyBench
