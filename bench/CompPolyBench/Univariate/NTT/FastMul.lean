/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.NTT.FastMul
public import CompPoly.Univariate.NTTFast.FastMul
public import CompPoly.Univariate.NTTFast.Plan

/-!
# Benchmarks for `CompPoly.Univariate.NTT.FastMul`
-/

public section

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Univariate.NTT.FastMul`. -/
def univariateNttFastMulGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-mul-koalabear", "Univariate multiplication (KoalaBear)"⟩,
  ⟨"univariate-mul-babybear", "Univariate multiplication (BabyBear)"⟩
]

/-- Display and checksum operations associated with a benchmark field. -/
private structure BenchField (F : Type*) where
  id : String
  checksum : F → Nat

/-- Per-preset measured iteration budgets for the direct multiplication group. The
canonical naive row uses the shared `mulMeasuredIterations` budget. -/
private structure MulBudgets where
  ntt : BenchPreset → Nat
  nttFast : BenchPreset → Nat
  nttFastPlan : BenchPreset → Nat
  fastNaive : BenchPreset → Nat
  fastNtt : BenchPreset → Nat
  fastNttFast : BenchPreset → Nat
  fastNttFastPlan : BenchPreset → Nat

/-- Benchmark direct univariate multiplication and root-of-unity NTT variants over a
canonical field and its native-word counterpart. `slug` distinguishes the two
native-word NTT row names, whose canonical-representation names are already taken. -/
private def runUnivariateMulWithFast {F G : Type}
    [Field F] [BEq F] [LawfulBEq F] [Field G] [BEq G] [LawfulBEq G]
    (key fieldTitle slug : String)
    (canonicalField : BenchField F) (fastField : BenchField G)
    (genCoeffs : Nat → StateM StdGen (Array F)) (toFast : Array F → Array G)
    (canonicalDomain : CPolynomial.NTT.Domain F) (fastDomain : CPolynomial.NTT.Domain G)
    (budgets : MulBudgets) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mulLhsCoeffs, gen) := (genCoeffs univariateMulCoeffSlots).run gen
  let (mulRhsCoeffs, gen) := (genCoeffs univariateMulCoeffSlots).run gen
  let mulLhsPoly := cpolyOfArray mulLhsCoeffs
  let mulRhsPoly := cpolyOfArray mulRhsCoeffs
  let fastMulLhsCoeffs := toFast mulLhsCoeffs
  let fastMulRhsCoeffs := toFast mulRhsCoeffs
  let fastMulLhsPoly := cpolyOfArray fastMulLhsCoeffs
  let fastMulRhsPoly := cpolyOfArray fastMulRhsCoeffs
  let canonicalPlan := CPolynomial.NTTFast.Plan.ofDomain canonicalDomain
  let fastPlan := CPolynomial.NTTFast.Plan.ofDomain fastDomain
  let canonicalChecksum := checksumCPolynomial canonicalField.checksum
  let fastChecksum := checksumCPolynomial fastField.checksum
  let warmup := mulWarmupIterations preset
  let measured := mulMeasuredIterations preset
  let nttMeasured := budgets.ntt preset
  let nttFastMeasured := budgets.nttFast preset
  let nttFastPlanMeasured := budgets.nttFastPlan preset
  let fastMeasured := budgets.fastNaive preset
  let fastNttMeasured := budgets.fastNtt preset
  let fastNttFastMeasured := budgets.fastNttFast preset
  let fastNttFastPlanMeasured := budgets.fastNttFastPlan preset
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
      CPolynomial.NTT.FastMul.fastMulImpl canonicalDomain mulLhsPoly mulRhsPoly)
    canonicalChecksum (checksumIterations := checksumIterations)
  let fastNtt ← runTimed
    s!"univariate-mul-ntt-{slug}-fast" "CPolynomial"
    (univariateMulNttMethod "FastMul.fastMulImpl") fastField.id
    univariateMulShape preset warmup fastNttMeasured
    (fun _ ↦ CPolynomial.NTT.FastMul.fastMulImpl fastDomain
      fastMulLhsPoly fastMulRhsPoly)
    fastChecksum (checksumIterations := checksumIterations)
  let canonicalNttFast ← runTimed
    "univariate-mul-ntt-fast" "CPolynomial" (univariateMulNttMethod "NTTFast.fastMulImpl")
    canonicalField.id univariateMulShape preset warmup nttFastMeasured
    (fun _ ↦
      CPolynomial.NTTFast.fastMulImpl canonicalDomain mulLhsPoly mulRhsPoly)
    canonicalChecksum (checksumIterations := checksumIterations)
  let fastNttFast ← runTimed
    s!"univariate-mul-ntt-fast-{slug}-fast" "CPolynomial"
    (univariateMulNttMethod "NTTFast.fastMulImpl") fastField.id
    univariateMulShape preset warmup fastNttFastMeasured
    (fun _ ↦ CPolynomial.NTTFast.fastMulImpl fastDomain
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
    groupKey := key,
    title := "Univariate multiplication (" ++ fieldTitle ++ ")",
    records := #[canonicalNaive, canonicalNtt, canonicalNttFast, canonicalNttFastPlan,
      fastNaive, fastNtt, fastNttFast, fastNttFastPlan]
  }, gen)

/-- Benchmark KoalaBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runKoalaBearUnivariateMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runUnivariateMulWithFast
    "univariate-mul-koalabear" "KoalaBear" "koalabear"
    ⟨"KoalaBear.Field", checksumKoalaBear⟩ ⟨"KoalaBear.Fast.Field", checksumKoalaBearFast⟩
    (fun size ↦ koalaBearArray size false) koalaBearFastArray
    koalaBearMulNttDomain koalaBearFastMulNttDomain
    { ntt := (·.selectNat 200 30 5)
      nttFast := (·.selectNat 800 120 25)
      nttFastPlan := (·.selectNat 850 120 25)
      fastNaive := (·.selectNat 210 30 6)
      fastNtt := (·.selectNat 630 90 18)
      fastNttFast := (·.selectNat 2450 350 70)
      fastNttFastPlan := (·.selectNat 2450 350 70) }
    preset gen

/-- Benchmark BabyBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runBabyBearUnivariateMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runUnivariateMulWithFast
    "univariate-mul-babybear" "BabyBear" "babybear"
    ⟨"BabyBear.Field", checksumBabyBear⟩ ⟨"BabyBear.Fast.Field", checksumBabyBearFast⟩
    (fun size ↦ babyBearArray size false) babyBearFastArray
    babyBearMulNttDomain babyBearFastMulNttDomain
    { ntt := (·.selectNat 200 30 5)
      nttFast := (·.selectNat 800 120 25)
      nttFastPlan := (·.selectNat 850 120 25)
      fastNaive := (·.selectNat 210 30 6)
      fastNtt := (·.selectNat 630 90 18)
      fastNttFast := (·.selectNat 2450 350 70)
      fastNttFastPlan := (·.selectNat 2450 350 70) }
    preset gen

/-- Runnable `CompPoly.Univariate.NTT.FastMul` benchmark tasks. -/
def univariateNttFastMulTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-koalabear", "Univariate multiplication (KoalaBear)"⟩
    runKoalaBearUnivariateMul,
  BenchTask.fromGroupRunner
    ⟨"univariate-mul-babybear", "Univariate multiplication (BabyBear)"⟩
    runBabyBearUnivariateMul
]

/-- Run selected direct univariate multiplication and root-of-unity NTT benchmarks. -/
def runUnivariateNttFastMul (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulTasks preset selection gen

end CompPolyBench
