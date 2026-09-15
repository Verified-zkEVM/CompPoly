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

/-- Display and checksum operations associated with a benchmark field. -/
private structure BenchField (F : Type*) where
  id : String
  checksum : F → Nat

/-- Benchmark direct univariate multiplication and root-of-unity NTT variants over a
canonical field and its native-word counterpart. `slug` distinguishes the two
native-word NTT row names, whose canonical-representation names are already taken. -/
private def runUnivariateMulWithFast {F G : Type}
    [Field F] [BEq F] [LawfulBEq F] [Field G] [BEq G] [LawfulBEq G]
    (key fieldTitle slug : String)
    (canonicalField : BenchField F) (fastField : BenchField G)
    (genCoeffs : Nat → StateM StdGen (Array F)) (toFast : Array F → Array G)
    (canonicalDomain : CPolynomial.NTT.Domain F) (fastDomain : CPolynomial.NTT.Domain G)
    (preset : BenchPreset) (gen : StdGen) :
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
  let checksumIterations := digestPeriod 1
  let canonicalNaive ← runTimedSpec
    { name := "univariate-mul-naive", representation := "CPolynomial", method := "mul",
      field := canonicalField.id, inputShape := univariateMulShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ mulLhsPoly * mulRhsPoly) canonicalChecksum
  let fastNaive ← runTimedSpec
    { name := "univariate-mul-naive-fast", representation := "CPolynomial", method := "mul",
      field := fastField.id, inputShape := univariateMulShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ fastMulLhsPoly * fastMulRhsPoly) fastChecksum
  let canonicalNtt ← runTimedSpec
    { name := "univariate-mul-ntt", representation := "CPolynomial",
      method := (univariateMulNttMethod "FastMul.fastMulImpl"), field := canonicalField.id,
      inputShape := univariateMulShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦
      CPolynomial.NTT.FastMul.fastMulImpl canonicalDomain mulLhsPoly mulRhsPoly)
    canonicalChecksum
  let fastNtt ← runTimedSpec
    { name := s!"univariate-mul-ntt-{slug}-fast", representation := "CPolynomial",
      method := (univariateMulNttMethod "FastMul.fastMulImpl"), field := fastField.id,
      inputShape := univariateMulShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.NTT.FastMul.fastMulImpl fastDomain
      fastMulLhsPoly fastMulRhsPoly)
    fastChecksum
  let canonicalNttFast ← runTimedSpec
    { name := "univariate-mul-ntt-fast", representation := "CPolynomial",
      method := (univariateMulNttMethod "NTTFast.fastMulImpl"), field := canonicalField.id,
      inputShape := univariateMulShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦
      CPolynomial.NTTFast.fastMulImpl canonicalDomain mulLhsPoly mulRhsPoly)
    canonicalChecksum
  let fastNttFast ← runTimedSpec
    { name := s!"univariate-mul-ntt-fast-{slug}-fast", representation := "CPolynomial",
      method := (univariateMulNttMethod "NTTFast.fastMulImpl"), field := fastField.id,
      inputShape := univariateMulShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.NTTFast.fastMulImpl fastDomain
      fastMulLhsPoly fastMulRhsPoly)
    fastChecksum
  let canonicalNttFastPlan ← runTimedSpec
    { name := "univariate-mul-ntt-fast-plan", representation := "CPolynomial",
      method := (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward"),
      field := canonicalField.id, inputShape := univariateMulShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.NTTFast.Plan.fastMulImpl canonicalPlan mulLhsPoly mulRhsPoly)
    canonicalChecksum
  let fastNttFastPlan ← runTimedSpec
    { name := "univariate-mul-ntt-fast-plan-fast", representation := "CPolynomial",
      method := (univariateMulNttMethod
      "NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward"),
      field := fastField.id, inputShape := univariateMulShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.NTTFast.Plan.fastMulImpl fastPlan fastMulLhsPoly fastMulRhsPoly)
    fastChecksum
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
    preset gen

/-- Benchmark BabyBear direct univariate multiplication and root-of-unity NTT variants. -/
private def runBabyBearUnivariateMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runUnivariateMulWithFast
    "univariate-mul-babybear" "BabyBear" "babybear"
    ⟨"BabyBear.Field", checksumBabyBear⟩ ⟨"BabyBear.Fast.Field", checksumBabyBearFast⟩
    (fun size ↦ babyBearArray size false) babyBearFastArray
    babyBearMulNttDomain babyBearFastMulNttDomain
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

end CompPolyBench
