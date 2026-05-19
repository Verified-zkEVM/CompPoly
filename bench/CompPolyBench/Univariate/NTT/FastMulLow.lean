/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Common
import CompPoly.Univariate.NTT.FastMulLow
import CompPoly.Univariate.NTTFast.FastMulLow

/-!
# Benchmarks for `CompPoly.Univariate.NTT.FastMulLow`
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Univariate.NTT.FastMulLow`. -/
def univariateNttFastMulLowGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-low-product-babybear", "Univariate low product (BabyBear)"⟩
]

/-- Benchmark low-product multiplication variants used by remainder and batch-evaluation paths. -/
private def runBabyBearUnivariateLowProduct (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (mulLowLhsCoeffs, gen) := (babyBearArray univariateMulLowCoeffSlots false).run gen
  let (mulLowRhsCoeffs, gen) := (babyBearArray univariateMulLowCoeffSlots false).run gen
  let mulLowLhsRaw : CPolynomial.Raw BabyBear.Field := mulLowLhsCoeffs
  let mulLowRhsRaw : CPolynomial.Raw BabyBear.Field := mulLowRhsCoeffs
  let naiveLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.Raw.MulLowContext.naive
  let convolutionLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearBestDomainForLength?
  let lowNaive ← runTimed
    "univariate-mul-low-naive" "CPolynomial.Raw" "MulLowContext.naive" "BabyBear.Field"
    univariateMulLowShape mulWarmupIterations mulMeasuredIterations
    (fun _ => naiveLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear)
  let lowConvolution ← runTimed
    "univariate-mul-low-convolution" "CPolynomial.Raw" "MulLowContext.convolution"
    "BabyBear.Field"
    univariateMulLowShape mulWarmupIterations mulMeasuredIterations
    (fun _ => convolutionLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear)
  let lowNtt ← runTimed
    "univariate-mul-low-ntt-with-fallback" "CPolynomial.Raw" "FastMulLow.withFallback"
    "BabyBear.Field"
    univariateMulLowShape mulWarmupIterations mulMeasuredIterations
    (fun _ => nttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear)
  let lowNttFast ← runTimed
    "univariate-mul-low-ntt-fast-with-fallback" "CPolynomial.Raw"
    "NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    univariateMulLowShape mulWarmupIterations mulMeasuredIterations
    (fun _ => nttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear)
  pure ({
    groupKey := "univariate-low-product-babybear",
    title := "Univariate low product (BabyBear)",
    records := #[lowNaive, lowConvolution, lowNtt, lowNttFast]
  }, gen)

/-- Runnable `CompPoly.Univariate.NTT.FastMulLow` benchmark tasks. -/
def univariateNttFastMulLowTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-low-product-babybear", "Univariate low product (BabyBear)"⟩
    runBabyBearUnivariateLowProduct
]

/-- Benchmark low-product multiplication variants used by remainder and batch-evaluation paths. -/
def runUnivariateNttFastMulLow (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulLowTasks selection gen

end CompPolyBench
