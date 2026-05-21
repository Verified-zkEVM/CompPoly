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
private def runBabyBearUnivariateLowProduct (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mulLowLhsCoeffs, gen) := (babyBearArray univariateMulLowCoeffSlots false).run gen
  let (mulLowRhsCoeffs, gen) := (babyBearArray univariateMulLowCoeffSlots false).run gen
  let mulLowLhsRaw : CPolynomial.Raw BabyBear.Field := mulLowLhsCoeffs
  let mulLowRhsRaw : CPolynomial.Raw BabyBear.Field := mulLowRhsCoeffs
  let fastMulLowLhsRaw : CPolynomial.Raw BabyBear.Fast.Element :=
    babyBearFastArray mulLowLhsCoeffs
  let fastMulLowRhsRaw : CPolynomial.Raw BabyBear.Fast.Element :=
    babyBearFastArray mulLowRhsCoeffs
  let naiveLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.Raw.MulLowContext.naive
  let convolutionLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearBestDomainForLength?
  let fastNaiveLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.Raw.MulLowContext.naive
  let fastConvolutionLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.Raw.MulLowContext.convolution
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let warmup := mulWarmupIterations preset
  let measured := mulMeasuredIterations preset
  let convolutionMeasured := preset.selectNat 30 5 1
  let nttMeasured := preset.selectNat 100 15 3
  let nttFastMeasured := preset.selectNat 500 70 15
  let checksumIterations := groupChecksumIterations measured [
    convolutionMeasured, nttMeasured, nttFastMeasured
  ]
  let lowNaive ← runTimed
    "univariate-mul-low-naive" "CPolynomial.Raw" "MulLowContext.naive" "BabyBear.Field"
    univariateMulLowShape preset warmup measured
    (fun _ ↦ naiveLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLowNaive ← runTimed
    "univariate-mul-low-naive-fast" "CPolynomial.Raw" "MulLowContext.naive"
    "BabyBear.Fast.Element"
    univariateMulLowShape preset warmup measured
    (fun _ ↦ fastNaiveLowMul.mulLow univariateMulLowOutputCoeffSlots fastMulLowLhsRaw
      fastMulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let lowConvolution ← runTimed
    "univariate-mul-low-convolution" "CPolynomial.Raw" "MulLowContext.convolution"
    "BabyBear.Field"
    univariateMulLowShape preset warmup convolutionMeasured
    (fun _ ↦ convolutionLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLowConvolution ← runTimed
    "univariate-mul-low-convolution-fast" "CPolynomial.Raw" "MulLowContext.convolution"
    "BabyBear.Fast.Element"
    univariateMulLowShape preset warmup convolutionMeasured
    (fun _ ↦ fastConvolutionLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let lowNtt ← runTimed
    "univariate-mul-low-ntt-with-fallback" "CPolynomial.Raw" "FastMulLow.withFallback"
    "BabyBear.Field"
    univariateMulLowShape preset warmup nttMeasured
    (fun _ ↦ nttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLowNtt ← runTimed
    "univariate-mul-low-ntt-with-fallback-fast" "CPolynomial.Raw"
    "FastMulLow.withFallback" "BabyBear.Fast.Element"
    univariateMulLowShape preset warmup nttMeasured
    (fun _ ↦ fastNttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let lowNttFast ← runTimed
    "univariate-mul-low-ntt-fast-with-fallback" "CPolynomial.Raw"
    "NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    univariateMulLowShape preset warmup nttFastMeasured
    (fun _ ↦ nttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLowNttFast ← runTimed
    "univariate-mul-low-ntt-fast-with-fallback-fast" "CPolynomial.Raw"
    "NTTFast.FastMulLow.withFallback" "BabyBear.Fast.Element"
    univariateMulLowShape preset warmup nttFastMeasured
    (fun _ ↦ fastNttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-low-product-babybear",
    title := "Univariate low product (BabyBear)",
    records := #[lowNaive, lowConvolution, lowNtt, lowNttFast, fastLowNaive,
      fastLowConvolution, fastLowNtt, fastLowNttFast]
  }, gen)

/-- Runnable `CompPoly.Univariate.NTT.FastMulLow` benchmark tasks. -/
def univariateNttFastMulLowTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-low-product-babybear", "Univariate low product (BabyBear)"⟩
    runBabyBearUnivariateLowProduct
]

/-- Run selected low-product multiplication benchmarks. -/
def runUnivariateNttFastMulLow (preset : BenchPreset) (selection : BenchSelection)
    (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulLowTasks preset selection gen

end CompPolyBench
