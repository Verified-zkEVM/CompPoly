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
  ⟨"univariate-low-product-koalabear", "Univariate low product (KoalaBear)"⟩
]

/-- Benchmark low-product multiplication variants used by remainder and batch-evaluation paths. -/
private def runKoalaBearUnivariateLowProduct (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mulLowLhsCoeffs, gen) := (koalaBearArray univariateMulLowCoeffSlots false).run gen
  let (mulLowRhsCoeffs, gen) := (koalaBearArray univariateMulLowCoeffSlots false).run gen
  let mulLowLhsRaw : CPolynomial.Raw KoalaBear.Field := mulLowLhsCoeffs
  let mulLowRhsRaw : CPolynomial.Raw KoalaBear.Field := mulLowRhsCoeffs
  let fastMulLowLhsRaw : CPolynomial.Raw KoalaBear.Fast.Field :=
    koalaBearFastArray mulLowLhsCoeffs
  let fastMulLowRhsRaw : CPolynomial.Raw KoalaBear.Fast.Field :=
    koalaBearFastArray mulLowRhsCoeffs
  let naiveLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.Raw.MulLowContext.naive
  let convolutionLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearBestDomainForLength?
  let fastNaiveLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.Raw.MulLowContext.naive
  let fastConvolutionLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let warmup := mulWarmupIterations preset
  let measured := mulMeasuredIterations preset
  let convolutionMeasured := preset.selectNat 30 5 1
  let nttMeasured := preset.selectNat 100 15 3
  let nttFastMeasured := preset.selectNat 500 70 15
  let fastMeasured := preset.selectNat 210 30 6
  let fastConvolutionMeasured := preset.selectNat 70 10 2
  let fastNttMeasured := preset.selectNat 420 60 12
  let fastNttFastMeasured := preset.selectNat 1960 280 56
  let checksumIterations := groupChecksumIterations measured [
    convolutionMeasured, nttMeasured, nttFastMeasured, fastMeasured, fastConvolutionMeasured,
    fastNttMeasured, fastNttFastMeasured
  ]
  let lowNaive ← runTimed
    "univariate-mul-low-naive" "CPolynomial.Raw" "MulLowContext.naive" "KoalaBear.Field"
    univariateMulLowShape preset warmup measured
    (fun _ ↦ naiveLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLowNaive ← runTimed
    "univariate-mul-low-naive-fast" "CPolynomial.Raw" "MulLowContext.naive"
    "KoalaBear.Fast.Field"
    univariateMulLowShape preset warmup fastMeasured
    (fun _ ↦ fastNaiveLowMul.mulLow univariateMulLowOutputCoeffSlots fastMulLowLhsRaw
      fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let lowConvolution ← runTimed
    "univariate-mul-low-convolution" "CPolynomial.Raw" "MulLowContext.convolution"
    "KoalaBear.Field"
    univariateMulLowShape preset warmup convolutionMeasured
    (fun _ ↦ convolutionLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLowConvolution ← runTimed
    "univariate-mul-low-convolution-fast" "CPolynomial.Raw" "MulLowContext.convolution"
    "KoalaBear.Fast.Field"
    univariateMulLowShape preset warmup fastConvolutionMeasured
    (fun _ ↦ fastConvolutionLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let lowNtt ← runTimed
    "univariate-mul-low-ntt-with-fallback" "CPolynomial.Raw" "FastMulLow.withFallback"
    "KoalaBear.Field"
    univariateMulLowShape preset warmup nttMeasured
    (fun _ ↦ nttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLowNtt ← runTimed
    "univariate-mul-low-ntt-with-fallback-fast" "CPolynomial.Raw"
    "FastMulLow.withFallback" "KoalaBear.Fast.Field"
    univariateMulLowShape preset warmup fastNttMeasured
    (fun _ ↦ fastNttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let lowNttFast ← runTimed
    "univariate-mul-low-ntt-fast-with-fallback" "CPolynomial.Raw"
    "NTTFast.FastMulLow.withFallback" "KoalaBear.Field"
    univariateMulLowShape preset warmup nttFastMeasured
    (fun _ ↦ nttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLowNttFast ← runTimed
    "univariate-mul-low-ntt-fast-with-fallback-fast" "CPolynomial.Raw"
    "NTTFast.FastMulLow.withFallback" "KoalaBear.Fast.Field"
    univariateMulLowShape preset warmup fastNttFastMeasured
    (fun _ ↦ fastNttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-low-product-koalabear",
    title := "Univariate low product (KoalaBear)",
    records := #[lowNaive, lowConvolution, lowNtt, lowNttFast, fastLowNaive,
      fastLowConvolution, fastLowNtt, fastLowNttFast]
  }, gen)

/-- Runnable `CompPoly.Univariate.NTT.FastMulLow` benchmark tasks. -/
def univariateNttFastMulLowTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-low-product-koalabear", "Univariate low product (KoalaBear)"⟩
    runKoalaBearUnivariateLowProduct
]

/-- Run selected low-product multiplication benchmarks. -/
def runUnivariateNttFastMulLow (preset : BenchPreset) (selection : BenchSelection)
    (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateNttFastMulLowTasks preset selection gen

end CompPolyBench
