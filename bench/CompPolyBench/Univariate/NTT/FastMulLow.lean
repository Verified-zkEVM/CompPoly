/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.NTT.FastMulLow
public import CompPoly.Univariate.NTTFast.FastMulLow

/-!
# Benchmarks for `CompPoly.Univariate.NTT.FastMulLow`
-/

public section

open CompPoly

namespace CompPolyBench

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
  let checksumIterations := digestPeriod 1
  let lowNaive ← runTimedSpec
    { name := "univariate-mul-low-naive", representation := "CPolynomial.Raw",
      method := "MulLowContext.naive", field := "KoalaBear.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ naiveLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear)
  let fastLowNaive ← runTimedSpec
    { name := "univariate-mul-low-naive-fast", representation := "CPolynomial.Raw",
      method := "MulLowContext.naive", field := "KoalaBear.Fast.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ fastNaiveLowMul.mulLow univariateMulLowOutputCoeffSlots fastMulLowLhsRaw
      fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast)
  let lowConvolution ← runTimedSpec
    { name := "univariate-mul-low-convolution", representation := "CPolynomial.Raw",
      method := "MulLowContext.convolution", field := "KoalaBear.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ convolutionLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear)
  let fastLowConvolution ← runTimedSpec
    { name := "univariate-mul-low-convolution-fast", representation := "CPolynomial.Raw",
      method := "MulLowContext.convolution", field := "KoalaBear.Fast.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ fastConvolutionLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast)
  let lowNtt ← runTimedSpec
    { name := "univariate-mul-low-ntt-with-fallback", representation := "CPolynomial.Raw",
      method := "FastMulLow.withFallback", field := "KoalaBear.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ nttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear)
  let fastLowNtt ← runTimedSpec
    { name := "univariate-mul-low-ntt-with-fallback-fast", representation := "CPolynomial.Raw",
      method := "FastMulLow.withFallback", field := "KoalaBear.Fast.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ fastNttWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast)
  let lowNttFast ← runTimedSpec
    { name := "univariate-mul-low-ntt-fast-with-fallback", representation := "CPolynomial.Raw",
      method := "NTTFast.FastMulLow.withFallback", field := "KoalaBear.Field",
      inputShape := univariateMulLowShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ nttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots mulLowLhsRaw
      mulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBear)
  let fastLowNttFast ← runTimedSpec
    { name := "univariate-mul-low-ntt-fast-with-fallback-fast",
      representation := "CPolynomial.Raw", method := "NTTFast.FastMulLow.withFallback",
      field := "KoalaBear.Fast.Field", inputShape := univariateMulLowShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ fastNttFastWithFallbackLowMul.mulLow univariateMulLowOutputCoeffSlots
      fastMulLowLhsRaw fastMulLowRhsRaw)
    (checksumRawPolynomial checksumKoalaBearFast)
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

end CompPolyBench
