/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.BatchEval
public import CompPoly.Univariate.NTT.FastMulLow
public import CompPoly.Univariate.NTTFast.FastMulLow

/-!
# Benchmarks for `CompPoly.Univariate.BatchEval`
-/

public section

open CompPoly

namespace CompPolyBench

/-- Run the small KoalaBear univariate batch-evaluation benchmark group. -/
private def runKoalaBearUnivariateBatchSmall (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (batchCoeffs, gen) := (koalaBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (koalaBearPoints univariateBatchPointCount).run gen
  let batchPoly := cpolyOfArray batchCoeffs
  let fastBatchCoeffs := koalaBearFastArray batchCoeffs
  let fastBatchPoints := koalaBearFastArray batchPoints
  let fastBatchPoly := cpolyOfArray fastBatchCoeffs
  let naiveMul : CPolynomial.MulContext KoalaBear.Field := CPolynomial.MulContext.naive
  let nttMul : CPolynomial.MulContext KoalaBear.Field :=
    CPolynomial.MulContext.ntt koalaBearBestDomainForLength?
  let nttFastMul : CPolynomial.MulContext KoalaBear.Field :=
    CPolynomial.MulContext.nttFast koalaBearBestDomainForLength?
  let naiveMod : CPolynomial.ModContext KoalaBear.Field := CPolynomial.ModContext.naive
  let remainderOnlyMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.remainderOnly
  let convolutionLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearBestDomainForLength?
  let reversalConvolutionLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal convolutionLowMul
  let reversalNttLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal nttWithFallbackLowMul
  let reversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal nttFastWithFallbackLowMul
  let fastNaiveMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.naive
  let fastNttMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.ntt koalaBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let fastNaiveMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.naive
  let fastRemainderOnlyMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.remainderOnly
  let fastConvolutionLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastReversalConvolutionLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastConvolutionLowMul
  let fastReversalNttLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastNttFastWithFallbackLowMul
  let checksumIterations := digestPeriod 1
  let smallBatchSum ← runTimedSpec
    { name := "univariate-batch-naive-sum", representation := "CPolynomial", method := "evalBatch",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ CPolynomial.evalBatch batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSum ← runTimedSpec
    { name := "univariate-batch-naive-sum-fast", representation := "CPolynomial",
      method := "evalBatch", field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ CPolynomial.evalBatch fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchHorner ← runTimedSpec
    { name := "univariate-batch-naive-horner", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ CPolynomial.evalBatchHorner batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchHorner ← runTimedSpec
    { name := "univariate-batch-naive-horner-fast", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Fast.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchHorner fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductNaive ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-naive-mod", representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul naiveMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductNaive ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-naive-mod-fast",
      representation := "CPolynomial", method := "evalBatchSubproduct naive mul/mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastNaiveMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-remainder-only-mod",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-remainder-only-mod-fast",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductReversalConvolution ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/reversal-convolution-low mod",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul reversalConvolutionLowMod batchPoly
      batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductReversalConvolution ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/reversal-convolution-low mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastReversalConvolutionLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod batchPoly
      batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  pure ({
    groupKey := "univariate-batch-small-koalabear",
    title := "Univariate batch evaluation, small (KoalaBear)",
    records := #[smallBatchSum, smallBatchHorner, smallBatchSubproductNaive,
      smallBatchSubproductRemainder, smallBatchSubproductNtt, smallBatchSubproductNttFast,
      smallBatchSubproductReversalConvolution, smallBatchSubproductReversalNtt,
      smallBatchSubproductReversalNttFast, fastSmallBatchSum, fastSmallBatchHorner,
      fastSmallBatchSubproductNaive, fastSmallBatchSubproductRemainder,
      fastSmallBatchSubproductNtt, fastSmallBatchSubproductNttFast,
      fastSmallBatchSubproductReversalConvolution, fastSmallBatchSubproductReversalNtt,
      fastSmallBatchSubproductReversalNttFast]
  }, gen)

/-- Run the medium KoalaBear univariate batch-evaluation benchmark group. -/
private def runKoalaBearUnivariateBatchMedium (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mediumBatchCoeffs, gen) := (koalaBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (koalaBearPoints mediumUnivariateBatchPointCount).run gen
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
  let fastMediumBatchCoeffs := koalaBearFastArray mediumBatchCoeffs
  let fastMediumBatchPoints := koalaBearFastArray mediumBatchPoints
  let fastMediumBatchPoly := cpolyOfArray fastMediumBatchCoeffs
  let naiveMul : CPolynomial.MulContext KoalaBear.Field := CPolynomial.MulContext.naive
  let nttMul : CPolynomial.MulContext KoalaBear.Field :=
    CPolynomial.MulContext.ntt koalaBearBestDomainForLength?
  let nttFastMul : CPolynomial.MulContext KoalaBear.Field :=
    CPolynomial.MulContext.nttFast koalaBearBestDomainForLength?
  let remainderOnlyMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.remainderOnly
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearBestDomainForLength?
  let reversalNttLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal nttWithFallbackLowMul
  let reversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal nttFastWithFallbackLowMul
  let fastNaiveMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.naive
  let fastNttMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.ntt koalaBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let fastRemainderOnlyMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.remainderOnly
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastReversalNttLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastNttFastWithFallbackLowMul
  let checksumIterations := digestPeriod 1
  let mediumBatchSum ← runTimedSpec
    { name := "univariate-batch-medium-naive-sum", representation := "CPolynomial",
      method := "evalBatch", field := "KoalaBear.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset (fun _ ↦ CPolynomial.evalBatch mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSum ← runTimedSpec
    { name := "univariate-batch-medium-naive-sum-fast", representation := "CPolynomial",
      method := "evalBatch", field := "KoalaBear.Fast.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatch fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchHorner ← runTimedSpec
    { name := "univariate-batch-medium-naive-horner", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchHorner mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchHorner ← runTimedSpec
    { name := "univariate-batch-medium-naive-horner-fast", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Fast.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchHorner fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod-fast",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod
      mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  pure ({
    groupKey := "univariate-batch-medium-koalabear",
    title := "Univariate batch evaluation, medium (KoalaBear)",
    records := #[mediumBatchSum, mediumBatchHorner, mediumBatchSubproductRemainder,
      mediumBatchSubproductNtt, mediumBatchSubproductNttFast, mediumBatchSubproductReversalNtt,
      mediumBatchSubproductReversalNttFast, fastMediumBatchSum, fastMediumBatchHorner,
      fastMediumBatchSubproductRemainder, fastMediumBatchSubproductNtt,
      fastMediumBatchSubproductNttFast, fastMediumBatchSubproductReversalNtt,
      fastMediumBatchSubproductReversalNttFast]
  }, gen)

/-- Run the large KoalaBear univariate batch-evaluation benchmark group. -/
private def runKoalaBearUnivariateBatchLarge (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (largeBatchCoeffs, gen) := (koalaBearArray largeUnivariateBatchCoeffSlots false).run gen
  let (largeBatchPoints, gen) := (koalaBearPoints largeUnivariateBatchPointCount).run gen
  let largeBatchPoly := cpolyOfArray largeBatchCoeffs
  let fastLargeBatchCoeffs := koalaBearFastArray largeBatchCoeffs
  let fastLargeBatchPoints := koalaBearFastArray largeBatchPoints
  let fastLargeBatchPoly := cpolyOfArray fastLargeBatchCoeffs
  let nttMul : CPolynomial.MulContext KoalaBear.Field :=
    CPolynomial.MulContext.ntt koalaBearBestDomainForLength?
  let nttFastMul : CPolynomial.MulContext KoalaBear.Field :=
    CPolynomial.MulContext.nttFast koalaBearBestDomainForLength?
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearBestDomainForLength?
  let reversalNttLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal nttWithFallbackLowMul
  let reversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Field :=
    CPolynomial.ModContext.reversal nttFastWithFallbackLowMul
  let fastNttMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.ntt koalaBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext KoalaBear.Fast.Field :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastReversalNttLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Fast.Field :=
    CPolynomial.ModContext.reversal fastNttFastWithFallbackLowMul
  let checksumIterations := digestPeriod 1
  let largeBatchHorner ← runTimedSpec
    { name := "univariate-batch-large-naive-horner", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Field",
      inputShape := largeUnivariateBatchShape, digestIterations := checksumIterations }
    preset (fun _ ↦ CPolynomial.evalBatchHorner largeBatchPoly largeBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastLargeBatchHorner ← runTimedSpec
    { name := "univariate-batch-large-naive-horner-fast", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Fast.Field",
      inputShape := largeUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchHorner fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let largeBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod", field := "KoalaBear.Field",
      inputShape := largeUnivariateBatchShape, digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastLargeBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod",
      field := "KoalaBear.Fast.Field", inputShape := largeUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let largeBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Field", inputShape := largeUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastLargeBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Fast.Field", inputShape := largeUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast)
  pure ({
    groupKey := "univariate-batch-large-koalabear",
    title := "Univariate batch evaluation, large (KoalaBear)",
    records := #[largeBatchHorner, largeBatchSubproductReversalNtt,
      largeBatchSubproductReversalNttFast, fastLargeBatchHorner,
      fastLargeBatchSubproductReversalNtt, fastLargeBatchSubproductReversalNttFast]
  }, gen)

/-- Runnable `CompPoly.Univariate.BatchEval` benchmark tasks. -/
def univariateBatchEvalTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-batch-small-koalabear", "Univariate batch evaluation, small (KoalaBear)"⟩
    runKoalaBearUnivariateBatchSmall,
  BenchTask.fromGroupRunner
    ⟨"univariate-batch-medium-koalabear", "Univariate batch evaluation, medium (KoalaBear)"⟩
    runKoalaBearUnivariateBatchMedium,
  BenchTask.fromGroupRunner
    ⟨"univariate-batch-large-koalabear", "Univariate batch evaluation, large (KoalaBear)"⟩
    runKoalaBearUnivariateBatchLarge
]

end CompPolyBench
