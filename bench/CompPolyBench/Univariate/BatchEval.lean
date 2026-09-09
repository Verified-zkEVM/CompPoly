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
  let warmup := batchWarmupIterations preset
  let measured := batchMeasuredIterations preset
  let sumMeasured := preset.selectNat 1750 250 50
  let hornerMeasured := preset.selectNat 11500 1600 300
  let remainderMeasured := preset.selectNat 900 130 30
  let nttMeasured := preset.selectNat 700 100 20
  let nttFastMeasured := preset.selectNat 800 120 25
  let reversalConvolutionMeasured := preset.selectNat 150 20 5
  let reversalNttMeasured := preset.selectNat 150 20 5
  let reversalNttFastMeasured := preset.selectNat 450 60 15
  let fastSumMeasured := preset.selectNat 19600 2800 560
  let fastHornerMeasured := preset.selectNat 84000 12000 2400
  let fastMeasured := preset.selectNat 35 5 1
  let fastRemainderMeasured := preset.selectNat 3850 550 110
  let fastNttMeasured := preset.selectNat 2800 400 80
  let fastNttFastMeasured := preset.selectNat 3150 450 90
  let fastReversalConvolutionMeasured := preset.selectNat 280 40 8
  let fastReversalNttMeasured := preset.selectNat 420 60 12
  let fastReversalNttFastMeasured := preset.selectNat 1750 250 50
  let checksumIterations := digestPeriod 1
  let smallBatchSum ← runTimedSpec
    { name := "univariate-batch-naive-sum", representation := "CPolynomial", method := "evalBatch",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup sumMeasured (fun _ ↦ CPolynomial.evalBatch batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSum ← runTimedSpec
    { name := "univariate-batch-naive-sum-fast", representation := "CPolynomial",
      method := "evalBatch", field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastSumMeasured (fun _ ↦ CPolynomial.evalBatch fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchHorner ← runTimedSpec
    { name := "univariate-batch-naive-horner", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup hornerMeasured (fun _ ↦ CPolynomial.evalBatchHorner batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchHorner ← runTimedSpec
    { name := "univariate-batch-naive-horner-fast", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Fast.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset warmup fastHornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductNaive ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-naive-mod", representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul naiveMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductNaive ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-naive-mod-fast",
      representation := "CPolynomial", method := "evalBatchSubproduct naive mul/mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastNaiveMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastRemainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-remainder-only-mod",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup nttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-remainder-only-mod-fast",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset warmup nttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductReversalConvolution ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/reversal-convolution-low mod",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup reversalConvolutionMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul reversalConvolutionLowMod batchPoly
      batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductReversalConvolution ← runTimedSpec
    { name := "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/reversal-convolution-low mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalConvolutionMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastReversalConvolutionLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod", field := "KoalaBear.Field",
      inputShape := univariateBatchShape, digestIterations := checksumIterations }
    preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let smallBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod batchPoly
      batchPoints)
    (checksumArray checksumKoalaBear)
  let fastSmallBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Fast.Field", inputShape := univariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalNttFastMeasured
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
  let warmup := mediumBatchWarmupIterations preset
  let measured := mediumBatchMeasuredIterations preset
  let hornerMeasured := preset.selectNat 150 20 5
  let reversalNttMeasured := preset.selectNat 50 10 1
  let reversalNttFastMeasured := preset.selectNat 170 25 5
  let fastMeasured := preset.selectNat 70 10 2
  let fastHornerMeasured := preset.selectNat 1400 200 40
  let fastRemainderMeasured := preset.selectNat 28 4 1
  let fastNttMeasured := preset.selectNat 28 4 1
  let fastNttFastMeasured := preset.selectNat 28 4 1
  let fastReversalNttMeasured := preset.selectNat 210 30 6
  let fastReversalNttFastMeasured := preset.selectNat 910 130 26
  let checksumIterations := digestPeriod 1
  let mediumBatchSum ← runTimedSpec
    { name := "univariate-batch-medium-naive-sum", representation := "CPolynomial",
      method := "evalBatch", field := "KoalaBear.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup measured (fun _ ↦ CPolynomial.evalBatch mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSum ← runTimedSpec
    { name := "univariate-batch-medium-naive-sum-fast", representation := "CPolynomial",
      method := "evalBatch", field := "KoalaBear.Fast.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup fastMeasured
    (fun _ ↦ CPolynomial.evalBatch fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchHorner ← runTimedSpec
    { name := "univariate-batch-medium-naive-horner", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchHorner ← runTimedSpec
    { name := "univariate-batch-medium-naive-horner-fast", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Fast.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup fastHornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductRemainder ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct naive mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastRemainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod-fast",
      representation := "CPolynomial", method := "evalBatchSubproduct ntt mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/remainder-only mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod", field := "KoalaBear.Field",
      inputShape := mediumUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let mediumBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod
      mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastMediumBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Fast.Field", inputShape := mediumUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalNttFastMeasured
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
  let warmup := largeBatchWarmupIterations preset
  let measured := largeBatchMeasuredIterations preset
  let reversalNttMeasured := preset.selectNat 20 3 1
  let reversalNttFastMeasured := preset.selectNat 80 10 2
  let fastMeasured := preset.selectNat 70 10 2
  let fastReversalNttMeasured := preset.selectNat 63 9 2
  let fastReversalNttFastMeasured := preset.selectNat 420 60 12
  let checksumIterations := digestPeriod 1
  let largeBatchHorner ← runTimedSpec
    { name := "univariate-batch-large-naive-horner", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Field",
      inputShape := largeUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup measured (fun _ ↦ CPolynomial.evalBatchHorner largeBatchPoly largeBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastLargeBatchHorner ← runTimedSpec
    { name := "univariate-batch-large-naive-horner-fast", representation := "CPolynomial",
      method := "evalBatchHorner", field := "KoalaBear.Fast.Field",
      inputShape := largeUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup fastMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let largeBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod", field := "KoalaBear.Field",
      inputShape := largeUnivariateBatchShape, digestIterations := checksumIterations }
    preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastLargeBatchSubproductReversalNtt ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt mul/reversal-ntt-low mod",
      field := "KoalaBear.Fast.Field", inputShape := largeUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast)
  let largeBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Field", inputShape := largeUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumKoalaBear)
  let fastLargeBatchSubproductReversalNttFast ← runTimedSpec
    { name := "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast",
      representation := "CPolynomial",
      method := "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
      field := "KoalaBear.Fast.Field", inputShape := largeUnivariateBatchShape,
      digestIterations := checksumIterations }
    preset warmup fastReversalNttFastMeasured
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
