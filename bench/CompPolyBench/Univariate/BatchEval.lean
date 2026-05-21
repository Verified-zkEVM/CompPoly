/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Common
import CompPoly.Univariate.BatchEval
import CompPoly.Univariate.NTT.FastMulLow
import CompPoly.Univariate.NTTFast.FastMulLow

/-!
# Benchmarks for `CompPoly.Univariate.BatchEval`
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Univariate.BatchEval`. -/
def univariateBatchEvalGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-batch-small-koalabear", "Univariate batch evaluation, small (KoalaBear)"⟩,
  ⟨"univariate-batch-medium-koalabear", "Univariate batch evaluation, medium (KoalaBear)"⟩,
  ⟨"univariate-batch-large-koalabear", "Univariate batch evaluation, large (KoalaBear)"⟩
]

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
  let fastNaiveMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.naive
  let fastNttMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.ntt koalaBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let fastNaiveMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.naive
  let fastRemainderOnlyMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.remainderOnly
  let fastConvolutionLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.Raw.MulLowContext.convolution
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastReversalConvolutionLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastConvolutionLowMul
  let fastReversalNttLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
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
  let checksumIterations := groupChecksumIterations measured [
    sumMeasured, hornerMeasured, remainderMeasured, nttMeasured, nttFastMeasured,
    reversalConvolutionMeasured, reversalNttMeasured, reversalNttFastMeasured,
    fastSumMeasured, fastHornerMeasured, fastMeasured, fastRemainderMeasured,
    fastNttMeasured, fastNttFastMeasured, fastReversalConvolutionMeasured,
    fastReversalNttMeasured, fastReversalNttFastMeasured
  ]
  let smallBatchSum ← runTimed
    "univariate-batch-naive-sum" "CPolynomial" "evalBatch" "KoalaBear.Field"
    univariateBatchShape preset warmup sumMeasured
    (fun _ ↦ CPolynomial.evalBatch batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSum ← runTimed
    "univariate-batch-naive-sum-fast" "CPolynomial" "evalBatch" "KoalaBear.Fast.Element"
    univariateBatchShape preset warmup fastSumMeasured
    (fun _ ↦ CPolynomial.evalBatch fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchHorner ← runTimed
    "univariate-batch-naive-horner" "CPolynomial" "evalBatchHorner" "KoalaBear.Field"
    univariateBatchShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchHorner ← runTimed
    "univariate-batch-naive-horner-fast" "CPolynomial" "evalBatchHorner"
    "KoalaBear.Fast.Element" univariateBatchShape preset warmup fastHornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductNaive ← runTimed
    "univariate-batch-subproduct-naive-mul-naive-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/mod" "KoalaBear.Field"
    univariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul naiveMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductNaive ← runTimed
    "univariate-batch-subproduct-naive-mul-naive-mod-fast" "CPolynomial"
    "evalBatchSubproduct naive mul/mod" "KoalaBear.Fast.Element"
    univariateBatchShape preset warmup fastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastNaiveMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductRemainder ← runTimed
    "univariate-batch-subproduct-naive-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "KoalaBear.Field"
    univariateBatchShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductRemainder ← runTimed
    "univariate-batch-subproduct-naive-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "KoalaBear.Fast.Element"
    univariateBatchShape preset warmup fastRemainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "KoalaBear.Field"
    univariateBatchShape preset warmup nttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "KoalaBear.Fast.Element"
    univariateBatchShape preset warmup fastNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "KoalaBear.Field"
    univariateBatchShape preset warmup nttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "KoalaBear.Fast.Element"
    univariateBatchShape preset warmup fastNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalConvolution ← runTimed
    "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/reversal-convolution-low mod" "KoalaBear.Field"
    univariateBatchShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul reversalConvolutionLowMod batchPoly
      batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductReversalConvolution ← runTimed
    "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct naive mul/reversal-convolution-low mod"
    "KoalaBear.Fast.Element" univariateBatchShape preset warmup fastReversalConvolutionMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastReversalConvolutionLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "KoalaBear.Field"
    univariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod batchPoly batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductReversalNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "KoalaBear.Fast.Element"
    univariateBatchShape preset warmup fastReversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod" "KoalaBear.Field"
    univariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod batchPoly
      batchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "KoalaBear.Fast.Element" univariateBatchShape preset warmup fastReversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
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
  let fastNaiveMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.naive
  let fastNttMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.ntt koalaBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let fastRemainderOnlyMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.remainderOnly
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastReversalNttLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
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
  let checksumIterations := groupChecksumIterations measured [
    hornerMeasured, reversalNttMeasured, reversalNttFastMeasured, fastMeasured,
    fastHornerMeasured, fastRemainderMeasured, fastNttMeasured, fastNttFastMeasured,
    fastReversalNttMeasured, fastReversalNttFastMeasured
  ]
  let mediumBatchSum ← runTimed
    "univariate-batch-medium-naive-sum" "CPolynomial" "evalBatch" "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatch mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSum ← runTimed
    "univariate-batch-medium-naive-sum-fast" "CPolynomial" "evalBatch"
    "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastMeasured
    (fun _ ↦ CPolynomial.evalBatch fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumBatchHorner ← runTimed
    "univariate-batch-medium-naive-horner" "CPolynomial" "evalBatchHorner" "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchHorner ← runTimed
    "univariate-batch-medium-naive-horner-fast" "CPolynomial" "evalBatchHorner"
    "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastHornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductRemainder ← runTimed
    "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductRemainder ← runTimed
    "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastRemainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/remainder-only mod"
    "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductReversalNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductReversalNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt mul/reversal-ntt-low mod"
    "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastReversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "KoalaBear.Field"
    mediumUnivariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod
      mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "KoalaBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup fastReversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
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
  let fastNttMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.ntt koalaBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext KoalaBear.Fast.Element :=
    CPolynomial.MulContext.nttFast koalaBearFastBestDomainForLength?
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext KoalaBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback koalaBearFastBestDomainForLength?
  let fastReversalNttLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext KoalaBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttFastWithFallbackLowMul
  let warmup := largeBatchWarmupIterations preset
  let measured := largeBatchMeasuredIterations preset
  let reversalNttMeasured := preset.selectNat 20 3 1
  let reversalNttFastMeasured := preset.selectNat 80 10 2
  let fastMeasured := preset.selectNat 70 10 2
  let fastReversalNttMeasured := preset.selectNat 63 9 2
  let fastReversalNttFastMeasured := preset.selectNat 420 60 12
  let checksumIterations := groupChecksumIterations measured [
    reversalNttMeasured, reversalNttFastMeasured, fastMeasured, fastReversalNttMeasured,
    fastReversalNttFastMeasured
  ]
  let largeBatchHorner ← runTimed
    "univariate-batch-large-naive-horner" "CPolynomial" "evalBatchHorner" "KoalaBear.Field"
    largeUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchHorner largeBatchPoly largeBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLargeBatchHorner ← runTimed
    "univariate-batch-large-naive-horner-fast" "CPolynomial" "evalBatchHorner"
    "KoalaBear.Fast.Element"
    largeUnivariateBatchShape preset warmup fastMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let largeBatchSubproductReversalNtt ← runTimed
    "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "KoalaBear.Field"
    largeUnivariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLargeBatchSubproductReversalNtt ← runTimed
    "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "KoalaBear.Fast.Element"
    largeUnivariateBatchShape preset warmup fastReversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let largeBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "KoalaBear.Field"
    largeUnivariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastLargeBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "KoalaBear.Fast.Element"
    largeUnivariateBatchShape preset warmup fastReversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumKoalaBearFast) (checksumIterations := checksumIterations)
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

/-- Run selected univariate batch-evaluation benchmarks. -/
def runUnivariateBatchEval (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateBatchEvalTasks preset selection gen

end CompPolyBench
