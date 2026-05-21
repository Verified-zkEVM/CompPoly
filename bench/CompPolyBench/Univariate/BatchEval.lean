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
  ⟨"univariate-batch-small-babybear", "Univariate batch evaluation, small (BabyBear)"⟩,
  ⟨"univariate-batch-medium-babybear", "Univariate batch evaluation, medium (BabyBear)"⟩,
  ⟨"univariate-batch-large-babybear", "Univariate batch evaluation, large (BabyBear)"⟩
]

/-- Run the small BabyBear univariate batch-evaluation benchmark group. -/
private def runBabyBearUnivariateBatchSmall (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (batchCoeffs, gen) := (babyBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (babyBearPoints univariateBatchPointCount).run gen
  let batchPoly := cpolyOfArray batchCoeffs
  let fastBatchCoeffs := babyBearFastArray batchCoeffs
  let fastBatchPoints := babyBearFastArray batchPoints
  let fastBatchPoly := cpolyOfArray fastBatchCoeffs
  let naiveMul : CPolynomial.MulContext BabyBear.Field := CPolynomial.MulContext.naive
  let nttMul : CPolynomial.MulContext BabyBear.Field :=
    CPolynomial.MulContext.ntt babyBearBestDomainForLength?
  let nttFastMul : CPolynomial.MulContext BabyBear.Field :=
    CPolynomial.MulContext.nttFast babyBearBestDomainForLength?
  let naiveMod : CPolynomial.ModContext BabyBear.Field := CPolynomial.ModContext.naive
  let remainderOnlyMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.remainderOnly
  let convolutionLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.Raw.MulLowContext.convolution
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearBestDomainForLength?
  let reversalConvolutionLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal convolutionLowMul
  let reversalNttLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal nttWithFallbackLowMul
  let reversalNttFastLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal nttFastWithFallbackLowMul
  let fastNaiveMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.naive
  let fastNttMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.ntt babyBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.nttFast babyBearFastBestDomainForLength?
  let fastNaiveMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.naive
  let fastRemainderOnlyMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.remainderOnly
  let fastConvolutionLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.Raw.MulLowContext.convolution
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastReversalConvolutionLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastConvolutionLowMul
  let fastReversalNttLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
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
  let checksumIterations := groupChecksumIterations measured [
    sumMeasured, hornerMeasured, remainderMeasured, nttMeasured, nttFastMeasured,
    reversalConvolutionMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let smallBatchSum ← runTimed
    "univariate-batch-naive-sum" "CPolynomial" "evalBatch" "BabyBear.Field"
    univariateBatchShape preset warmup sumMeasured
    (fun _ ↦ CPolynomial.evalBatch batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSum ← runTimed
    "univariate-batch-naive-sum-fast" "CPolynomial" "evalBatch" "BabyBear.Fast.Element"
    univariateBatchShape preset warmup sumMeasured
    (fun _ ↦ CPolynomial.evalBatch fastBatchPoly fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchHorner ← runTimed
    "univariate-batch-naive-horner" "CPolynomial" "evalBatchHorner" "BabyBear.Field"
    univariateBatchShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchHorner ← runTimed
    "univariate-batch-naive-horner-fast" "CPolynomial" "evalBatchHorner"
    "BabyBear.Fast.Element" univariateBatchShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastBatchPoly fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductNaive ← runTimed
    "univariate-batch-subproduct-naive-mul-naive-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/mod" "BabyBear.Field"
    univariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul naiveMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductNaive ← runTimed
    "univariate-batch-subproduct-naive-mul-naive-mod-fast" "CPolynomial"
    "evalBatchSubproduct naive mul/mod" "BabyBear.Fast.Element"
    univariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastNaiveMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductRemainder ← runTimed
    "univariate-batch-subproduct-naive-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "BabyBear.Field"
    univariateBatchShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductRemainder ← runTimed
    "univariate-batch-subproduct-naive-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "BabyBear.Fast.Element"
    univariateBatchShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "BabyBear.Field"
    univariateBatchShape preset warmup nttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "BabyBear.Fast.Element"
    univariateBatchShape preset warmup nttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "BabyBear.Field"
    univariateBatchShape preset warmup nttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "BabyBear.Fast.Element"
    univariateBatchShape preset warmup nttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalConvolution ← runTimed
    "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/reversal-convolution-low mod" "BabyBear.Field"
    univariateBatchShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul reversalConvolutionLowMod batchPoly
      batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductReversalConvolution ← runTimed
    "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct naive mul/reversal-convolution-low mod"
    "BabyBear.Fast.Element" univariateBatchShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastReversalConvolutionLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Field"
    univariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductReversalNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Fast.Element"
    univariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod fastBatchPoly
      fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod" "BabyBear.Field"
    univariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod batchPoly
      batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Fast.Element" univariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastBatchPoly fastBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-batch-small-babybear",
    title := "Univariate batch evaluation, small (BabyBear)",
    records := #[smallBatchSum, smallBatchHorner, smallBatchSubproductNaive,
      smallBatchSubproductRemainder, smallBatchSubproductNtt, smallBatchSubproductNttFast,
      smallBatchSubproductReversalConvolution, smallBatchSubproductReversalNtt,
      smallBatchSubproductReversalNttFast, fastSmallBatchSum, fastSmallBatchHorner,
      fastSmallBatchSubproductNaive, fastSmallBatchSubproductRemainder,
      fastSmallBatchSubproductNtt, fastSmallBatchSubproductNttFast,
      fastSmallBatchSubproductReversalConvolution, fastSmallBatchSubproductReversalNtt,
      fastSmallBatchSubproductReversalNttFast]
  }, gen)

/-- Run the medium BabyBear univariate batch-evaluation benchmark group. -/
private def runBabyBearUnivariateBatchMedium (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mediumBatchCoeffs, gen) := (babyBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (babyBearPoints mediumUnivariateBatchPointCount).run gen
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
  let fastMediumBatchCoeffs := babyBearFastArray mediumBatchCoeffs
  let fastMediumBatchPoints := babyBearFastArray mediumBatchPoints
  let fastMediumBatchPoly := cpolyOfArray fastMediumBatchCoeffs
  let naiveMul : CPolynomial.MulContext BabyBear.Field := CPolynomial.MulContext.naive
  let nttMul : CPolynomial.MulContext BabyBear.Field :=
    CPolynomial.MulContext.ntt babyBearBestDomainForLength?
  let nttFastMul : CPolynomial.MulContext BabyBear.Field :=
    CPolynomial.MulContext.nttFast babyBearBestDomainForLength?
  let remainderOnlyMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.remainderOnly
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearBestDomainForLength?
  let reversalNttLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal nttWithFallbackLowMul
  let reversalNttFastLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal nttFastWithFallbackLowMul
  let fastNaiveMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.naive
  let fastNttMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.ntt babyBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.nttFast babyBearFastBestDomainForLength?
  let fastRemainderOnlyMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.remainderOnly
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastReversalNttLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttFastWithFallbackLowMul
  let warmup := mediumBatchWarmupIterations preset
  let measured := mediumBatchMeasuredIterations preset
  let hornerMeasured := preset.selectNat 150 20 5
  let reversalNttMeasured := preset.selectNat 50 10 1
  let reversalNttFastMeasured := preset.selectNat 170 25 5
  let checksumIterations := groupChecksumIterations measured [
    hornerMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let mediumBatchSum ← runTimed
    "univariate-batch-medium-naive-sum" "CPolynomial" "evalBatch" "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatch mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSum ← runTimed
    "univariate-batch-medium-naive-sum-fast" "CPolynomial" "evalBatch"
    "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatch fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumBatchHorner ← runTimed
    "univariate-batch-medium-naive-horner" "CPolynomial" "evalBatchHorner" "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchHorner ← runTimed
    "univariate-batch-medium-naive-horner-fast" "CPolynomial" "evalBatchHorner"
    "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup hornerMeasured
    (fun _ ↦ CPolynomial.evalBatchHorner fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductRemainder ← runTimed
    "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductRemainder ← runTimed
    "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNaiveMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/remainder-only mod"
    "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastRemainderOnlyMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductReversalNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductReversalNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt mul/reversal-ntt-low mod"
    "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Field"
    mediumUnivariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod
      mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Fast.Element"
    mediumUnivariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastMediumBatchPoly fastMediumBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-batch-medium-babybear",
    title := "Univariate batch evaluation, medium (BabyBear)",
    records := #[mediumBatchSum, mediumBatchHorner, mediumBatchSubproductRemainder,
      mediumBatchSubproductNtt, mediumBatchSubproductNttFast, mediumBatchSubproductReversalNtt,
      mediumBatchSubproductReversalNttFast, fastMediumBatchSum, fastMediumBatchHorner,
      fastMediumBatchSubproductRemainder, fastMediumBatchSubproductNtt,
      fastMediumBatchSubproductNttFast, fastMediumBatchSubproductReversalNtt,
      fastMediumBatchSubproductReversalNttFast]
  }, gen)

/-- Run the large BabyBear univariate batch-evaluation benchmark group. -/
private def runBabyBearUnivariateBatchLarge (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (largeBatchCoeffs, gen) := (babyBearArray largeUnivariateBatchCoeffSlots false).run gen
  let (largeBatchPoints, gen) := (babyBearPoints largeUnivariateBatchPointCount).run gen
  let largeBatchPoly := cpolyOfArray largeBatchCoeffs
  let fastLargeBatchCoeffs := babyBearFastArray largeBatchCoeffs
  let fastLargeBatchPoints := babyBearFastArray largeBatchPoints
  let fastLargeBatchPoly := cpolyOfArray fastLargeBatchCoeffs
  let nttMul : CPolynomial.MulContext BabyBear.Field :=
    CPolynomial.MulContext.ntt babyBearBestDomainForLength?
  let nttFastMul : CPolynomial.MulContext BabyBear.Field :=
    CPolynomial.MulContext.nttFast babyBearBestDomainForLength?
  let nttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearBestDomainForLength?
  let nttFastWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Field :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearBestDomainForLength?
  let reversalNttLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal nttWithFallbackLowMul
  let reversalNttFastLowMod : CPolynomial.ModContext BabyBear.Field :=
    CPolynomial.ModContext.reversal nttFastWithFallbackLowMul
  let fastNttMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.ntt babyBearFastBestDomainForLength?
  let fastNttFastMul : CPolynomial.MulContext BabyBear.Fast.Element :=
    CPolynomial.MulContext.nttFast babyBearFastBestDomainForLength?
  let fastNttWithFallbackLowMul : CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTT.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastNttFastWithFallbackLowMul :
      CPolynomial.Raw.MulLowContext BabyBear.Fast.Element :=
    CPolynomial.NTTFast.FastMulLow.withFallback babyBearFastBestDomainForLength?
  let fastReversalNttLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttWithFallbackLowMul
  let fastReversalNttFastLowMod : CPolynomial.ModContext BabyBear.Fast.Element :=
    CPolynomial.ModContext.reversal fastNttFastWithFallbackLowMul
  let warmup := largeBatchWarmupIterations preset
  let measured := largeBatchMeasuredIterations preset
  let reversalNttMeasured := preset.selectNat 20 3 1
  let reversalNttFastMeasured := preset.selectNat 80 10 2
  let checksumIterations := groupChecksumIterations measured [
    reversalNttMeasured, reversalNttFastMeasured
  ]
  let largeBatchHorner ← runTimed
    "univariate-batch-large-naive-horner" "CPolynomial" "evalBatchHorner" "BabyBear.Field"
    largeUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchHorner largeBatchPoly largeBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLargeBatchHorner ← runTimed
    "univariate-batch-large-naive-horner-fast" "CPolynomial" "evalBatchHorner"
    "BabyBear.Fast.Element"
    largeUnivariateBatchShape preset warmup measured
    (fun _ ↦ CPolynomial.evalBatchHorner fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let largeBatchSubproductReversalNtt ← runTimed
    "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Field"
    largeUnivariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLargeBatchSubproductReversalNtt ← runTimed
    "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod-fast" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Fast.Element"
    largeUnivariateBatchShape preset warmup reversalNttMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttMul fastReversalNttLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  let largeBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Field"
    largeUnivariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let fastLargeBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Fast.Element"
    largeUnivariateBatchShape preset warmup reversalNttFastMeasured
    (fun _ ↦ CPolynomial.evalBatchSubproduct fastNttFastMul fastReversalNttFastLowMod
      fastLargeBatchPoly fastLargeBatchPoints)
    (checksumArray checksumBabyBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-batch-large-babybear",
    title := "Univariate batch evaluation, large (BabyBear)",
    records := #[largeBatchHorner, largeBatchSubproductReversalNtt,
      largeBatchSubproductReversalNttFast, fastLargeBatchHorner,
      fastLargeBatchSubproductReversalNtt, fastLargeBatchSubproductReversalNttFast]
  }, gen)

/-- Runnable `CompPoly.Univariate.BatchEval` benchmark tasks. -/
def univariateBatchEvalTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-batch-small-babybear", "Univariate batch evaluation, small (BabyBear)"⟩
    runBabyBearUnivariateBatchSmall,
  BenchTask.fromGroupRunner
    ⟨"univariate-batch-medium-babybear", "Univariate batch evaluation, medium (BabyBear)"⟩
    runBabyBearUnivariateBatchMedium,
  BenchTask.fromGroupRunner
    ⟨"univariate-batch-large-babybear", "Univariate batch evaluation, large (BabyBear)"⟩
    runBabyBearUnivariateBatchLarge
]

/-- Run selected univariate batch-evaluation benchmarks. -/
def runUnivariateBatchEval (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateBatchEvalTasks preset selection gen

end CompPolyBench
