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
private def runBabyBearUnivariateBatchSmall (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (batchCoeffs, gen) := (babyBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (babyBearPoints univariateBatchPointCount).run gen
  let batchPoly := cpolyOfArray batchCoeffs
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
  let sumMeasured := 1750
  let hornerMeasured := 11500
  let remainderMeasured := 900
  let nttMeasured := 700
  let nttFastMeasured := 800
  let reversalConvolutionMeasured := 150
  let reversalNttMeasured := 150
  let reversalNttFastMeasured := 450
  let checksumIterations := groupChecksumIterations batchMeasuredIterations [
    sumMeasured, hornerMeasured, remainderMeasured, nttMeasured, nttFastMeasured,
    reversalConvolutionMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let smallBatchSum ← runTimed
    "univariate-batch-naive-sum" "CPolynomial" "evalBatch" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations sumMeasured
    (fun _ => CPolynomial.evalBatch batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchHorner ← runTimed
    "univariate-batch-naive-horner" "CPolynomial" "evalBatchHorner" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations hornerMeasured
    (fun _ => CPolynomial.evalBatchHorner batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductNaive ← runTimed
    "univariate-batch-subproduct-naive-mul-naive-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations batchMeasuredIterations
    (fun _ => CPolynomial.evalBatchSubproduct naiveMul naiveMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductRemainder ← runTimed
    "univariate-batch-subproduct-naive-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations remainderMeasured
    (fun _ => CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations nttMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations nttFastMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalConvolution ← runTimed
    "univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/reversal-convolution-low mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations reversalConvolutionMeasured
    (fun _ => CPolynomial.evalBatchSubproduct naiveMul reversalConvolutionLowMod batchPoly
      batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalNtt ← runTimed
    "univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations reversalNttMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod batchPoly batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let smallBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod" "BabyBear.Field"
    univariateBatchShape batchWarmupIterations reversalNttFastMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod batchPoly
      batchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-batch-small-babybear",
    title := "Univariate batch evaluation, small (BabyBear)",
    records := #[smallBatchSum, smallBatchHorner, smallBatchSubproductNaive,
      smallBatchSubproductRemainder, smallBatchSubproductNtt, smallBatchSubproductNttFast,
      smallBatchSubproductReversalConvolution, smallBatchSubproductReversalNtt,
      smallBatchSubproductReversalNttFast]
  }, gen)

/-- Run the medium BabyBear univariate batch-evaluation benchmark group. -/
private def runBabyBearUnivariateBatchMedium (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (mediumBatchCoeffs, gen) := (babyBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (babyBearPoints mediumUnivariateBatchPointCount).run gen
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
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
  let hornerMeasured := 150
  let reversalNttMeasured := 50
  let reversalNttFastMeasured := 170
  let checksumIterations := groupChecksumIterations mediumBatchMeasuredIterations [
    hornerMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let mediumBatchSum ← runTimed
    "univariate-batch-medium-naive-sum" "CPolynomial" "evalBatch" "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations mediumBatchMeasuredIterations
    (fun _ => CPolynomial.evalBatch mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumBatchHorner ← runTimed
    "univariate-batch-medium-naive-horner" "CPolynomial" "evalBatchHorner" "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations hornerMeasured
    (fun _ => CPolynomial.evalBatchHorner mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumBatchSubproductRemainder ← runTimed
    "univariate-batch-medium-subproduct-naive-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct naive mul/remainder-only mod" "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations mediumBatchMeasuredIterations
    (fun _ => CPolynomial.evalBatchSubproduct naiveMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumBatchSubproductNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/remainder-only mod" "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations mediumBatchMeasuredIterations
    (fun _ => CPolynomial.evalBatchSubproduct nttMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumBatchSubproductNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod" "CPolynomial"
    "evalBatchSubproduct ntt-fast mul/remainder-only mod" "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations mediumBatchMeasuredIterations
    (fun _ => CPolynomial.evalBatchSubproduct nttFastMul remainderOnlyMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumBatchSubproductReversalNtt ← runTimed
    "univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations reversalNttMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod mediumBatchPoly
      mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Field"
    mediumUnivariateBatchShape mediumBatchWarmupIterations reversalNttFastMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod
      mediumBatchPoly mediumBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-batch-medium-babybear",
    title := "Univariate batch evaluation, medium (BabyBear)",
    records := #[mediumBatchSum, mediumBatchHorner, mediumBatchSubproductRemainder,
      mediumBatchSubproductNtt, mediumBatchSubproductNttFast, mediumBatchSubproductReversalNtt,
      mediumBatchSubproductReversalNttFast]
  }, gen)

/-- Run the large BabyBear univariate batch-evaluation benchmark group. -/
private def runBabyBearUnivariateBatchLarge (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (largeBatchCoeffs, gen) := (babyBearArray largeUnivariateBatchCoeffSlots false).run gen
  let (largeBatchPoints, gen) := (babyBearPoints largeUnivariateBatchPointCount).run gen
  let largeBatchPoly := cpolyOfArray largeBatchCoeffs
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
  let reversalNttMeasured := 20
  let reversalNttFastMeasured := 80
  let checksumIterations := groupChecksumIterations largeBatchMeasuredIterations [
    reversalNttMeasured, reversalNttFastMeasured
  ]
  let largeBatchHorner ← runTimed
    "univariate-batch-large-naive-horner" "CPolynomial" "evalBatchHorner" "BabyBear.Field"
    largeUnivariateBatchShape largeBatchWarmupIterations largeBatchMeasuredIterations
    (fun _ => CPolynomial.evalBatchHorner largeBatchPoly largeBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let largeBatchSubproductReversalNtt ← runTimed
    "univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod" "CPolynomial"
    "evalBatchSubproduct ntt mul/reversal-ntt-low mod" "BabyBear.Field"
    largeUnivariateBatchShape largeBatchWarmupIterations reversalNttMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttMul reversalNttLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  let largeBatchSubproductReversalNttFast ← runTimed
    "univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod"
    "CPolynomial" "evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod"
    "BabyBear.Field"
    largeUnivariateBatchShape largeBatchWarmupIterations reversalNttFastMeasured
    (fun _ => CPolynomial.evalBatchSubproduct nttFastMul reversalNttFastLowMod largeBatchPoly
      largeBatchPoints)
    (checksumArray checksumBabyBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-batch-large-babybear",
    title := "Univariate batch evaluation, large (BabyBear)",
    records := #[largeBatchHorner, largeBatchSubproductReversalNtt,
      largeBatchSubproductReversalNttFast]
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

/-- Run univariate batch-evaluation benchmarks. -/
def runUnivariateBatchEval (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateBatchEvalTasks selection gen

end CompPolyBench
