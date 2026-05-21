/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Common
import CompPoly.Fields.BN254
import CompPoly.Univariate.NTT.FastMulLow
import CompPoly.Univariate.NTTFast.FastMulLow

/-!
# Benchmarks for `CompPoly.Univariate.Basic`
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Univariate.Basic`. -/
def univariateBasicGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-dense-babybear", "Univariate dense evaluation (BabyBear)"⟩,
  ⟨"univariate-sparse-babybear", "Univariate sparse evaluation (BabyBear)"⟩,
  ⟨"univariate-monic-remainder-small-babybear",
    "Univariate monic remainder, small (BabyBear)"⟩,
  ⟨"univariate-monic-remainder-medium-babybear",
    "Univariate monic remainder, medium (BabyBear)"⟩,
  ⟨"univariate-dense-goldilocks", "Univariate dense evaluation (Goldilocks)"⟩,
  ⟨"univariate-dense-bn254", "Univariate dense evaluation (BN254)"⟩
]

/-- Benchmark dense univariate evaluation over a generic prime `ZMod` field. -/
private def runDenseUnivariateZMod (modulus : Nat) [Fact (Nat.Prime modulus)]
    (key nameSuffix fieldName fieldTitle : String)
    (largeHornerMeasured mediumHornerMeasured smallHornerMeasured : Nat)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (zmodArray modulus 512 false).run gen
  let (points, gen) := (zmodArray modulus 32 false).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured :=
    preset.selectNat largeHornerMeasured mediumHornerMeasured smallHornerMeasured
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let sumRecord ← runTimed
    ("univariate-dense-sum-" ++ nameSuffix) "CPolynomial" "eval sum-of-powers" fieldName
    "degree<512, dense, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumZMod (checksumIterations := checksumIterations)
  let hornerRecord ← runTimed
    ("univariate-dense-horner-" ++ nameSuffix) "CPolynomial" "evalHorner" fieldName
    "degree<512, dense, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumZMod (checksumIterations := checksumIterations)
  pure ({
    groupKey := key,
    title := "Univariate dense evaluation (" ++ fieldTitle ++ ")",
    records := #[sumRecord, hornerRecord]
  }, gen)

/-- Benchmark dense BabyBear univariate evaluation. -/
private def runBabyBearUnivariateDense (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (babyBearArray 512 false).run gen
  let (points, gen) := (babyBearPoints 32).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let fastDenseCoeffs := babyBearFastArray denseCoeffs
  let fastPoints := babyBearFastArray points
  let fastDensePoly := cpolyOfArray fastDenseCoeffs
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 45000 6500 1300
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let denseSum ← runTimed
    "univariate-dense-sum" "CPolynomial" "eval sum-of-powers" "BabyBear.Field"
    "degree<512, dense, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  let fastDenseSum ← runTimed
    "univariate-dense-sum-fast" "CPolynomial" "eval sum-of-powers"
    "BabyBear.Fast.Element" "degree<512, dense, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (fastPoints.getD (i % fastPoints.size) 0) fastDensePoly)
    checksumBabyBearFast (checksumIterations := checksumIterations)
  let denseHorner ← runTimed
    "univariate-dense-horner" "CPolynomial" "evalHorner" "BabyBear.Field"
    "degree<512, dense, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  let fastDenseHorner ← runTimed
    "univariate-dense-horner-fast" "CPolynomial" "evalHorner" "BabyBear.Fast.Element"
    "degree<512, dense, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (fastPoints.getD (i % fastPoints.size) 0) fastDensePoly)
    checksumBabyBearFast (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-dense-babybear",
    title := "Univariate dense evaluation (BabyBear)",
    records := #[denseSum, denseHorner, fastDenseSum, fastDenseHorner]
  }, gen)

/-- Benchmark sparse BabyBear univariate evaluation. -/
private def runBabyBearUnivariateSparse (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (sparseCoeffs, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 32).run gen
  let sparsePoly := cpolyOfArray sparseCoeffs
  let fastSparseCoeffs := babyBearFastArray sparseCoeffs
  let fastPoints := babyBearFastArray points
  let fastSparsePoly := cpolyOfArray fastSparseCoeffs
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 50000 7000 1500
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let sparseSum ← runTimed
    "univariate-sparse-sum" "CPolynomial" "eval sum-of-powers" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  let fastSparseSum ← runTimed
    "univariate-sparse-sum-fast" "CPolynomial" "eval sum-of-powers"
    "BabyBear.Fast.Element"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (fastPoints.getD (i % fastPoints.size) 0) fastSparsePoly)
    checksumBabyBearFast (checksumIterations := checksumIterations)
  let sparseHorner ← runTimed
    "univariate-sparse-horner" "CPolynomial" "evalHorner" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  let fastSparseHorner ← runTimed
    "univariate-sparse-horner-fast" "CPolynomial" "evalHorner" "BabyBear.Fast.Element"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (fastPoints.getD (i % fastPoints.size) 0)
      fastSparsePoly)
    checksumBabyBearFast (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-sparse-babybear",
    title := "Univariate sparse evaluation (BabyBear)",
    records := #[sparseSum, sparseHorner, fastSparseSum, fastSparseHorner]
  }, gen)

/-- Benchmark small BabyBear monic-remainder variants. -/
private def runBabyBearUnivariateMonicRemainderSmall (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (batchCoeffs, gen) := (babyBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (babyBearPoints univariateBatchPointCount).run gen
  let batchPoly := cpolyOfArray batchCoeffs
  let modDivisor := monicDivisorFromPoints batchPoints
  let fastBatchCoeffs := babyBearFastArray batchCoeffs
  let fastBatchPoints := babyBearFastArray batchPoints
  let fastBatchPoly := cpolyOfArray fastBatchCoeffs
  let fastModDivisor := monicDivisorFromPoints fastBatchPoints
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
  let warmup := modWarmupIterations preset
  let measured := modMeasuredIterations preset
  let remainderMeasured := preset.selectNat 3400 500 100
  let reversalConvolutionMeasured := preset.selectNat 650 100 20
  let reversalNttMeasured := preset.selectNat 550 80 20
  let reversalNttFastMeasured := preset.selectNat 2200 300 60
  let checksumIterations := groupChecksumIterations measured [
    remainderMeasured, reversalConvolutionMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let smallModNaive ← runTimed
    "univariate-mod-by-monic-naive" "CPolynomial" "modByMonic" "BabyBear.Field"
    univariateModShape preset warmup measured
    (fun _ ↦ CPolynomial.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallModNaive ← runTimed
    "univariate-mod-by-monic-naive-fast" "CPolynomial" "modByMonic"
    "BabyBear.Fast.Element"
    univariateModShape preset warmup measured
    (fun _ ↦ CPolynomial.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallModRemainder ← runTimed
    "univariate-mod-by-monic-remainder-only" "CPolynomial" "modByMonicRemainderOnly"
    "BabyBear.Field"
    univariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallModRemainder ← runTimed
    "univariate-mod-by-monic-remainder-only-fast" "CPolynomial" "modByMonicRemainderOnly"
    "BabyBear.Fast.Element"
    univariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallModReversalConvolution ← runTimed
    "univariate-mod-by-monic-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Field"
    univariateModShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ reversalConvolutionLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallModReversalConvolution ← runTimed
    "univariate-mod-by-monic-reversal-convolution-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Fast.Element"
    univariateModShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ fastReversalConvolutionLowMod.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallModReversalNtt ← runTimed
    "univariate-mod-by-monic-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Field"
    univariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ reversalNttLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallModReversalNtt ← runTimed
    "univariate-mod-by-monic-reversal-ntt-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Fast.Element"
    univariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ fastReversalNttLowMod.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let smallModReversalNttFast ← runTimed
    "univariate-mod-by-monic-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    univariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ reversalNttFastLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastSmallModReversalNttFast ← runTimed
    "univariate-mod-by-monic-reversal-ntt-fast-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Fast.Element"
    univariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ fastReversalNttFastLowMod.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-monic-remainder-small-babybear",
    title := "Univariate monic remainder, small (BabyBear)",
    records := #[smallModNaive, smallModRemainder, smallModReversalConvolution,
      smallModReversalNtt, smallModReversalNttFast, fastSmallModNaive,
      fastSmallModRemainder, fastSmallModReversalConvolution, fastSmallModReversalNtt,
      fastSmallModReversalNttFast]
  }, gen)

/-- Benchmark medium BabyBear monic-remainder variants. -/
private def runBabyBearUnivariateMonicRemainderMedium (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mediumBatchCoeffs, gen) := (babyBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (babyBearPoints mediumUnivariateBatchPointCount).run gen
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
  let mediumModDivisor := monicDivisorFromPoints mediumBatchPoints
  let fastMediumBatchCoeffs := babyBearFastArray mediumBatchCoeffs
  let fastMediumBatchPoints := babyBearFastArray mediumBatchPoints
  let fastMediumBatchPoly := cpolyOfArray fastMediumBatchCoeffs
  let fastMediumModDivisor := monicDivisorFromPoints fastMediumBatchPoints
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
  let warmup := mediumModWarmupIterations preset
  let measured := mediumModMeasuredIterations preset
  let remainderMeasured := preset.selectNat 30 5 1
  let reversalNttMeasured := preset.selectNat 200 30 5
  let reversalNttFastMeasured := preset.selectNat 900 130 30
  let checksumIterations := groupChecksumIterations measured [
    remainderMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let mediumModRemainder ← runTimed
    "univariate-mod-by-monic-medium-remainder-only" "CPolynomial"
    "modByMonicRemainderOnly" "BabyBear.Field"
    mediumUnivariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumModRemainder ← runTimed
    "univariate-mod-by-monic-medium-remainder-only-fast" "CPolynomial"
    "modByMonicRemainderOnly" "BabyBear.Fast.Element"
    mediumUnivariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumModReversalConvolution ← runTimed
    "univariate-mod-by-monic-medium-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Field"
    mediumUnivariateModShape preset warmup measured
    (fun _ ↦ reversalConvolutionLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumModReversalConvolution ← runTimed
    "univariate-mod-by-monic-medium-reversal-convolution-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Fast.Element"
    mediumUnivariateModShape preset warmup measured
    (fun _ ↦ fastReversalConvolutionLowMod.modByMonic fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumModReversalNtt ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Field"
    mediumUnivariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ reversalNttLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumModReversalNtt ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Fast.Element"
    mediumUnivariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ fastReversalNttLowMod.modByMonic fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  let mediumModReversalNttFast ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    mediumUnivariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ reversalNttFastLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let fastMediumModReversalNttFast ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Fast.Element"
    mediumUnivariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ fastReversalNttFastLowMod.modByMonic fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumBabyBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-monic-remainder-medium-babybear",
    title := "Univariate monic remainder, medium (BabyBear)",
    records := #[mediumModRemainder, mediumModReversalConvolution, mediumModReversalNtt,
      mediumModReversalNttFast, fastMediumModRemainder, fastMediumModReversalConvolution,
      fastMediumModReversalNtt, fastMediumModReversalNttFast]
  }, gen)

/-- Benchmark dense Goldilocks univariate evaluation. -/
private def runGoldilocksUnivariateDense (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runDenseUnivariateZMod
    Goldilocks.fieldSize "univariate-dense-goldilocks" "goldilocks" "Goldilocks.Field"
    "Goldilocks" 40000 6000 1200 preset gen

/-- Benchmark dense BN254 univariate evaluation. -/
private def runBn254UnivariateDense (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runDenseUnivariateZMod
    BN254.scalarFieldSize "univariate-dense-bn254" "bn254" "BN254.ScalarField" "BN254"
    40000 6000 1200 preset gen

/-- Runnable `CompPoly.Univariate.Basic` benchmark tasks. -/
def univariateBasicTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-dense-babybear", "Univariate dense evaluation (BabyBear)"⟩
    runBabyBearUnivariateDense,
  BenchTask.fromGroupRunner
    ⟨"univariate-sparse-babybear", "Univariate sparse evaluation (BabyBear)"⟩
    runBabyBearUnivariateSparse,
  BenchTask.fromGroupRunner
    ⟨"univariate-monic-remainder-small-babybear",
      "Univariate monic remainder, small (BabyBear)"⟩
    runBabyBearUnivariateMonicRemainderSmall,
  BenchTask.fromGroupRunner
    ⟨"univariate-monic-remainder-medium-babybear",
      "Univariate monic remainder, medium (BabyBear)"⟩
    runBabyBearUnivariateMonicRemainderMedium,
  BenchTask.fromGroupRunner
    ⟨"univariate-dense-goldilocks", "Univariate dense evaluation (Goldilocks)"⟩
    runGoldilocksUnivariateDense,
  BenchTask.fromGroupRunner
    ⟨"univariate-dense-bn254", "Univariate dense evaluation (BN254)"⟩
    runBn254UnivariateDense
]

/-- Run selected evaluation and public monic-remainder benchmarks. -/
def runUnivariateBasic (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateBasicTasks preset selection gen

end CompPolyBench
