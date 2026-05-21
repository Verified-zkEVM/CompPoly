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
  ⟨"univariate-dense-koalabear", "Univariate dense evaluation (KoalaBear)"⟩,
  ⟨"univariate-sparse-koalabear", "Univariate sparse evaluation (KoalaBear)"⟩,
  ⟨"univariate-monic-remainder-small-koalabear",
    "Univariate monic remainder, small (KoalaBear)"⟩,
  ⟨"univariate-monic-remainder-medium-koalabear",
    "Univariate monic remainder, medium (KoalaBear)"⟩,
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

/-- Benchmark dense KoalaBear univariate evaluation. -/
private def runKoalaBearUnivariateDense (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (koalaBearArray 512 false).run gen
  let (points, gen) := (koalaBearPoints 32).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let fastDenseCoeffs := koalaBearFastArray denseCoeffs
  let fastPoints := koalaBearFastArray points
  let fastDensePoly := cpolyOfArray fastDenseCoeffs
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 45000 6500 1300
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let denseSum ← runTimed
    "univariate-dense-sum" "CPolynomial" "eval sum-of-powers" "KoalaBear.Field"
    "degree<512, dense, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastDenseSum ← runTimed
    "univariate-dense-sum-fast" "CPolynomial" "eval sum-of-powers"
    "KoalaBear.Fast.Element" "degree<512, dense, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (fastPoints.getD (i % fastPoints.size) 0) fastDensePoly)
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  let denseHorner ← runTimed
    "univariate-dense-horner" "CPolynomial" "evalHorner" "KoalaBear.Field"
    "degree<512, dense, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastDenseHorner ← runTimed
    "univariate-dense-horner-fast" "CPolynomial" "evalHorner" "KoalaBear.Fast.Element"
    "degree<512, dense, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (fastPoints.getD (i % fastPoints.size) 0) fastDensePoly)
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-dense-koalabear",
    title := "Univariate dense evaluation (KoalaBear)",
    records := #[denseSum, denseHorner, fastDenseSum, fastDenseHorner]
  }, gen)

/-- Benchmark sparse KoalaBear univariate evaluation. -/
private def runKoalaBearUnivariateSparse (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (sparseCoeffs, gen) := (koalaBearArray 512 true).run gen
  let (points, gen) := (koalaBearPoints 32).run gen
  let sparsePoly := cpolyOfArray sparseCoeffs
  let fastSparseCoeffs := koalaBearFastArray sparseCoeffs
  let fastPoints := koalaBearFastArray points
  let fastSparsePoly := cpolyOfArray fastSparseCoeffs
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat 50000 7000 1500
  let checksumIterations := groupChecksumIterations measured [hornerMeasured]
  let sparseSum ← runTimed
    "univariate-sparse-sum" "CPolynomial" "eval sum-of-powers" "KoalaBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (points.getD (i % points.size) 0) sparsePoly)
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastSparseSum ← runTimed
    "univariate-sparse-sum-fast" "CPolynomial" "eval sum-of-powers"
    "KoalaBear.Fast.Element"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup measured
    (fun i ↦ CPolynomial.eval (fastPoints.getD (i % fastPoints.size) 0) fastSparsePoly)
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  let sparseHorner ← runTimed
    "univariate-sparse-horner" "CPolynomial" "evalHorner" "KoalaBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (points.getD (i % points.size) 0) sparsePoly)
    checksumKoalaBear (checksumIterations := checksumIterations)
  let fastSparseHorner ← runTimed
    "univariate-sparse-horner-fast" "CPolynomial" "evalHorner" "KoalaBear.Fast.Element"
    "degree<512, one nonzero per 4 coeffs, 32 points" preset warmup hornerMeasured
    (fun i ↦ CPolynomial.evalHorner (fastPoints.getD (i % fastPoints.size) 0)
      fastSparsePoly)
    checksumKoalaBearFast (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-sparse-koalabear",
    title := "Univariate sparse evaluation (KoalaBear)",
    records := #[sparseSum, sparseHorner, fastSparseSum, fastSparseHorner]
  }, gen)

/-- Benchmark small KoalaBear monic-remainder variants. -/
private def runKoalaBearUnivariateMonicRemainderSmall (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (batchCoeffs, gen) := (koalaBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (koalaBearPoints univariateBatchPointCount).run gen
  let batchPoly := cpolyOfArray batchCoeffs
  let modDivisor := monicDivisorFromPoints batchPoints
  let fastBatchCoeffs := koalaBearFastArray batchCoeffs
  let fastBatchPoints := koalaBearFastArray batchPoints
  let fastBatchPoly := cpolyOfArray fastBatchCoeffs
  let fastModDivisor := monicDivisorFromPoints fastBatchPoints
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
    "univariate-mod-by-monic-naive" "CPolynomial" "modByMonic" "KoalaBear.Field"
    univariateModShape preset warmup measured
    (fun _ ↦ CPolynomial.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallModNaive ← runTimed
    "univariate-mod-by-monic-naive-fast" "CPolynomial" "modByMonic"
    "KoalaBear.Fast.Element"
    univariateModShape preset warmup measured
    (fun _ ↦ CPolynomial.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallModRemainder ← runTimed
    "univariate-mod-by-monic-remainder-only" "CPolynomial" "modByMonicRemainderOnly"
    "KoalaBear.Field"
    univariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly batchPoly modDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallModRemainder ← runTimed
    "univariate-mod-by-monic-remainder-only-fast" "CPolynomial" "modByMonicRemainderOnly"
    "KoalaBear.Fast.Element"
    univariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallModReversalConvolution ← runTimed
    "univariate-mod-by-monic-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "KoalaBear.Field"
    univariateModShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ reversalConvolutionLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallModReversalConvolution ← runTimed
    "univariate-mod-by-monic-reversal-convolution-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "KoalaBear.Fast.Element"
    univariateModShape preset warmup reversalConvolutionMeasured
    (fun _ ↦ fastReversalConvolutionLowMod.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallModReversalNtt ← runTimed
    "univariate-mod-by-monic-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "KoalaBear.Field"
    univariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ reversalNttLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallModReversalNtt ← runTimed
    "univariate-mod-by-monic-reversal-ntt-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "KoalaBear.Fast.Element"
    univariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ fastReversalNttLowMod.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let smallModReversalNttFast ← runTimed
    "univariate-mod-by-monic-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "KoalaBear.Field"
    univariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ reversalNttFastLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSmallModReversalNttFast ← runTimed
    "univariate-mod-by-monic-reversal-ntt-fast-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "KoalaBear.Fast.Element"
    univariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ fastReversalNttFastLowMod.modByMonic fastBatchPoly fastModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-monic-remainder-small-koalabear",
    title := "Univariate monic remainder, small (KoalaBear)",
    records := #[smallModNaive, smallModRemainder, smallModReversalConvolution,
      smallModReversalNtt, smallModReversalNttFast, fastSmallModNaive,
      fastSmallModRemainder, fastSmallModReversalConvolution, fastSmallModReversalNtt,
      fastSmallModReversalNttFast]
  }, gen)

/-- Benchmark medium KoalaBear monic-remainder variants. -/
private def runKoalaBearUnivariateMonicRemainderMedium (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mediumBatchCoeffs, gen) := (koalaBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (koalaBearPoints mediumUnivariateBatchPointCount).run gen
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
  let mediumModDivisor := monicDivisorFromPoints mediumBatchPoints
  let fastMediumBatchCoeffs := koalaBearFastArray mediumBatchCoeffs
  let fastMediumBatchPoints := koalaBearFastArray mediumBatchPoints
  let fastMediumBatchPoly := cpolyOfArray fastMediumBatchCoeffs
  let fastMediumModDivisor := monicDivisorFromPoints fastMediumBatchPoints
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
    "modByMonicRemainderOnly" "KoalaBear.Field"
    mediumUnivariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumModRemainder ← runTimed
    "univariate-mod-by-monic-medium-remainder-only-fast" "CPolynomial"
    "modByMonicRemainderOnly" "KoalaBear.Fast.Element"
    mediumUnivariateModShape preset warmup remainderMeasured
    (fun _ ↦ CPolynomial.modByMonicRemainderOnly fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumModReversalConvolution ← runTimed
    "univariate-mod-by-monic-medium-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "KoalaBear.Field"
    mediumUnivariateModShape preset warmup measured
    (fun _ ↦ reversalConvolutionLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumModReversalConvolution ← runTimed
    "univariate-mod-by-monic-medium-reversal-convolution-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "KoalaBear.Fast.Element"
    mediumUnivariateModShape preset warmup measured
    (fun _ ↦ fastReversalConvolutionLowMod.modByMonic fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumModReversalNtt ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "KoalaBear.Field"
    mediumUnivariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ reversalNttLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumModReversalNtt ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "KoalaBear.Fast.Element"
    mediumUnivariateModShape preset warmup reversalNttMeasured
    (fun _ ↦ fastReversalNttLowMod.modByMonic fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let mediumModReversalNttFast ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "KoalaBear.Field"
    mediumUnivariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ reversalNttFastLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastMediumModReversalNttFast ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul-fast" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "KoalaBear.Fast.Element"
    mediumUnivariateModShape preset warmup reversalNttFastMeasured
    (fun _ ↦ fastReversalNttFastLowMod.modByMonic fastMediumBatchPoly
      fastMediumModDivisor)
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-monic-remainder-medium-koalabear",
    title := "Univariate monic remainder, medium (KoalaBear)",
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
    ⟨"univariate-dense-koalabear", "Univariate dense evaluation (KoalaBear)"⟩
    runKoalaBearUnivariateDense,
  BenchTask.fromGroupRunner
    ⟨"univariate-sparse-koalabear", "Univariate sparse evaluation (KoalaBear)"⟩
    runKoalaBearUnivariateSparse,
  BenchTask.fromGroupRunner
    ⟨"univariate-monic-remainder-small-koalabear",
      "Univariate monic remainder, small (KoalaBear)"⟩
    runKoalaBearUnivariateMonicRemainderSmall,
  BenchTask.fromGroupRunner
    ⟨"univariate-monic-remainder-medium-koalabear",
      "Univariate monic remainder, medium (KoalaBear)"⟩
    runKoalaBearUnivariateMonicRemainderMedium,
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
