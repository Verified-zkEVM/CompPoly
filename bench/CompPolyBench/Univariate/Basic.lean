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
    (key nameSuffix fieldName fieldTitle : String) (hornerMeasured : Nat) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (zmodArray modulus 512 false).run gen
  let (points, gen) := (zmodArray modulus 32 false).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let checksumIterations := groupChecksumIterations measuredIterations [hornerMeasured]
  let sumRecord ← runTimed
    ("univariate-dense-sum-" ++ nameSuffix) "CPolynomial" "eval sum-of-powers" fieldName
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumZMod (checksumIterations := checksumIterations)
  let hornerRecord ← runTimed
    ("univariate-dense-horner-" ++ nameSuffix) "CPolynomial" "evalHorner" fieldName
    "degree<512, dense, 32 points" warmupIterations hornerMeasured
    (fun i => CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumZMod (checksumIterations := checksumIterations)
  pure ({
    groupKey := key,
    title := "Univariate dense evaluation (" ++ fieldTitle ++ ")",
    records := #[sumRecord, hornerRecord]
  }, gen)

/-- Benchmark dense BabyBear univariate evaluation. -/
private def runBabyBearUnivariateDense (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (babyBearArray 512 false).run gen
  let (points, gen) := (babyBearPoints 32).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let hornerMeasured := 45000
  let checksumIterations := groupChecksumIterations measuredIterations [hornerMeasured]
  let denseSum ← runTimed
    "univariate-dense-sum" "CPolynomial" "eval sum-of-powers" "BabyBear.Field"
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  let denseHorner ← runTimed
    "univariate-dense-horner" "CPolynomial" "evalHorner" "BabyBear.Field"
    "degree<512, dense, 32 points" warmupIterations hornerMeasured
    (fun i => CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-dense-babybear",
    title := "Univariate dense evaluation (BabyBear)",
    records := #[denseSum, denseHorner]
  }, gen)

/-- Benchmark sparse BabyBear univariate evaluation. -/
private def runBabyBearUnivariateSparse (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (sparseCoeffs, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 32).run gen
  let sparsePoly := cpolyOfArray sparseCoeffs
  let hornerMeasured := 50000
  let checksumIterations := groupChecksumIterations measuredIterations [hornerMeasured]
  let sparseSum ← runTimed
    "univariate-sparse-sum" "CPolynomial" "eval sum-of-powers" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.eval (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  let sparseHorner ← runTimed
    "univariate-sparse-horner" "CPolynomial" "evalHorner" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" warmupIterations hornerMeasured
    (fun i => CPolynomial.evalHorner (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-sparse-babybear",
    title := "Univariate sparse evaluation (BabyBear)",
    records := #[sparseSum, sparseHorner]
  }, gen)

/-- Benchmark small BabyBear monic-remainder variants. -/
private def runBabyBearUnivariateMonicRemainderSmall (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (batchCoeffs, gen) := (babyBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (babyBearPoints univariateBatchPointCount).run gen
  let batchPoly := cpolyOfArray batchCoeffs
  let modDivisor := monicDivisorFromPoints batchPoints
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
  let remainderMeasured := 3400
  let reversalConvolutionMeasured := 650
  let reversalNttMeasured := 550
  let reversalNttFastMeasured := 2200
  let checksumIterations := groupChecksumIterations modMeasuredIterations [
    remainderMeasured, reversalConvolutionMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let smallModNaive ← runTimed
    "univariate-mod-by-monic-naive" "CPolynomial" "modByMonic" "BabyBear.Field"
    univariateModShape modWarmupIterations modMeasuredIterations
    (fun _ => CPolynomial.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let smallModRemainder ← runTimed
    "univariate-mod-by-monic-remainder-only" "CPolynomial" "modByMonicRemainderOnly"
    "BabyBear.Field"
    univariateModShape modWarmupIterations remainderMeasured
    (fun _ => CPolynomial.modByMonicRemainderOnly batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let smallModReversalConvolution ← runTimed
    "univariate-mod-by-monic-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Field"
    univariateModShape modWarmupIterations reversalConvolutionMeasured
    (fun _ => reversalConvolutionLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let smallModReversalNtt ← runTimed
    "univariate-mod-by-monic-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Field"
    univariateModShape modWarmupIterations reversalNttMeasured
    (fun _ => reversalNttLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let smallModReversalNttFast ← runTimed
    "univariate-mod-by-monic-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    univariateModShape modWarmupIterations reversalNttFastMeasured
    (fun _ => reversalNttFastLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-monic-remainder-small-babybear",
    title := "Univariate monic remainder, small (BabyBear)",
    records := #[smallModNaive, smallModRemainder, smallModReversalConvolution,
      smallModReversalNtt, smallModReversalNttFast]
  }, gen)

/-- Benchmark medium BabyBear monic-remainder variants. -/
private def runBabyBearUnivariateMonicRemainderMedium (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (mediumBatchCoeffs, gen) := (babyBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (babyBearPoints mediumUnivariateBatchPointCount).run gen
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
  let mediumModDivisor := monicDivisorFromPoints mediumBatchPoints
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
  let remainderMeasured := 30
  let reversalNttMeasured := 200
  let reversalNttFastMeasured := 900
  let checksumIterations := groupChecksumIterations mediumModMeasuredIterations [
    remainderMeasured, reversalNttMeasured, reversalNttFastMeasured
  ]
  let mediumModRemainder ← runTimed
    "univariate-mod-by-monic-medium-remainder-only" "CPolynomial"
    "modByMonicRemainderOnly" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations remainderMeasured
    (fun _ => CPolynomial.modByMonicRemainderOnly mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumModReversalConvolution ← runTimed
    "univariate-mod-by-monic-medium-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations mediumModMeasuredIterations
    (fun _ => reversalConvolutionLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumModReversalNtt ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations reversalNttMeasured
    (fun _ => reversalNttLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  let mediumModReversalNttFast ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations reversalNttFastMeasured
    (fun _ => reversalNttFastLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-monic-remainder-medium-babybear",
    title := "Univariate monic remainder, medium (BabyBear)",
    records := #[mediumModRemainder, mediumModReversalConvolution, mediumModReversalNtt,
      mediumModReversalNttFast]
  }, gen)

/-- Benchmark dense Goldilocks univariate evaluation. -/
private def runGoldilocksUnivariateDense (gen : StdGen) : IO (BenchGroup × StdGen) := do
  runDenseUnivariateZMod
    Goldilocks.fieldSize "univariate-dense-goldilocks" "goldilocks" "Goldilocks.Field"
    "Goldilocks" 40000 gen

/-- Benchmark dense BN254 univariate evaluation. -/
private def runBn254UnivariateDense (gen : StdGen) : IO (BenchGroup × StdGen) := do
  runDenseUnivariateZMod
    BN254.scalarFieldSize "univariate-dense-bn254" "bn254" "BN254.ScalarField" "BN254"
    40000 gen

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

/-- Benchmark evaluation and public monic-remainder operations from `CompPoly.Univariate.Basic`. -/
def runUnivariateBasic (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks univariateBasicTasks selection gen

end CompPolyBench
