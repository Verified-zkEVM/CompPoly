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

/-- Benchmark dense univariate evaluation over a generic prime `ZMod` field. -/
private def runDenseUnivariateZMod (modulus : Nat) [Fact (Nat.Prime modulus)]
    (nameSuffix fieldName : String) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (zmodArray modulus 512 false).run gen
  let (points, gen) := (zmodArray modulus 32 false).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let sumRecord ← runTimed
    ("univariate-dense-sum-" ++ nameSuffix) "CPolynomial" "eval sum-of-powers" fieldName
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumZMod
  let hornerRecord ← runTimed
    ("univariate-dense-horner-" ++ nameSuffix) "CPolynomial" "evalHorner" fieldName
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumZMod
  pure ({
      title := fieldName ++ " univariate dense evaluation"
      records := #[sumRecord, hornerRecord] }, gen)

/-- Benchmark evaluation and public monic-remainder operations from `CompPoly.Univariate.Basic`. -/
def runUnivariateBasic (gen : StdGen) : IO (Array BenchGroup × StdGen) := do
  let (denseCoeffs, gen) := (babyBearArray 512 false).run gen
  let (sparseCoeffs, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 32).run gen
  let (batchCoeffs, gen) := (babyBearArray univariateBatchCoeffSlots false).run gen
  let (batchPoints, gen) := (babyBearPoints univariateBatchPointCount).run gen
  let (mediumBatchCoeffs, gen) := (babyBearArray mediumUnivariateBatchCoeffSlots false).run gen
  let (mediumBatchPoints, gen) := (babyBearPoints mediumUnivariateBatchPointCount).run gen
  let densePoly := cpolyOfArray denseCoeffs
  let sparsePoly := cpolyOfArray sparseCoeffs
  let batchPoly := cpolyOfArray batchCoeffs
  let mediumBatchPoly := cpolyOfArray mediumBatchCoeffs
  let modDivisor := monicDivisorFromPoints batchPoints
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
  let mut groups := #[]
  let denseSum ← runTimed
    "univariate-dense-sum" "CPolynomial" "eval sum-of-powers" "BabyBear.Field"
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.eval (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear
  let denseHorner ← runTimed
    "univariate-dense-horner" "CPolynomial" "evalHorner" "BabyBear.Field"
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.evalHorner (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear
  groups := groups.push {
    title := "BabyBear univariate dense evaluation"
    records := #[denseSum, denseHorner]
  }
  let sparseSum ← runTimed
    "univariate-sparse-sum" "CPolynomial" "eval sum-of-powers" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.eval (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear
  let sparseHorner ← runTimed
    "univariate-sparse-horner" "CPolynomial" "evalHorner" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.evalHorner (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear
  groups := groups.push {
    title := "BabyBear univariate sparse evaluation"
    records := #[sparseSum, sparseHorner]
  }
  let smallModNaive ← runTimed
    "univariate-mod-by-monic-naive" "CPolynomial" "modByMonic" "BabyBear.Field"
    univariateModShape modWarmupIterations modMeasuredIterations
    (fun _ => CPolynomial.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear)
  let smallModRemainder ← runTimed
    "univariate-mod-by-monic-remainder-only" "CPolynomial" "modByMonicRemainderOnly"
    "BabyBear.Field"
    univariateModShape modWarmupIterations modMeasuredIterations
    (fun _ => CPolynomial.modByMonicRemainderOnly batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear)
  let smallModReversalConvolution ← runTimed
    "univariate-mod-by-monic-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Field"
    univariateModShape modWarmupIterations modMeasuredIterations
    (fun _ => reversalConvolutionLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear)
  let smallModReversalNtt ← runTimed
    "univariate-mod-by-monic-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Field"
    univariateModShape modWarmupIterations modMeasuredIterations
    (fun _ => reversalNttLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear)
  let smallModReversalNttFast ← runTimed
    "univariate-mod-by-monic-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    univariateModShape modWarmupIterations modMeasuredIterations
    (fun _ => reversalNttFastLowMod.modByMonic batchPoly modDivisor)
    (checksumCPolynomial checksumBabyBear)
  groups := groups.push {
    title := "BabyBear univariate monic remainder, small"
    records := #[smallModNaive, smallModRemainder, smallModReversalConvolution,
      smallModReversalNtt, smallModReversalNttFast]
  }
  let mediumModRemainder ← runTimed
    "univariate-mod-by-monic-medium-remainder-only" "CPolynomial"
    "modByMonicRemainderOnly" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations mediumModMeasuredIterations
    (fun _ => CPolynomial.modByMonicRemainderOnly mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear)
  let mediumModReversalConvolution ← runTimed
    "univariate-mod-by-monic-medium-reversal-convolution-low-mul" "CPolynomial"
    "modByMonicByReversal, MulLowContext.convolution" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations mediumModMeasuredIterations
    (fun _ => reversalConvolutionLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear)
  let mediumModReversalNtt ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-low-mul" "CPolynomial"
    "modByMonicByReversal, FastMulLow.withFallback" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations mediumModMeasuredIterations
    (fun _ => reversalNttLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear)
  let mediumModReversalNttFast ← runTimed
    "univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul" "CPolynomial"
    "modByMonicByReversal, NTTFast.FastMulLow.withFallback" "BabyBear.Field"
    mediumUnivariateModShape mediumModWarmupIterations mediumModMeasuredIterations
    (fun _ => reversalNttFastLowMod.modByMonic mediumBatchPoly mediumModDivisor)
    (checksumCPolynomial checksumBabyBear)
  groups := groups.push {
    title := "BabyBear univariate monic remainder, medium"
    records := #[mediumModRemainder, mediumModReversalConvolution, mediumModReversalNtt,
      mediumModReversalNttFast]
  }
  let (goldilocksGroup, gen) ← runDenseUnivariateZMod
    Goldilocks.fieldSize "goldilocks" "Goldilocks.Field" gen
  groups := groups.push goldilocksGroup
  let (bn254Group, gen) ← runDenseUnivariateZMod
    BN254.scalarFieldSize "bn254" "BN254.ScalarField" gen
  groups := groups.push bn254Group
  pure (groups, gen)

end CompPolyBench
