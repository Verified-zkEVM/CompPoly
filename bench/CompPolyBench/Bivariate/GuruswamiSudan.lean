/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Core
import CompPolyBench.Bivariate.GuruswamiSudan.ReceivedWord

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for dense and Lee-O'Sullivan interpolation,
Roth-Ruckenstein and Alekhnovich root finding, packed distance filtering, and
backend-parametric `gsCore` and `gsFilteredCore`.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

private def runGsInterpolationSystemKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsSmallBenchmarkPoints message
  let fastPoints := gsSmallBenchmarkPoints fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 3 1 1
  let fastMeasured := preset.selectNat 10 2 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-system" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup measured
    (fun _ ↦ interpolationMatrix points gsSmallParams)
    (checksumDenseMatrix checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-system-fast" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastMeasured
    (fun _ ↦ interpolationMatrix fastPoints gsSmallParams)
    (checksumDenseMatrix checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-system-small-koalabear",
    title := "Guruswami-Sudan dense interpolation system construction, small (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsInterpolationSolveKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsSmallBenchmarkPoints message
  let fastPoints := gsSmallBenchmarkPoints fastMessage
  let matrix := interpolationMatrix points gsSmallParams
  let fastMatrix := interpolationMatrix fastPoints gsSmallParams
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let inPlaceMeasured := preset.selectNat 8 2 1
  let fastInPlaceMeasured := preset.selectNat 16 3 1
  let checksumIterations := groupChecksumIterations measured
    [fastMeasured, inPlaceMeasured, fastInPlaceMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-solve-copying" "DenseMatrix"
    "Homogeneous interpolation solve, copying"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup measured
    (fun _ ↦ DenseMatrix.homogeneousWitness matrix)
    (checksumOptionArray checksumKoalaBear) checksumIterations
  let inPlaceRow <- runTimed
    "guruswami-sudan-interp-solve" "DenseMatrix"
    "Homogeneous interpolation solve, in-place"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup inPlaceMeasured
    (fun _ ↦ DenseMatrix.homogeneousWitnessInPlace matrix)
    (checksumOptionArray checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-solve-copying-fast" "DenseMatrix"
    "Homogeneous interpolation solve, copying"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastMeasured
    (fun _ ↦ DenseMatrix.homogeneousWitness fastMatrix)
    (checksumOptionArray checksumKoalaBearFast) checksumIterations
  let fastInPlaceRow <- runTimed
    "guruswami-sudan-interp-solve-inplace-fast" "DenseMatrix"
    "Homogeneous interpolation solve, in-place"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastInPlaceMeasured
    (fun _ ↦ DenseMatrix.homogeneousWitnessInPlace fastMatrix)
    (checksumOptionArray checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-solve-small-koalabear",
    title := "Guruswami-Sudan dense interpolation solving, small (KoalaBear)",
    records := #[row, inPlaceRow, fastRow, fastInPlaceRow]
  }, gen)

private def runGsInterpolationSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsSmallBenchmarkPoints message
  let fastPoints := gsSmallBenchmarkPoints fastMessage
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 100 15 3
  let leeSubproductMeasured := preset.selectNat 90 13 3
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 600 90 20
  let fastLeeSubproductMeasured := preset.selectNat 400 60 10
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-interp-dense-small" "CBivariate"
    "Dense linear"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup denseMeasured
    (fun _ ↦ koalaBearDenseInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
    checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup leeDirectMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup leeSubproductMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
    checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-interp-dense-small-fast" "CBivariate"
    "Dense linear"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastDenseMeasured
    (fun _ ↦ fastKoalaBearDenseInterpContext.interpolate fastPoints gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastLeeDirectMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastLeeSubproductMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-small-koalabear",
    title := "Guruswami-Sudan interpolation, small (KoalaBear)",
    records := #[
      denseRow, leeDirectRow, leeSubproductRow,
      fastDenseRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsRootKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let Q := nonlinearRootBenchmarkQ message
  let fastQ := nonlinearRootBenchmarkQ fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 20 3 1
  let nttFastMeasured := preset.selectNat 20 3 1
  let fastMeasured := preset.selectNat 80 10 2
  let fastNttFastMeasured := preset.selectNat 80 10 2
  let alekhnovichMeasured := preset.selectNat 10 2 1
  let alekhnovichNttFastMeasured := preset.selectNat 10 2 1
  let alekhnovichFastMeasured := preset.selectNat 30 5 1
  let alekhnovichFastNttFastMeasured := preset.selectNat 30 5 1
  let checksumIterations := groupChecksumIterations measured [
    nttFastMeasured, fastMeasured, fastNttFastMeasured, alekhnovichMeasured,
    alekhnovichNttFastMeasured, alekhnovichFastMeasured, alekhnovichFastNttFastMeasured
  ]
  let row <- runTimed
    "guruswami-sudan-root-roth" "CBivariate"
    "Roth-Ruckenstein root finding with nonlinear field-root equations"
    "KoalaBear.Field" gsRootShape preset warmup measured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFieldRoots Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let nttFastRow <- runTimed
    "guruswami-sudan-root-roth-nttfast" "CBivariate"
    "Roth-Ruckenstein root finding with NTTFast field-root equations"
    "KoalaBear.Field" gsRootShape preset warmup nttFastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFieldRootsFast Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-root-roth-fast" "CBivariate"
    "Roth-Ruckenstein root finding with nonlinear field-root equations"
    "KoalaBear.Fast.Field" gsRootShape preset warmup fastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFastFieldRoots fastQ gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastNttFastRow <- runTimed
    "guruswami-sudan-root-roth-fast-nttfast" "CBivariate"
    "Roth-Ruckenstein root finding with NTTFast field-root equations"
    "KoalaBear.Fast.Field" gsRootShape preset warmup fastNttFastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFastFieldRootsFast fastQ
      gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  let alekhnovichRow <- runTimed
    "guruswami-sudan-root-alekhnovich" "CBivariate"
    "Alekhnovich root finding with nonlinear field-root equations"
    "KoalaBear.Field" gsRootShape preset warmup alekhnovichMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFieldRoots Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let alekhnovichNttFastRow <- runTimed
    "guruswami-sudan-root-alekhnovich-nttfast" "CBivariate"
    "Alekhnovich root finding with NTTFast field-root equations"
    "KoalaBear.Field" gsRootShape preset warmup alekhnovichNttFastMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFieldRootsFast Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let alekhnovichFastRow <- runTimed
    "guruswami-sudan-root-alekhnovich-fast" "CBivariate"
    "Alekhnovich root finding with nonlinear field-root equations"
    "KoalaBear.Fast.Field" gsRootShape preset warmup alekhnovichFastMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFastFieldRoots fastQ gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  let alekhnovichFastNttFastRow <- runTimed
    "guruswami-sudan-root-alekhnovich-fast-nttfast" "CBivariate"
    "Alekhnovich root finding with NTTFast field-root equations"
    "KoalaBear.Fast.Field" gsRootShape preset warmup alekhnovichFastNttFastMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFastFieldRootsFast fastQ
      gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-root-koalabear",
    title := "Guruswami-Sudan root finding (KoalaBear)",
    records := #[row, nttFastRow, alekhnovichRow, alekhnovichNttFastRow,
      fastRow, fastNttFastRow, alekhnovichFastRow, alekhnovichFastNttFastRow]
  }, gen)

private def runGsPackedFilterKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let radius : Nat := 0
  let candidateCount := preset.selectNat 128 64 32
  let inputShape := s!"n={gsPointCount},k={gsMessageDegree},cand={candidateCount},r={radius}"
  let candidates : Array (CPolynomial KoalaBear.Field) :=
    (List.range candidateCount).map (fun i ↦
      message + CPolynomial.C ((i + 1 : Nat) : KoalaBear.Field)) |>.toArray
  let fastCandidates : Array (CPolynomial KoalaBear.Fast.Field) :=
    (List.range candidateCount).map (fun i ↦
      fastMessage + CPolynomial.C ((i + 1 : Nat) : KoalaBear.Fast.Field)) |>.toArray
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 20 3 1
  let fastMeasured := preset.selectNat 200 30 5
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-packed-filter" "CPolynomial"
    "Packed distance filtering"
    "KoalaBear.Field" inputShape preset warmup measured
    (fun _ ↦ candidates.filter (passesCandidateDistance points radius))
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-packed-filter-fast" "CPolynomial"
    "Packed distance filtering"
    "KoalaBear.Fast.Field" inputShape preset warmup fastMeasured
    (fun _ ↦ fastCandidates.filter (passesCandidateDistance fastPoints radius))
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-packed-filter-koalabear",
    title := "Guruswami-Sudan packed distance filtering (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

/-- Runnable GS benchmark tasks. -/
def guruswamiSudanTasks : List BenchTask := [
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 0
    ⟨"guruswami-sudan-interp-system-small-koalabear", ""⟩) runGsInterpolationSystemKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 1
    ⟨"guruswami-sudan-interp-solve-small-koalabear", ""⟩) runGsInterpolationSolveKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 2
    ⟨"guruswami-sudan-interp-small-koalabear", ""⟩) runGsInterpolationSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 3
    ⟨"guruswami-sudan-root-koalabear", ""⟩) runGsRootKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 4
    ⟨"guruswami-sudan-core-small-koalabear", ""⟩) runGsCoreSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 5
    ⟨"guruswami-sudan-packed-filter-koalabear", ""⟩) runGsPackedFilterKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 6
    ⟨"guruswami-sudan-filtered-core-small-koalabear", ""⟩) runGsFilteredCoreSmallKoala
] ++ guruswamiSudanReceivedWordTasks

end CompPolyBench
