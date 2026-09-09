/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Bivariate.GuruswamiSudan.Core
public import CompPolyBench.Bivariate.GuruswamiSudan.ReceivedWord

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for dense and Lee-O'Sullivan interpolation,
Roth-Ruckenstein and Alekhnovich root finding, packed distance filtering, and
backend-parametric `gsCore` and `gsFilteredCore`.
-/

public section

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
  let row <- runTimedSpec
    { name := "guruswami-sudan-interp-system", representation := "DenseMatrix",
      method := "Interpolation system construction", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup measured (fun _ ↦ interpolationMatrix points gsSmallParams)
    (checksumDenseMatrix checksumKoalaBear)
  let fastRow <- runTimedSpec
    { name := "guruswami-sudan-interp-system-fast", representation := "DenseMatrix",
      method := "Interpolation system construction", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastMeasured (fun _ ↦ interpolationMatrix fastPoints gsSmallParams)
    (checksumDenseMatrix checksumKoalaBearFast)
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
  let row <- runTimedSpec
    { name := "guruswami-sudan-interp-solve-copying", representation := "DenseMatrix",
      method := "Homogeneous interpolation solve, copying", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup measured (fun _ ↦ DenseMatrix.homogeneousWitness matrix)
    (checksumOptionArray checksumKoalaBear)
  let inPlaceRow <- runTimedSpec
    { name := "guruswami-sudan-interp-solve", representation := "DenseMatrix",
      method := "Homogeneous interpolation solve, in-place", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup inPlaceMeasured (fun _ ↦ DenseMatrix.homogeneousWitnessInPlace matrix)
    (checksumOptionArray checksumKoalaBear)
  let fastRow <- runTimedSpec
    { name := "guruswami-sudan-interp-solve-copying-fast", representation := "DenseMatrix",
      method := "Homogeneous interpolation solve, copying", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastMeasured (fun _ ↦ DenseMatrix.homogeneousWitness fastMatrix)
    (checksumOptionArray checksumKoalaBearFast)
  let fastInPlaceRow <- runTimedSpec
    { name := "guruswami-sudan-interp-solve-inplace-fast", representation := "DenseMatrix",
      method := "Homogeneous interpolation solve, in-place", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastInPlaceMeasured (fun _ ↦ DenseMatrix.homogeneousWitnessInPlace fastMatrix)
    (checksumOptionArray checksumKoalaBearFast)
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
  let approximantMeasured := preset.selectNat 60 9 2
  let hybridMeasured := preset.selectNat 90 13 3
  let fastApproximantMeasured := preset.selectNat 300 45 10
  let fastHybridMeasured := preset.selectNat 400 60 10
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured,
    approximantMeasured, hybridMeasured,
    fastApproximantMeasured, fastHybridMeasured
  ]
  let denseRow <- runTimedSpec
    { name := "guruswami-sudan-interp-dense-small", representation := "CBivariate",
      method := "Dense linear", field := "KoalaBear.Field", inputShape := gsSmallInterpInputShape,
      digestIterations := checksumIterations }
    preset warmup denseMeasured
    (fun _ ↦ koalaBearDenseInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
  let leeDirectRow <- runTimedSpec
    { name := "guruswami-sudan-interp-lee-direct-small", representation := "CBivariate",
      method := "Lee-O'Sullivan direct", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup leeDirectMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
  let leeSubproductRow <- runTimedSpec
    { name := "guruswami-sudan-interp-lee-subproduct-small", representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup leeSubproductMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
  let fastDenseRow <- runTimedSpec
    { name := "guruswami-sudan-interp-dense-small-fast", representation := "CBivariate",
      method := "Dense linear", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastDenseMeasured
    (fun _ ↦ fastKoalaBearDenseInterpContext.interpolate fastPoints gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
  let fastLeeDirectRow <- runTimedSpec
    { name := "guruswami-sudan-interp-lee-direct-small-fast", representation := "CBivariate",
      method := "Lee-O'Sullivan direct", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastLeeDirectMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
  let fastLeeSubproductRow <- runTimedSpec
    { name := "guruswami-sudan-interp-lee-subproduct-small-fast", representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastLeeSubproductMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
  let approximantRow <- runTimedSpec
    { name := "guruswami-sudan-interp-approximant-small", representation := "CBivariate",
      method := "Approximant basis (PM-Basis)", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup approximantMeasured
    (fun _ ↦ koalaBearApproximantBasisSubproductInterpContext.interpolate points
      gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
  let hybridRow <- runTimedSpec
    { name := "guruswami-sudan-interp-hybrid-small", representation := "CBivariate",
      method := "Hybrid (budgeted Lee-O'Sullivan with approximant fallback)",
      field := "KoalaBear.Field", inputShape := gsSmallInterpInputShape,
      digestIterations := checksumIterations }
    preset warmup hybridMeasured
    (fun _ ↦ koalaBearHybridInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
  let fastApproximantRow <- runTimedSpec
    { name := "guruswami-sudan-interp-approximant-small-fast", representation := "CBivariate",
      method := "Approximant basis (PM-Basis)", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastApproximantMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisSubproductInterpContext.interpolate
      fastPoints gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
  let fastHybridRow <- runTimedSpec
    { name := "guruswami-sudan-interp-hybrid-small-fast", representation := "CBivariate",
      method := "Hybrid (budgeted Lee-O'Sullivan with approximant fallback)",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallInterpInputShape,
      digestIterations := checksumIterations }
    preset warmup fastHybridMeasured
    (fun _ ↦ fastKoalaBearHybridInterpContext.interpolate fastPoints gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
  pure ({
    groupKey := "guruswami-sudan-interp-small-koalabear",
    title := "Guruswami-Sudan interpolation, small (KoalaBear)",
    records := #[
      denseRow, leeDirectRow, leeSubproductRow,
      fastDenseRow, fastLeeDirectRow, fastLeeSubproductRow,
      approximantRow, hybridRow, fastApproximantRow, fastHybridRow
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
  let row <- runTimedSpec
    { name := "guruswami-sudan-root-roth", representation := "CBivariate",
      method := "Roth-Ruckenstein root finding with nonlinear field-root equations",
      field := "KoalaBear.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup measured (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFieldRoots Q gsMessageDegree)
    checksumPolynomialArrayKoala
  let nttFastRow <- runTimedSpec
    { name := "guruswami-sudan-root-roth-nttfast", representation := "CBivariate",
      method := "Roth-Ruckenstein root finding with NTTFast field-root equations",
      field := "KoalaBear.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup nttFastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFieldRootsFast Q gsMessageDegree)
    checksumPolynomialArrayKoala
  let fastRow <- runTimedSpec
    { name := "guruswami-sudan-root-roth-fast", representation := "CBivariate",
      method := "Roth-Ruckenstein root finding with nonlinear field-root equations",
      field := "KoalaBear.Fast.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup fastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFastFieldRoots fastQ gsMessageDegree)
    checksumPolynomialArrayKoalaFast
  let fastNttFastRow <- runTimedSpec
    { name := "guruswami-sudan-root-roth-fast-nttfast", representation := "CBivariate",
      method := "Roth-Ruckenstein root finding with NTTFast field-root equations",
      field := "KoalaBear.Fast.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup fastNttFastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFastFieldRootsFast fastQ
      gsMessageDegree)
    checksumPolynomialArrayKoalaFast
  let alekhnovichRow <- runTimedSpec
    { name := "guruswami-sudan-root-alekhnovich", representation := "CBivariate",
      method := "Alekhnovich root finding with nonlinear field-root equations",
      field := "KoalaBear.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup alekhnovichMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFieldRoots Q gsMessageDegree)
    checksumPolynomialArrayKoala
  let alekhnovichNttFastRow <- runTimedSpec
    { name := "guruswami-sudan-root-alekhnovich-nttfast", representation := "CBivariate",
      method := "Alekhnovich root finding with NTTFast field-root equations",
      field := "KoalaBear.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup alekhnovichNttFastMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFieldRootsFast Q gsMessageDegree)
    checksumPolynomialArrayKoala
  let alekhnovichFastRow <- runTimedSpec
    { name := "guruswami-sudan-root-alekhnovich-fast", representation := "CBivariate",
      method := "Alekhnovich root finding with nonlinear field-root equations",
      field := "KoalaBear.Fast.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup alekhnovichFastMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFastFieldRoots fastQ gsMessageDegree)
    checksumPolynomialArrayKoalaFast
  let alekhnovichFastNttFastRow <- runTimedSpec
    { name := "guruswami-sudan-root-alekhnovich-fast-nttfast", representation := "CBivariate",
      method := "Alekhnovich root finding with NTTFast field-root equations",
      field := "KoalaBear.Fast.Field", inputShape := gsRootShape,
      digestIterations := checksumIterations }
    preset warmup alekhnovichFastNttFastMeasured
    (fun _ ↦ alekhnovichRootsYDegreeLt koalaFastFieldRootsFast fastQ
      gsMessageDegree)
    checksumPolynomialArrayKoalaFast
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
  let row <- runTimedSpec
    { name := "guruswami-sudan-packed-filter", representation := "CPolynomial",
      method := "Packed distance filtering", field := "KoalaBear.Field", inputShape := inputShape,
      digestIterations := checksumIterations }
    preset warmup measured (fun _ ↦ candidates.filter (passesCandidateDistance points radius))
    checksumPolynomialArrayKoala
  let fastRow <- runTimedSpec
    { name := "guruswami-sudan-packed-filter-fast", representation := "CPolynomial",
      method := "Packed distance filtering", field := "KoalaBear.Fast.Field",
      inputShape := inputShape, digestIterations := checksumIterations }
    preset warmup fastMeasured
    (fun _ ↦ fastCandidates.filter (passesCandidateDistance fastPoints radius))
    checksumPolynomialArrayKoalaFast
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
