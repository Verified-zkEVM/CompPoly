/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Core
import CompPolyBench.Bivariate.GuruswamiSudan.ReceivedWord

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for the dense interpolation path,
Koetter interpolation path, Roth-Ruckenstein and Alekhnovich root finding, and
full backend-parametric `gsCore` and `gsFilteredCore`.
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
  let kernelContext := denseLinearKernelContext KoalaBear.Field
  let fastKernelContext := denseLinearKernelContext KoalaBear.Fast.Field
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-solve" "DenseMatrix" "Homogeneous interpolation solve"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup measured
    (fun _ ↦ kernelContext.homogeneousWitness matrix)
    (checksumOptionArray checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-solve-fast" "DenseMatrix"
    "Homogeneous interpolation solve"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastMeasured
    (fun _ ↦ fastKernelContext.homogeneousWitness fastMatrix)
    (checksumOptionArray checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-solve-small-koalabear",
    title := "Guruswami-Sudan dense interpolation solving, small (KoalaBear)",
    records := #[row, fastRow]
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
  let koetterMeasured := preset.selectNat 10 2 1
  let leeDirectMeasured := preset.selectNat 60 8 2
  let leeSubproductMeasured := preset.selectNat 50 7 1
  let approximantDirectMeasured := preset.selectNat 30 5 1
  let approximantSubproductMeasured := preset.selectNat 1 1 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastKoetterMeasured := preset.selectNat 70 10 2
  let fastLeeDirectMeasured := preset.selectNat 400 60 10
  let fastLeeSubproductMeasured := preset.selectNat 300 40 10
  let fastApproximantDirectMeasured := preset.selectNat 200 30 5
  let fastApproximantSubproductMeasured := preset.selectNat 1 1 1
  let checksumIterations := groupChecksumIterations denseMeasured [
    koetterMeasured, leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    approximantDirectMeasured, approximantSubproductMeasured, fastKoetterMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured, fastApproximantDirectMeasured,
    fastApproximantSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-interp-dense-small" "CBivariate"
    "Dense linear"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup denseMeasured
    (fun _ ↦ denseInterpolate points gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
    checksumIterations
  let koetterRow <- runTimed
    "guruswami-sudan-interp-koetter-small" "CBivariate"
    "Koetter"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup koetterMeasured
    (fun _ ↦ koetterInterpolate points gsSmallParams)
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
  let approximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-small" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup approximantDirectMeasured
    (fun _ ↦ koalaBearApproximantBasisDirectInterpContext.interpolate points
      gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
    checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-small" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup approximantSubproductMeasured
    (fun _ ↦ koalaBearApproximantBasisSubproductInterpContext.interpolate points
      gsSmallParams)
    (checksumInterpolationValidityOption points gsSmallParams)
    checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-interp-dense-small-fast" "CBivariate"
    "Dense linear"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastDenseMeasured
    (fun _ ↦ denseInterpolate fastPoints gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-interp-koetter-small-fast" "CBivariate"
    "Koetter"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastKoetterMeasured
    (fun _ ↦ koetterInterpolate fastPoints gsSmallParams)
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
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-small-fast" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastApproximantDirectMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisDirectInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-small-fast" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisSubproductInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationValidityOption fastPoints gsSmallParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-small-koalabear",
    title := "Guruswami-Sudan interpolation, small (KoalaBear)",
    records := #[
      denseRow, koetterRow, leeDirectRow, leeSubproductRow,
      approximantDirectRow, approximantSubproductRow,
      fastDenseRow, fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow,
      fastApproximantDirectRow, fastApproximantSubproductRow
    ]
  }, gen)

private def runGsInterpolationLargeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsLargeInterpMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsLargeBenchmarkPoints message
  let fastPoints := gsLargeBenchmarkPoints fastMessage
  let warmup := gsWarmupIterations preset
  let koetterMeasured := preset.selectNat 1 1 1
  let leeMeasured := preset.selectNat 1 1 1
  let approximantDirectMeasured := preset.selectNat 1 1 1
  let approximantSubproductMeasured := preset.selectNat 1 1 1
  let fastKoetterMeasured := preset.selectNat 1 1 1
  let fastLeeMeasured := preset.selectNat 1 1 1
  let fastApproximantDirectMeasured := preset.selectNat 1 1 1
  let fastApproximantSubproductMeasured := preset.selectNat 1 1 1
  let checksumIterations := groupChecksumIterations koetterMeasured [
    leeMeasured, leeMeasured, approximantDirectMeasured, approximantSubproductMeasured,
    fastKoetterMeasured, fastLeeMeasured, fastLeeMeasured,
    fastApproximantDirectMeasured, fastApproximantSubproductMeasured
  ]
  let koetterRow <- runTimed
    "guruswami-sudan-interp-koetter" "CBivariate"
    "Koetter"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup koetterMeasured
    (fun _ ↦ koetterInterpolate points gsLargeInterpParams)
    (checksumInterpolationValidityOption points gsLargeInterpParams)
    checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup leeMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsLargeInterpParams)
    (checksumInterpolationValidityOption points gsLargeInterpParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup leeMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsLargeInterpParams)
    (checksumInterpolationValidityOption points gsLargeInterpParams)
    checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup approximantDirectMeasured
    (fun _ ↦ koalaBearApproximantBasisDirectInterpContext.interpolate points
      gsLargeInterpParams)
    (checksumInterpolationValidityOption points gsLargeInterpParams)
    checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup approximantSubproductMeasured
    (fun _ ↦ koalaBearApproximantBasisSubproductInterpContext.interpolate points
      gsLargeInterpParams)
    (checksumInterpolationValidityOption points gsLargeInterpParams)
    checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-interp-koetter-fast" "CBivariate"
    "Koetter"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup fastKoetterMeasured
    (fun _ ↦ koetterInterpolate fastPoints gsLargeInterpParams)
    (checksumInterpolationValidityOption fastPoints gsLargeInterpParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup fastLeeMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints
      gsLargeInterpParams)
    (checksumInterpolationValidityOption fastPoints gsLargeInterpParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup fastLeeMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsLargeInterpParams)
    (checksumInterpolationValidityOption fastPoints gsLargeInterpParams)
    checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-fast" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup
    fastApproximantDirectMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisDirectInterpContext.interpolate fastPoints
      gsLargeInterpParams)
    (checksumInterpolationValidityOption fastPoints gsLargeInterpParams)
    checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-fast" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisSubproductInterpContext.interpolate fastPoints
      gsLargeInterpParams)
    (checksumInterpolationValidityOption fastPoints gsLargeInterpParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-large-koalabear",
    title := "Guruswami-Sudan interpolation, large (KoalaBear)",
    records := #[
      koetterRow, leeDirectRow, leeSubproductRow,
      approximantDirectRow, approximantSubproductRow,
      fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow,
      fastApproximantDirectRow, fastApproximantSubproductRow
    ]
  }, gen)

private def runGsLeeSetupLargeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsLargeInterpMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsLargeBenchmarkPoints message
  let fastPoints := gsLargeBenchmarkPoints fastMessage
  let directV : CPolynomial.VanishingPolynomialContext KoalaBear.Field :=
    CPolynomial.VanishingPolynomialContext.direct
  let subproductV : CPolynomial.VanishingPolynomialContext KoalaBear.Field :=
    CPolynomial.VanishingPolynomialContext.subproduct koalaBearNttFastMulContext
  let hornerE : CPolynomial.BatchEvalContext KoalaBear.Field :=
    CPolynomial.BatchEvalContext.horner KoalaBear.Field
  let subproductE : CPolynomial.BatchEvalContext KoalaBear.Field :=
    koalaBearNttFastBatchEvalContext
  let fastDirectV : CPolynomial.VanishingPolynomialContext KoalaBear.Fast.Field :=
    CPolynomial.VanishingPolynomialContext.direct
  let fastSubproductV : CPolynomial.VanishingPolynomialContext KoalaBear.Fast.Field :=
    CPolynomial.VanishingPolynomialContext.subproduct fastKoalaBearNttFastMulContext
  let fastHornerE : CPolynomial.BatchEvalContext KoalaBear.Fast.Field :=
    CPolynomial.BatchEvalContext.horner KoalaBear.Fast.Field
  let fastSubproductE : CPolynomial.BatchEvalContext KoalaBear.Fast.Field :=
    fastKoalaBearNttFastBatchEvalContext
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 5 1 1
  let fastMeasured := preset.selectNat 25 4 1
  let checksumIterations := groupChecksumIterations measured [
    measured, fastMeasured, fastMeasured
  ]
  let directRow <- runTimed
    "guruswami-sudan-lee-setup-direct" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (direct vanishing)"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup measured
    (fun _ ↦ leeOSullivanBasisRows directV hornerE points gsLargeInterpParams)
    (checksumPolynomialMatrix checksumKoalaBear) checksumIterations
  let subproductRow <- runTimed
    "guruswami-sudan-lee-setup-subproduct" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (subproduct vanishing)"
    "KoalaBear.Field" gsLargeInterpInputShape preset warmup measured
    (fun _ ↦ leeOSullivanBasisRows subproductV subproductE points gsLargeInterpParams)
    (checksumPolynomialMatrix checksumKoalaBear) checksumIterations
  let fastDirectRow <- runTimed
    "guruswami-sudan-lee-setup-direct-fast" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (direct vanishing)"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup fastMeasured
    (fun _ ↦ leeOSullivanBasisRows fastDirectV fastHornerE fastPoints
      gsLargeInterpParams)
    (checksumPolynomialMatrix checksumKoalaBearFast) checksumIterations
  let fastSubproductRow <- runTimed
    "guruswami-sudan-lee-setup-subproduct-fast" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (subproduct vanishing)"
    "KoalaBear.Fast.Field" gsLargeInterpInputShape preset warmup fastMeasured
    (fun _ ↦ leeOSullivanBasisRows fastSubproductV fastSubproductE fastPoints
      gsLargeInterpParams)
    (checksumPolynomialMatrix checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-lee-setup-large-koalabear",
    title := "Guruswami-Sudan Lee-O'Sullivan setup, large (KoalaBear)",
    records := #[directRow, subproductRow, fastDirectRow, fastSubproductRow]
  }, gen)

private def runGsHasseKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let Q := multiplicityBenchmarkQ message
  let fastQ := multiplicityBenchmarkQ fastMessage
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 80 10 2
  let fastMeasured := preset.selectNat 500 70 15
  let checksumIterations := groupChecksumIterations measured [
    measured,
    measured,
    fastMeasured,
    fastMeasured,
    fastMeasured
  ]
  let row <- runTimed
    "guruswami-sudan-hasse-check" "CBivariate" "Hasse multiplicity check"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ ↦ CBivariate.satisfiesMultiplicityConstraintsBool Q points gsCheckMultiplicity)
    checksumBool checksumIterations
  let genericRow <- runTimed
    "guruswami-sudan-hasse-check-generic" "CBivariate"
    "Generic multiplicity check"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ ↦ points.all fun point ↦
      CBivariate.checkMultiplicity Q gsCheckMultiplicity point.1 point.2)
    checksumBool checksumIterations
  let shiftOnceRow <- runTimed
    "guruswami-sudan-hasse-check-shift-once" "CBivariate"
    "Shift-once multiplicity check"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ ↦ points.all fun point ↦
      checkMultiplicityShiftOnce Q gsCheckMultiplicity point.1 point.2)
    checksumBool checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-hasse-check-fast" "CBivariate" "Hasse multiplicity check"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ ↦ CBivariate.satisfiesMultiplicityConstraintsBool fastQ fastPoints
      gsCheckMultiplicity)
    checksumBool checksumIterations
  let fastGenericRow <- runTimed
    "guruswami-sudan-hasse-check-generic-fast" "CBivariate"
    "Generic multiplicity check"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ ↦ fastPoints.all fun point ↦
      CBivariate.checkMultiplicity fastQ gsCheckMultiplicity point.1 point.2)
    checksumBool checksumIterations
  let fastShiftOnceRow <- runTimed
    "guruswami-sudan-hasse-check-shift-once-fast" "CBivariate"
    "Shift-once multiplicity check"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ ↦ fastPoints.all fun point ↦
      checkMultiplicityShiftOnce fastQ gsCheckMultiplicity point.1 point.2)
    checksumBool checksumIterations
  pure ({
    groupKey := "guruswami-sudan-hasse-koalabear",
    title := "Guruswami-Sudan Hasse multiplicity checking (KoalaBear)",
    records := #[row, genericRow, shiftOnceRow, fastRow, fastGenericRow, fastShiftOnceRow]
  }, gen)

private def runGsComposeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let Q := multiplicityBenchmarkQ message
  let fastQ := multiplicityBenchmarkQ fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 80 10 2
  let fastMeasured := preset.selectNat 500 70 15
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-compose-y" "CPolynomial" "Composition in Y"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ ↦ CBivariate.composeY Q message)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-compose-y-fast" "CPolynomial" "Composition in Y"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ ↦ CBivariate.composeY fastQ fastMessage)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-compose-koalabear",
    title := "Guruswami-Sudan composition in Y (KoalaBear)",
    records := #[row, fastRow]
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
    records := #[row, nttFastRow, fastRow, fastNttFastRow, alekhnovichRow,
      alekhnovichNttFastRow, alekhnovichFastRow, alekhnovichFastNttFastRow]
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
    ⟨"guruswami-sudan-interp-large-koalabear", ""⟩) runGsInterpolationLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 4
    ⟨"guruswami-sudan-lee-setup-large-koalabear", ""⟩) runGsLeeSetupLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 5
    ⟨"guruswami-sudan-hasse-koalabear", ""⟩) runGsHasseKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 6
    ⟨"guruswami-sudan-compose-koalabear", ""⟩) runGsComposeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 7
    ⟨"guruswami-sudan-root-koalabear", ""⟩) runGsRootKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 8
    ⟨"guruswami-sudan-core-small-koalabear", ""⟩) runGsCoreSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 9
    ⟨"guruswami-sudan-core-large-koalabear", ""⟩) runGsCoreLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 10
    ⟨"guruswami-sudan-packed-filter-koalabear", ""⟩) runGsPackedFilterKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 11
    ⟨"guruswami-sudan-filtered-core-small-koalabear", ""⟩) runGsFilteredCoreSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 12
    ⟨"guruswami-sudan-filtered-core-large-koalabear", ""⟩) runGsFilteredCoreLargeKoala
] ++ guruswamiSudanReceivedWordTasks

end CompPolyBench
