/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Perturbed Received-Word Benchmarks

Perturbed (non-codeword) counterparts of the small interpolation,
root-backend core, and filtered-core benchmark groups.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

/-! ### Perturbation shape -/

private def gsNonCodewordSmallPeriod : Nat := 3

private def gsNonCodewordSmallErrors : Nat :=
  (gsSmallPointCount + gsNonCodewordSmallPeriod - 1) / gsNonCodewordSmallPeriod

private def gsNonCodewordSmallInputShape : String :=
  gsSmallInterpInputShape ++ s!",errors=every{gsNonCodewordSmallPeriod}"

private def gsNonCodewordSmallFilteredShape : String :=
  gsNonCodewordSmallInputShape ++ s!",r={gsNonCodewordSmallErrors}"

private def perturbEveryNthY {F : Type*} [Add F] [OfNat F 1]
    (period : Nat) (points : Array (Prod F F)) : Array (Prod F F) :=
  if period == 0 then
    points
  else
    points.zipIdx.map fun pair ↦
      let point := pair.1
      let idx := pair.2
      if idx % period == 0 then
        (point.1, point.2 + 1)
      else
        point

/-! ### Shared inputs -/

private structure PerturbedSmallInputs where
  points : Array (Prod KoalaBear.Field KoalaBear.Field)
  fastPoints : Array (Prod KoalaBear.Fast.Field KoalaBear.Fast.Field)

private def perturbedSmallInputs (gen : StdGen) : PerturbedSmallInputs × StdGen :=
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := perturbEveryNthY gsNonCodewordSmallPeriod
    (codewordPointsWithCount gsSmallPointCount message)
  let fastPoints := perturbEveryNthY gsNonCodewordSmallPeriod
    (codewordPointsWithCount gsSmallPointCount fastMessage)
  ({ points := points, fastPoints := fastPoints }, gen)

/-! ### Group metadata -/

/-- Benchmark group metadata for perturbed received-word rows. -/
def guruswamiSudanReceivedWordGroupInfos : List BenchGroupInfo := [
  ⟨"guruswami-sudan-interp-noncodeword-small-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-noncodeword-small-koalabear",
    "Guruswami-Sudan full core on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear",
    "Guruswami-Sudan filtered core on perturbed received word, small (KoalaBear)"⟩
]

/-! ### Group runners -/

private def runGsInterpolationNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 15 2 1
  let leeSubproductMeasured := preset.selectNat 15 2 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 80 11 2
  let fastLeeSubproductMeasured := preset.selectNat 70 10 2
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-interp-dense-noncodeword-small" "CBivariate"
    "Dense linear"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup denseMeasured
    (fun _ ↦ koalaBearDenseInterpContext.interpolate inputs.points gsSmallParams)
    (checksumInterpolationValidityOption inputs.points gsSmallParams)
    checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup leeDirectMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate inputs.points gsSmallParams)
    (checksumInterpolationValidityOption inputs.points gsSmallParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup leeSubproductMeasured
    (fun _ ↦
      koalaBearLeeSubproductInterpContext.interpolate inputs.points gsSmallParams)
    (checksumInterpolationValidityOption inputs.points gsSmallParams)
    checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-interp-dense-noncodeword-small-fast" "CBivariate"
    "Dense linear"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastDenseMeasured
    (fun _ ↦ fastKoalaBearDenseInterpContext.interpolate inputs.fastPoints gsSmallParams)
    (checksumInterpolationValidityOption inputs.fastPoints gsSmallParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastLeeDirectMeasured
    (fun _ ↦
      fastKoalaBearLeeDirectInterpContext.interpolate inputs.fastPoints
        gsSmallParams)
    (checksumInterpolationValidityOption inputs.fastPoints gsSmallParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastLeeSubproductMeasured
    (fun _ ↦
      fastKoalaBearLeeSubproductInterpContext.interpolate inputs.fastPoints
        gsSmallParams)
    (checksumInterpolationValidityOption inputs.fastPoints gsSmallParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-noncodeword-small-koalabear",
    title := "Guruswami-Sudan interpolation on perturbed received word, small (KoalaBear)",
    records := #[
      denseRow, leeDirectRow, leeSubproductRow,
      fastDenseRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsCoreNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let alekRootContext :=
    alekhnovichRootContext KoalaBear.Field koalaBearFieldRootContext
  let fastAlekRootContext :=
    alekhnovichRootContext KoalaBear.Fast.Field fastKoalaBearFieldRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 15 2 1
  let leeSubproductMeasured := preset.selectNat 15 2 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 80 11 2
  let fastLeeSubproductMeasured := preset.selectNat 70 10 2
  let alekDenseMeasured := denseMeasured
  let alekLeeDirectMeasured := leeDirectMeasured
  let alekLeeSubproductMeasured := leeSubproductMeasured
  let fastAlekDenseMeasured := fastDenseMeasured
  let fastAlekLeeDirectMeasured := fastLeeDirectMeasured
  let fastAlekLeeSubproductMeasured := fastLeeSubproductMeasured
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured, alekDenseMeasured,
    alekLeeDirectMeasured, alekLeeSubproductMeasured, fastAlekDenseMeasured,
    fastAlekLeeDirectMeasured, fastAlekLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-core-dense-noncodeword-small" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup denseMeasured
    (fun _ ↦
      (gsCore inputs.points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-core-dense-noncodeword-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup alekDenseMeasured
    (fun _ ↦
      (gsCore inputs.points koalaBearDenseInterpContext alekRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup leeDirectMeasured
    (fun _ ↦
      (gsCore inputs.points koalaBearLeeDirectInterpContext koalaBearRothRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-noncodeword-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup alekLeeDirectMeasured
    (fun _ ↦
      (gsCore inputs.points koalaBearLeeDirectInterpContext alekRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup leeSubproductMeasured
    (fun _ ↦
      (gsCore inputs.points koalaBearLeeSubproductInterpContext koalaBearRothRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-noncodeword-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup alekLeeSubproductMeasured
    (fun _ ↦
      (gsCore inputs.points koalaBearLeeSubproductInterpContext alekRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-core-dense-noncodeword-small-fast" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup fastDenseMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-core-dense-noncodeword-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastAlekDenseMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearDenseInterpContext
        fastAlekRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastLeeDirectMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearLeeDirectInterpContext
        fastKoalaBearRothRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-noncodeword-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastAlekLeeDirectMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearLeeDirectInterpContext
        fastAlekRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastLeeSubproductMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearLeeSubproductInterpContext
        fastKoalaBearRothRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-noncodeword-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup
    fastAlekLeeSubproductMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearLeeSubproductInterpContext
        fastAlekRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-noncodeword-small-koalabear",
    title := "Guruswami-Sudan full core on perturbed received word, small (KoalaBear)",
    records := #[
      denseRow, denseAlekRow, leeDirectRow, leeDirectAlekRow,
      leeSubproductRow, leeSubproductAlekRow,
      fastDenseRow, fastDenseAlekRow, fastLeeDirectRow,
      fastLeeDirectAlekRow, fastLeeSubproductRow, fastLeeSubproductAlekRow
    ]
  }, gen)

private def runGsFilteredCoreNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let alekRootContext :=
    alekhnovichRootContext KoalaBear.Field koalaBearFieldRootContext
  let fastAlekRootContext :=
    alekhnovichRootContext KoalaBear.Fast.Field fastKoalaBearFieldRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 15 2 1
  let leeSubproductMeasured := preset.selectNat 15 2 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 80 11 2
  let fastLeeSubproductMeasured := preset.selectNat 70 10 2
  let alekDenseMeasured := denseMeasured
  let alekLeeDirectMeasured := leeDirectMeasured
  let alekLeeSubproductMeasured := leeSubproductMeasured
  let fastAlekDenseMeasured := fastDenseMeasured
  let fastAlekLeeDirectMeasured := fastLeeDirectMeasured
  let fastAlekLeeSubproductMeasured := fastLeeSubproductMeasured
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured, alekDenseMeasured,
    alekLeeDirectMeasured, alekLeeSubproductMeasured, fastAlekDenseMeasured,
    fastAlekLeeDirectMeasured, fastAlekLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-noncodeword-small" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup denseMeasured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-noncodeword-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup alekDenseMeasured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearDenseInterpContext alekRootContext
        gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup leeDirectMeasured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearLeeDirectInterpContext
        koalaBearRothRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-noncodeword-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup alekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearLeeDirectInterpContext alekRootContext
        gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup leeSubproductMeasured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearLeeSubproductInterpContext
        koalaBearRothRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup
    alekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearLeeSubproductInterpContext alekRootContext
        gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-noncodeword-small-fast" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup
    fastDenseMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-noncodeword-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup
    fastAlekDenseMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearDenseInterpContext
        fastAlekRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup
    fastLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearLeeDirectInterpContext
        fastKoalaBearRothRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-noncodeword-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup
    fastAlekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearLeeDirectInterpContext
        fastAlekRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup
    fastLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearLeeSubproductInterpContext
        fastKoalaBearRothRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup
    fastAlekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearLeeSubproductInterpContext
        fastAlekRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-noncodeword-small-koalabear",
    title := "Guruswami-Sudan filtered core on perturbed received word, small (KoalaBear)",
    records := #[
      denseRow, denseAlekRow, leeDirectRow, leeDirectAlekRow,
      leeSubproductRow, leeSubproductAlekRow,
      fastDenseRow, fastDenseAlekRow, fastLeeDirectRow,
      fastLeeDirectAlekRow, fastLeeSubproductRow, fastLeeSubproductAlekRow
    ]
  }, gen)

/-- Runnable received-word GS benchmark tasks. -/
def guruswamiSudanReceivedWordTasks : List BenchTask := [
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 0
    ⟨"guruswami-sudan-interp-noncodeword-small-koalabear", ""⟩)
    runGsInterpolationNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 1
    ⟨"guruswami-sudan-core-noncodeword-small-koalabear", ""⟩)
    runGsCoreNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 2
    ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear", ""⟩)
    runGsFilteredCoreNonCodewordSmallKoala
]

end CompPolyBench
