/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Core Benchmarks

Full backend-parametric `gsCore` and `gsFilteredCore` benchmark runners.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

def runGsCoreSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsSmallBenchmarkPoints message
  let fastPoints := gsSmallBenchmarkPoints fastMessage
  let alekRootContext :=
    alekhnovichRootContext KoalaBear.Field koalaBearFieldRootContext
  let fastAlekRootContext :=
    alekhnovichRootContext KoalaBear.Fast.Field fastKoalaBearFieldRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 100 15 3
  let leeSubproductMeasured := preset.selectNat 90 13 3
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 600 90 20
  let fastLeeSubproductMeasured := preset.selectNat 400 60 10
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
    "guruswami-sudan-core-dense-small" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup denseMeasured
    (fun _ ↦ gsCore points koalaBearDenseInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-core-dense-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekDenseMeasured
    (fun _ ↦ gsCore points koalaBearDenseInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup leeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekLeeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup leeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekLeeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-core-dense-small-fast" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastDenseMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-core-dense-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastAlekDenseMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearDenseInterpContext fastAlekRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastLeeDirectMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastKoalaBearRothRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastAlekLeeDirectMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastAlekRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastKoalaBearRothRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastAlekLeeSubproductMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastAlekRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-small-koalabear",
    title := "Guruswami-Sudan full core, small (KoalaBear)",
    records := #[
      denseRow, denseAlekRow, leeDirectRow, leeDirectAlekRow,
      leeSubproductRow, leeSubproductAlekRow,
      fastDenseRow, fastDenseAlekRow, fastLeeDirectRow,
      fastLeeDirectAlekRow, fastLeeSubproductRow, fastLeeSubproductAlekRow
    ]
  }, gen)

def runGsFilteredCoreSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsSmallBenchmarkPoints message
  let fastPoints := gsSmallBenchmarkPoints fastMessage
  let alekRootContext :=
    alekhnovichRootContext KoalaBear.Field koalaBearFieldRootContext
  let fastAlekRootContext :=
    alekhnovichRootContext KoalaBear.Fast.Field fastKoalaBearFieldRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 100 15 3
  let leeSubproductMeasured := preset.selectNat 90 13 3
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 600 90 20
  let fastLeeSubproductMeasured := preset.selectNat 400 60 10
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
    "guruswami-sudan-filtered-core-dense-small" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup denseMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekDenseMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearDenseInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup leeDirectMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup leeSubproductMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-fast" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastAlekDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearDenseInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastAlekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup
    fastAlekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-small-koalabear",
    title := "Guruswami-Sudan filtered core, small (KoalaBear)",
    records := #[
      denseRow, denseAlekRow, leeDirectRow, leeDirectAlekRow,
      leeSubproductRow, leeSubproductAlekRow,
      fastDenseRow, fastDenseAlekRow, fastLeeDirectRow,
      fastLeeDirectAlekRow, fastLeeSubproductRow, fastLeeSubproductAlekRow
    ]
  }, gen)

end CompPolyBench
