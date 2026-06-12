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
  let rothRootContext := koalaBearRothRootContext
  let fastRothRootContext := fastKoalaBearRothRootContext
  let alekRootContext := koalaBearAlekhnovichRootContext
  let fastAlekRootContext := fastKoalaBearAlekhnovichRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 100 15 3
  let leeSubproductMeasured := preset.selectNat 90 13 3
  let approximantDirectMeasured := preset.selectNat 7 1 1
  let approximantSubproductMeasured := preset.selectNat 7 1 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 600 90 20
  let fastLeeSubproductMeasured := preset.selectNat 400 60 10
  let fastApproximantDirectMeasured := preset.selectNat 20 3 1
  let fastApproximantSubproductMeasured := preset.selectNat 20 3 1
  let alekDenseMeasured := denseMeasured
  let alekLeeDirectMeasured := leeDirectMeasured
  let alekLeeSubproductMeasured := leeSubproductMeasured
  let alekApproximantDirectMeasured := approximantDirectMeasured
  let alekApproximantSubproductMeasured := approximantSubproductMeasured
  let fastAlekDenseMeasured := fastDenseMeasured
  let fastAlekLeeDirectMeasured := fastLeeDirectMeasured
  let fastAlekLeeSubproductMeasured := fastLeeSubproductMeasured
  let fastAlekApproximantDirectMeasured := fastApproximantDirectMeasured
  let fastAlekApproximantSubproductMeasured := fastApproximantSubproductMeasured
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    approximantDirectMeasured, approximantSubproductMeasured, fastLeeDirectMeasured,
    fastLeeSubproductMeasured, fastApproximantDirectMeasured,
    fastApproximantSubproductMeasured, alekDenseMeasured, alekLeeDirectMeasured,
    alekLeeSubproductMeasured, alekApproximantDirectMeasured,
    alekApproximantSubproductMeasured, fastAlekDenseMeasured, fastAlekLeeDirectMeasured,
    fastAlekLeeSubproductMeasured,
    fastAlekApproximantDirectMeasured, fastAlekApproximantSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-core-dense-small" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup denseMeasured
    (fun _ ↦ gsCore points (denseInterpContext KoalaBear.Field) rothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-core-dense-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekDenseMeasured
    (fun _ ↦ gsCore points (denseInterpContext KoalaBear.Field) alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup leeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext rothRootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekLeeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext alekRootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup leeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext rothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekLeeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-core-approximant-direct-small" "CBivariate"
    "Approximant basis direct + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup approximantDirectMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisDirectInterpContext
      rothRootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectAlekRow <- runTimed
    "guruswami-sudan-core-approximant-direct-small-alekhnovich" "CBivariate"
    "Approximant basis direct + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup alekApproximantDirectMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisDirectInterpContext
      alekRootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-small" "CBivariate"
    "Approximant basis subproduct + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup
    approximantSubproductMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisSubproductInterpContext
      rothRootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductAlekRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-small-alekhnovich" "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup
    alekApproximantSubproductMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisSubproductInterpContext
      alekRootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-core-dense-small-fast" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastDenseMeasured
    (fun _ ↦
      gsCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRothRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-core-dense-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastAlekDenseMeasured
    (fun _ ↦
      gsCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastAlekRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastLeeDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastAlekLeeDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastAlekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastAlekLeeSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearLeeSubproductInterpContext fastAlekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-core-approximant-direct-small-fast" "CBivariate"
    "Approximant basis direct + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastApproximantDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisDirectInterpContext
      fastRothRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectAlekRow <- runTimed
    "guruswami-sudan-core-approximant-direct-small-alekhnovich-fast" "CBivariate"
    "Approximant basis direct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastAlekApproximantDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisDirectInterpContext
      fastAlekRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-small-fast" "CBivariate"
    "Approximant basis subproduct + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisSubproductInterpContext
      fastRothRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductAlekRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-small-alekhnovich-fast" "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup
    fastAlekApproximantSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisSubproductInterpContext
      fastAlekRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-small-koalabear",
    title := "Guruswami-Sudan full core, small (KoalaBear)",
    records := #[
      denseRow, denseAlekRow, leeDirectRow,
      leeDirectAlekRow, leeSubproductRow, leeSubproductAlekRow, approximantDirectRow,
      approximantDirectAlekRow, approximantSubproductRow, approximantSubproductAlekRow,
      fastDenseRow, fastDenseAlekRow, fastLeeDirectRow, fastLeeDirectAlekRow, fastLeeSubproductRow,
      fastLeeSubproductAlekRow, fastApproximantDirectRow, fastApproximantDirectAlekRow,
      fastApproximantSubproductRow, fastApproximantSubproductAlekRow
    ]
  }, gen)

def runGsCoreMediumKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMediumInterpMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsMediumBenchmarkPoints message
  let fastPoints := gsMediumBenchmarkPoints fastMessage
  let rothRootContext := koalaBearRothRootContext
  let fastRothRootContext := fastKoalaBearRothRootContext
  let alekRootContext := koalaBearAlekhnovichRootContext
  let fastAlekRootContext := fastKoalaBearAlekhnovichRootContext
  let warmup := gsWarmupIterations preset
  let leeMeasured := preset.selectNat 10 1 1
  let approximantDirectMeasured := preset.selectNat 2 1 1
  let approximantSubproductMeasured := preset.selectNat 2 1 1
  let fastLeeMeasured := preset.selectNat 50 7 1
  let fastApproximantDirectMeasured := preset.selectNat 7 1 1
  let fastApproximantSubproductMeasured := preset.selectNat 7 1 1
  let alekLeeMeasured := leeMeasured
  let alekApproximantDirectMeasured := approximantDirectMeasured
  let alekApproximantSubproductMeasured := approximantSubproductMeasured
  let fastAlekLeeMeasured := fastLeeMeasured
  let fastAlekApproximantDirectMeasured := fastApproximantDirectMeasured
  let fastAlekApproximantSubproductMeasured := fastApproximantSubproductMeasured
  let checksumIterations := groupChecksumIterations leeMeasured [
    leeMeasured, leeMeasured, approximantDirectMeasured, approximantSubproductMeasured,
    fastLeeMeasured, fastLeeMeasured,
    fastApproximantDirectMeasured, fastApproximantSubproductMeasured,
    alekLeeMeasured, alekLeeMeasured, alekApproximantDirectMeasured,
    alekApproximantSubproductMeasured, fastAlekLeeMeasured,
    fastAlekLeeMeasured, fastAlekApproximantDirectMeasured,
    fastAlekApproximantSubproductMeasured
  ]
  let leeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-roth" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup leeMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext rothRootContext
      gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup alekLeeMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext alekRootContext
      gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-roth" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup leeMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext rothRootContext
      gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup alekLeeMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext alekRootContext
      gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-core-approximant-direct-roth" "CBivariate"
    "Approximant basis direct + RR roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup approximantDirectMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisDirectInterpContext
      rothRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectAlekRow <- runTimed
    "guruswami-sudan-core-approximant-direct-alekhnovich" "CBivariate"
    "Approximant basis direct + Alekhnovich roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup alekApproximantDirectMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisDirectInterpContext
      alekRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-roth" "CBivariate"
    "Approximant basis subproduct + RR roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup
    approximantSubproductMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisSubproductInterpContext
      rothRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductAlekRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-alekhnovich" "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots"
    "KoalaBear.Field" gsMediumInterpInputShape preset warmup
    alekApproximantSubproductMeasured
    (fun _ ↦ gsCore points koalaBearApproximantBasisSubproductInterpContext
      alekRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-roth-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastRothRootContext
        gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-core-lee-direct-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup fastAlekLeeMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastAlekRootContext
        gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-roth-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRothRootContext
        gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup fastAlekLeeMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext fastAlekRootContext
        gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-core-approximant-direct-roth-fast" "CBivariate"
    "Approximant basis direct + RR roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup
    fastApproximantDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisDirectInterpContext
      fastRothRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectAlekRow <- runTimed
    "guruswami-sudan-core-approximant-direct-alekhnovich-fast" "CBivariate"
    "Approximant basis direct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup
    fastAlekApproximantDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisDirectInterpContext
      fastAlekRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-roth-fast" "CBivariate"
    "Approximant basis subproduct + RR roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisSubproductInterpContext
      fastRothRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductAlekRow <- runTimed
    "guruswami-sudan-core-approximant-subproduct-alekhnovich-fast" "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsMediumInterpInputShape preset warmup
    fastAlekApproximantSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearApproximantBasisSubproductInterpContext
      fastAlekRootContext gsMediumInterpParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-medium-koalabear",
    title := "Guruswami-Sudan full core, medium (KoalaBear)",
    records := #[
      leeDirectRow, leeDirectAlekRow, leeSubproductRow,
      leeSubproductAlekRow, approximantDirectRow, approximantDirectAlekRow,
      approximantSubproductRow, approximantSubproductAlekRow, fastLeeDirectRow,
      fastLeeDirectAlekRow, fastLeeSubproductRow,
      fastLeeSubproductAlekRow, fastApproximantDirectRow, fastApproximantDirectAlekRow,
      fastApproximantSubproductRow, fastApproximantSubproductAlekRow
    ]
  }, gen)

def runGsFilteredCoreSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsSmallBenchmarkPoints message
  let fastPoints := gsSmallBenchmarkPoints fastMessage
  let rothRootContext := koalaBearRothRootContext
  let fastRothRootContext := fastKoalaBearRothRootContext
  let alekRootContext := koalaBearAlekhnovichRootContext
  let fastAlekRootContext := fastKoalaBearAlekhnovichRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let leeDirectMeasured := preset.selectNat 100 15 3
  let leeSubproductMeasured := preset.selectNat 90 13 3
  let approximantDirectMeasured := preset.selectNat 7 1 1
  let approximantSubproductMeasured := preset.selectNat 7 1 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastLeeDirectMeasured := preset.selectNat 600 90 20
  let fastLeeSubproductMeasured := preset.selectNat 400 60 10
  let fastApproximantDirectMeasured := preset.selectNat 20 3 1
  let fastApproximantSubproductMeasured := preset.selectNat 20 3 1
  let alekDenseMeasured := denseMeasured
  let alekLeeDirectMeasured := leeDirectMeasured
  let alekLeeSubproductMeasured := leeSubproductMeasured
  let alekApproximantDirectMeasured := approximantDirectMeasured
  let alekApproximantSubproductMeasured := approximantSubproductMeasured
  let fastAlekDenseMeasured := fastDenseMeasured
  let fastAlekLeeDirectMeasured := fastLeeDirectMeasured
  let fastAlekLeeSubproductMeasured := fastLeeSubproductMeasured
  let fastAlekApproximantDirectMeasured := fastApproximantDirectMeasured
  let fastAlekApproximantSubproductMeasured := fastApproximantSubproductMeasured
  let checksumIterations := groupChecksumIterations denseMeasured [
    leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    approximantDirectMeasured, approximantSubproductMeasured, fastLeeDirectMeasured,
    fastLeeSubproductMeasured, fastApproximantDirectMeasured,
    fastApproximantSubproductMeasured, alekDenseMeasured, alekLeeDirectMeasured,
    alekLeeSubproductMeasured, alekApproximantDirectMeasured,
    alekApproximantSubproductMeasured, fastAlekDenseMeasured, fastAlekLeeDirectMeasured,
    fastAlekLeeSubproductMeasured,
    fastAlekApproximantDirectMeasured, fastAlekApproximantSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup denseMeasured
    (fun _ ↦
      gsFilteredCore points (denseInterpContext KoalaBear.Field) rothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekDenseMeasured
    (fun _ ↦
      gsFilteredCore points (denseInterpContext KoalaBear.Field) alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup leeDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearLeeDirectInterpContext rothRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekLeeDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearLeeDirectInterpContext alekRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup leeSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearLeeSubproductInterpContext rothRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekLeeSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearLeeSubproductInterpContext alekRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-small" "CBivariate"
    "Approximant basis direct + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup approximantDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisDirectInterpContext
      rothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-small-alekhnovich" "CBivariate"
    "Approximant basis direct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup alekApproximantDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisDirectInterpContext
      alekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-small" "CBivariate"
    "Approximant basis subproduct + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup approximantSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisSubproductInterpContext
      rothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-small-alekhnovich"
    "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup
    alekApproximantSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisSubproductInterpContext
      alekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-fast" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastAlekDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastAlekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext fastRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastAlekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext fastAlekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastAlekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext fastAlekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-small-fast" "CBivariate"
    "Approximant basis direct + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup
    fastApproximantDirectMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisDirectInterpContext fastRothRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-small-alekhnovich-fast"
    "CBivariate"
    "Approximant basis direct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup
    fastAlekApproximantDirectMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisDirectInterpContext fastAlekRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-small-fast" "CBivariate"
    "Approximant basis subproduct + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisSubproductInterpContext fastRothRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-small-alekhnovich-fast"
    "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup
    fastAlekApproximantSubproductMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisSubproductInterpContext fastAlekRootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-small-koalabear",
    title := "Guruswami-Sudan filtered core, small (KoalaBear)",
    records := #[
      denseRow, denseAlekRow, leeDirectRow,
      leeDirectAlekRow, leeSubproductRow, leeSubproductAlekRow, approximantDirectRow,
      approximantDirectAlekRow, approximantSubproductRow, approximantSubproductAlekRow,
      fastDenseRow, fastDenseAlekRow, fastLeeDirectRow, fastLeeDirectAlekRow, fastLeeSubproductRow,
      fastLeeSubproductAlekRow, fastApproximantDirectRow, fastApproximantDirectAlekRow,
      fastApproximantSubproductRow, fastApproximantSubproductAlekRow
    ]
  }, gen)

def runGsFilteredCoreMediumKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMediumInterpMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := gsMediumBenchmarkPoints message
  let fastPoints := gsMediumBenchmarkPoints fastMessage
  let rothRootContext := koalaBearRothRootContext
  let fastRothRootContext := fastKoalaBearRothRootContext
  let alekRootContext := koalaBearAlekhnovichRootContext
  let fastAlekRootContext := fastKoalaBearAlekhnovichRootContext
  let warmup := gsWarmupIterations preset
  let leeMeasured := preset.selectNat 10 1 1
  let approximantDirectMeasured := preset.selectNat 2 1 1
  let approximantSubproductMeasured := preset.selectNat 2 1 1
  let fastLeeMeasured := preset.selectNat 50 7 1
  let fastApproximantDirectMeasured := preset.selectNat 7 1 1
  let fastApproximantSubproductMeasured := preset.selectNat 7 1 1
  let alekLeeMeasured := leeMeasured
  let alekApproximantDirectMeasured := approximantDirectMeasured
  let alekApproximantSubproductMeasured := approximantSubproductMeasured
  let fastAlekLeeMeasured := fastLeeMeasured
  let fastAlekApproximantDirectMeasured := fastApproximantDirectMeasured
  let fastAlekApproximantSubproductMeasured := fastApproximantSubproductMeasured
  let checksumIterations := groupChecksumIterations leeMeasured [
    leeMeasured, leeMeasured, approximantDirectMeasured, approximantSubproductMeasured,
    fastLeeMeasured, fastLeeMeasured,
    fastApproximantDirectMeasured, fastApproximantSubproductMeasured,
    alekLeeMeasured, alekLeeMeasured, alekApproximantDirectMeasured,
    alekApproximantSubproductMeasured, fastAlekLeeMeasured,
    fastAlekLeeMeasured, fastAlekApproximantDirectMeasured,
    fastAlekApproximantSubproductMeasured
  ]
  let leeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup leeMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext rothRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-alekhnovich" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup alekLeeMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext alekRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup leeMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext rothRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-alekhnovich" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup alekLeeMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext alekRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-roth" "CBivariate"
    "Approximant basis direct + RR roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup approximantDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisDirectInterpContext
      rothRootContext gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-alekhnovich" "CBivariate"
    "Approximant basis direct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup alekApproximantDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisDirectInterpContext
      alekRootContext gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-roth" "CBivariate"
    "Approximant basis subproduct + RR roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup approximantSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisSubproductInterpContext
      rothRootContext gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let approximantSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-alekhnovich" "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup alekApproximantSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearApproximantBasisSubproductInterpContext
      alekRootContext gsMediumInterpParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-fast" "CBivariate"
    "Lee-O'Sullivan direct + RR roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext fastRothRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan direct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastAlekLeeMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext fastAlekRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + RR roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRothRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-alekhnovich-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastAlekLeeMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext fastAlekRootContext
        gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-roth-fast" "CBivariate"
    "Approximant basis direct + RR roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastApproximantDirectMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisDirectInterpContext fastRothRootContext
      gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantDirectAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-direct-alekhnovich-fast" "CBivariate"
    "Approximant basis direct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup
    fastAlekApproximantDirectMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisDirectInterpContext fastAlekRootContext
      gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-roth-fast" "CBivariate"
    "Approximant basis subproduct + RR roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisSubproductInterpContext fastRothRootContext
      gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastApproximantSubproductAlekRow <- runTimed
    "guruswami-sudan-filtered-core-approximant-subproduct-alekhnovich-fast"
    "CBivariate"
    "Approximant basis subproduct + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup
    fastAlekApproximantSubproductMeasured
    (fun _ ↦ gsFilteredCore fastPoints
      fastKoalaBearApproximantBasisSubproductInterpContext fastAlekRootContext
      gsMediumInterpParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-medium-koalabear",
    title := "Guruswami-Sudan filtered core, medium (KoalaBear)",
    records := #[
      leeDirectRow, leeDirectAlekRow, leeSubproductRow,
      leeSubproductAlekRow, approximantDirectRow, approximantDirectAlekRow,
      approximantSubproductRow, approximantSubproductAlekRow, fastLeeDirectRow,
      fastLeeDirectAlekRow, fastLeeSubproductRow,
      fastLeeSubproductAlekRow, fastApproximantDirectRow, fastApproximantDirectAlekRow,
      fastApproximantSubproductRow, fastApproximantSubproductAlekRow
    ]
  }, gen)

end CompPolyBench
