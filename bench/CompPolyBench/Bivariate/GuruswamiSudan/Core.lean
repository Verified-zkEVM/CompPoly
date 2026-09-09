/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Core Benchmarks

Full backend-parametric `gsCore` and `gsFilteredCore` benchmark runners.
-/

public section

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
  let checksumIterations := digestPeriod 1
  let denseRow <- runTimedSpec
    { name := "guruswami-sudan-core-dense-small", representation := "CBivariate",
      method := "Dense linear + RR roots", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup denseMeasured
    (fun _ ↦ gsCore points koalaBearDenseInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala
  let denseAlekRow <- runTimedSpec
    { name := "guruswami-sudan-core-dense-small-alekhnovich", representation := "CBivariate",
      method := "Dense linear + Alekhnovich roots", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup alekDenseMeasured
    (fun _ ↦ gsCore points koalaBearDenseInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala
  let leeDirectRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-direct-small", representation := "CBivariate",
      method := "Lee-O'Sullivan direct + RR roots", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup leeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala
  let leeDirectAlekRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-direct-small-alekhnovich", representation := "CBivariate",
      method := "Lee-O'Sullivan direct + Alekhnovich roots", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup alekLeeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala
  let leeSubproductRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-subproduct-small", representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct + RR roots", field := "KoalaBear.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup leeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala
  let leeSubproductAlekRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-subproduct-small-alekhnovich",
      representation := "CBivariate", method := "Lee-O'Sullivan subproduct + Alekhnovich roots",
      field := "KoalaBear.Field", inputShape := gsSmallInterpInputShape,
      digestIterations := checksumIterations }
    preset warmup alekLeeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala
  let fastDenseRow <- runTimedSpec
    { name := "guruswami-sudan-core-dense-small-fast", representation := "CBivariate",
      method := "Dense linear + RR roots", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastDenseMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast
  let fastDenseAlekRow <- runTimedSpec
    { name := "guruswami-sudan-core-dense-small-alekhnovich-fast", representation := "CBivariate",
      method := "Dense linear + Alekhnovich roots", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastAlekDenseMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearDenseInterpContext fastAlekRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast
  let fastLeeDirectRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-direct-small-fast", representation := "CBivariate",
      method := "Lee-O'Sullivan direct + RR roots", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastLeeDirectMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastKoalaBearRothRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast
  let fastLeeDirectAlekRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-direct-small-alekhnovich-fast",
      representation := "CBivariate", method := "Lee-O'Sullivan direct + Alekhnovich roots",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallInterpInputShape,
      digestIterations := checksumIterations }
    preset warmup fastAlekLeeDirectMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastAlekRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast
  let fastLeeSubproductRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-subproduct-small-fast", representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct + RR roots", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallInterpInputShape, digestIterations := checksumIterations }
    preset warmup fastLeeSubproductMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastKoalaBearRothRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast
  let fastLeeSubproductAlekRow <- runTimedSpec
    { name := "guruswami-sudan-core-lee-subproduct-small-alekhnovich-fast",
      representation := "CBivariate", method := "Lee-O'Sullivan subproduct + Alekhnovich roots",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallInterpInputShape,
      digestIterations := checksumIterations }
    preset warmup fastAlekLeeSubproductMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastAlekRootContext gsSmallParams)
    checksumPolynomialArrayKoalaFast
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
  let checksumIterations := digestPeriod 1
  let denseRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-dense-small", representation := "CBivariate",
      method := "Dense linear + RR roots + filter", field := "KoalaBear.Field",
      inputShape := gsSmallFilteredShape, digestIterations := checksumIterations }
    preset warmup denseMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala
  let denseAlekRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-dense-small-alekhnovich",
      representation := "CBivariate", method := "Dense linear + Alekhnovich roots + filter",
      field := "KoalaBear.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup alekDenseMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearDenseInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala
  let leeDirectRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-direct-small", representation := "CBivariate",
      method := "Lee-O'Sullivan direct + RR roots + filter", field := "KoalaBear.Field",
      inputShape := gsSmallFilteredShape, digestIterations := checksumIterations }
    preset warmup leeDirectMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala
  let leeDirectAlekRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-direct-small-alekhnovich",
      representation := "CBivariate",
      method := "Lee-O'Sullivan direct + Alekhnovich roots + filter", field := "KoalaBear.Field",
      inputShape := gsSmallFilteredShape, digestIterations := checksumIterations }
    preset warmup alekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala
  let leeSubproductRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-subproduct-small", representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct + RR roots + filter", field := "KoalaBear.Field",
      inputShape := gsSmallFilteredShape, digestIterations := checksumIterations }
    preset warmup leeSubproductMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala
  let leeSubproductAlekRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich",
      representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct + Alekhnovich roots + filter",
      field := "KoalaBear.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup alekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala
  let fastDenseRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-dense-small-fast", representation := "CBivariate",
      method := "Dense linear + RR roots + filter", field := "KoalaBear.Fast.Field",
      inputShape := gsSmallFilteredShape, digestIterations := checksumIterations }
    preset warmup fastDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast
  let fastDenseAlekRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-dense-small-alekhnovich-fast",
      representation := "CBivariate", method := "Dense linear + Alekhnovich roots + filter",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup fastAlekDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearDenseInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast
  let fastLeeDirectRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-direct-small-fast",
      representation := "CBivariate", method := "Lee-O'Sullivan direct + RR roots + filter",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup fastLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast
  let fastLeeDirectAlekRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-direct-small-alekhnovich-fast",
      representation := "CBivariate",
      method := "Lee-O'Sullivan direct + Alekhnovich roots + filter",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup fastAlekLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast
  let fastLeeSubproductRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-subproduct-small-fast",
      representation := "CBivariate", method := "Lee-O'Sullivan subproduct + RR roots + filter",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup fastLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast
  let fastLeeSubproductAlekRow <- runTimedSpec
    { name := "guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich-fast",
      representation := "CBivariate",
      method := "Lee-O'Sullivan subproduct + Alekhnovich roots + filter",
      field := "KoalaBear.Fast.Field", inputShape := gsSmallFilteredShape,
      digestIterations := checksumIterations }
    preset warmup fastAlekLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast
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
