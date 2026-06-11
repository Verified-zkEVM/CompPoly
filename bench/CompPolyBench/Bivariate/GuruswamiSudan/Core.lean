/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Core Benchmarks

Full dense-interpolation root-backend `gsCore` and `gsFilteredCore` benchmark
runners.
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
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [
    measured, fastMeasured, fastMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-core-dense-small" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup measured
    (fun _ ↦ gsCore points koalaBearDenseInterpContext koalaBearRothRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-core-dense-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Field" gsSmallInterpInputShape preset warmup measured
    (fun _ ↦ gsCore points koalaBearDenseInterpContext alekRootContext
      gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-core-dense-small-fast" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-core-dense-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots"
    "KoalaBear.Fast.Field" gsSmallInterpInputShape preset warmup fastMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearDenseInterpContext fastAlekRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-small-koalabear",
    title := "Guruswami-Sudan dense full core, small (KoalaBear)",
    records := #[denseRow, denseAlekRow, fastDenseRow, fastDenseAlekRow]
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
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [
    measured, fastMeasured, fastMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup measured
    (fun _ ↦
      gsFilteredCore points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let denseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-alekhnovich" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup measured
    (fun _ ↦
      gsFilteredCore points koalaBearDenseInterpContext alekRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-fast" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastDenseAlekRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-alekhnovich-fast" "CBivariate"
    "Dense linear + Alekhnovich roots + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearDenseInterpContext
        fastAlekRootContext gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-small-koalabear",
    title := "Guruswami-Sudan dense filtered core, small (KoalaBear)",
    records := #[denseRow, denseAlekRow, fastDenseRow, fastDenseAlekRow]
  }, gen)

end CompPolyBench
