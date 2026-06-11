/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Perturbed Received-Word Benchmarks

Perturbed (non-codeword) counterparts of the dense-interpolation/Roth-Ruckenstein
small interpolation, core, and filtered-core benchmark groups.
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
    "Guruswami-Sudan dense interpolation on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-noncodeword-small-koalabear",
    "Guruswami-Sudan dense/RR full core on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear",
    "Guruswami-Sudan dense/RR filtered core on perturbed received word, small (KoalaBear)"⟩
]

/-! ### Group runners -/

private def runGsInterpolationNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let denseRow <- runTimed
    "guruswami-sudan-interp-dense-noncodeword-small" "CBivariate"
    "Dense linear"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup measured
    (fun _ ↦ koalaBearDenseInterpContext.interpolate inputs.points gsSmallParams)
    (checksumInterpolationValidityOption inputs.points gsSmallParams)
    checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-interp-dense-noncodeword-small-fast" "CBivariate"
    "Dense linear"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup fastMeasured
    (fun _ ↦ fastKoalaBearDenseInterpContext.interpolate inputs.fastPoints gsSmallParams)
    (checksumInterpolationValidityOption inputs.fastPoints gsSmallParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-noncodeword-small-koalabear",
    title := "Guruswami-Sudan dense interpolation on perturbed received word, small (KoalaBear)",
    records := #[denseRow, fastDenseRow]
  }, gen)

private def runGsCoreNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let denseRow <- runTimed
    "guruswami-sudan-core-dense-noncodeword-small" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Field" gsNonCodewordSmallInputShape preset warmup measured
    (fun _ ↦
      (gsCore inputs.points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams).filter (passesCandidateDistance inputs.points gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-core-dense-noncodeword-small-fast" "CBivariate"
    "Dense linear + RR roots"
    "KoalaBear.Fast.Field" gsNonCodewordSmallInputShape preset warmup fastMeasured
    (fun _ ↦
      (gsCore inputs.fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams).filter
          (passesCandidateDistance inputs.fastPoints gsNonCodewordSmallErrors))
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-noncodeword-small-koalabear",
    title := "Guruswami-Sudan dense/RR full core on perturbed received word, small (KoalaBear)",
    records := #[denseRow, fastDenseRow]
  }, gen)

private def runGsFilteredCoreNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let denseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-noncodeword-small" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Field" gsNonCodewordSmallFilteredShape preset warmup measured
    (fun _ ↦
      gsFilteredCore inputs.points koalaBearDenseInterpContext koalaBearRothRootContext
        gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-noncodeword-small-fast" "CBivariate"
    "Dense linear + RR roots + filter"
    "KoalaBear.Fast.Field" gsNonCodewordSmallFilteredShape preset warmup fastMeasured
    (fun _ ↦
      gsFilteredCore inputs.fastPoints fastKoalaBearDenseInterpContext
        fastKoalaBearRothRootContext gsSmallParams gsNonCodewordSmallErrors)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-noncodeword-small-koalabear",
    title := "Guruswami-Sudan dense/RR filtered core on perturbed received word, small (KoalaBear)",
    records := #[denseRow, fastDenseRow]
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
