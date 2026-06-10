/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Perturbed Received-Word Benchmarks

Perturbed (non-codeword) counterparts of the codeword interpolation, core, and
filtered-core benchmark groups, over the same small and large input shapes and
the same backend rows. Perturbations stay within the Guruswami-Sudan decoding
radius, so the full pipeline still recovers the original message.

Different interpolation backends may return different valid witnesses on the
same perturbed word, so interpolation rows checksum the witness validity class
rather than coefficients; core rows checksum the decoded candidate lists.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

/-! ### Perturbation shapes

The small shape perturbs every 3rd symbol (22 errors at `n=64`, inside the
`m=2, D=75` decoding radius of 26), the large shape every 7th symbol
(28 errors at `n=192`, inside the radius of 71). Filtered groups use the
exact error count as the distance radius.
-/

private def gsNonCodewordSmallPeriod : Nat := 3

private def gsNonCodewordLargePeriod : Nat := 7

private def gsNonCodewordSmallErrors : Nat :=
  (gsSmallPointCount + gsNonCodewordSmallPeriod - 1) / gsNonCodewordSmallPeriod

private def gsNonCodewordLargeErrors : Nat :=
  (gsLargeInterpPointCount + gsNonCodewordLargePeriod - 1) /
    gsNonCodewordLargePeriod

private def gsNonCodewordSmallInputShape : String :=
  gsSmallInterpInputShape ++ s!",errors=every{gsNonCodewordSmallPeriod}"

private def gsNonCodewordLargeInputShape : String :=
  gsLargeInterpInputShape ++ s!",errors=every{gsNonCodewordLargePeriod}"

private def gsNonCodewordSmallFilteredShape : String :=
  gsNonCodewordSmallInputShape ++ s!",r={gsNonCodewordSmallErrors}"

private def gsNonCodewordLargeFilteredShape : String :=
  gsNonCodewordLargeInputShape ++ s!",r={gsNonCodewordLargeErrors}"

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

/-! ### Group runner machinery

Iteration counts follow the bench conventions: within a group, each row's
count is sized so the rows spend approximately the same total wall-clock time;
presets only scale counts, with `medium ≈ large / 7` and
`small ≈ max 1 (large / 35)`, rounded to convenient values.
-/

/-- One benchmark row with the checksum precomposed onto the closure. -/
private structure PerturbedRowSpec where
  key : String
  method : String
  field : String
  measured : Nat
  run : Nat → Nat

/-- Interpolation backend descriptor: row-key part, method label, context, and
large/medium/small measured-iteration counts. -/
private structure PerturbedBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] where
  keyPart : String
  method : String
  ctx : GSInterpContext F
  large : Nat
  medium : Nat
  small : Nat

private def PerturbedBackend.measured {F : Type*} [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] (backend : PerturbedBackend F)
    (preset : BenchPreset) : Nat :=
  preset.selectNat backend.large backend.medium backend.small

/-- Run all rows of one perturbed-word group with a shared checksum prefix. -/
private def runPerturbedGroup (info : BenchGroupInfo) (inputShape : String)
    (preset : BenchPreset) (rows : Array PerturbedRowSpec) : IO BenchGroup := do
  let warmup := gsWarmupIterations preset
  let counts := (rows.map fun row ↦ row.measured).toList
  let checksumIterations := groupChecksumIterations (counts.headD 1) counts
  let mut records : Array BenchRecord := #[]
  for row in rows do
    let record ← runTimed row.key "CBivariate" row.method row.field inputShape
      preset warmup row.measured row.run id checksumIterations
    records := records.push record
  pure { groupKey := info.groupKey, title := info.title, records := records }

/-- Interpolation rows for one field implementation. -/
private def perturbedInterpRows {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F]
    (fieldName fieldSuffix sizeKey : String) (preset : BenchPreset)
    (points : Array (Prod F F)) (params : GSInterpParams)
    (backends : Array (PerturbedBackend F)) : Array PerturbedRowSpec :=
  backends.map fun backend ↦
    { key :=
        s!"guruswami-sudan-interp-{backend.keyPart}-noncodeword-{sizeKey}{fieldSuffix}"
      method := backend.method
      field := fieldName
      measured := backend.measured preset
      run := fun _ ↦
        checksumInterpolationValidityOption points params
          (backend.ctx.interpolate points params) }

/-- Core or filtered-core rows for one field implementation: one RR-roots row
and one Alekhnovich-roots row per backend. `filtered` selects `gsFilteredCore`.

On a perturbed received word, different valid interpolation witnesses can
carry different spurious `Y`-roots beyond the decoding radius, so the raw
`gsCore` candidate list is not canonical across backends. Candidates inside
the radius are roots of every valid witness, so checksums always compare the
distance-filtered sublist (a no-op for the already-filtered rows). -/
private def perturbedCoreRows {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F]
    (groupKeyPart fieldName fieldSuffix sizeKey methodSuffix : String)
    (filtered : Bool) (radius : Nat) (preset : BenchPreset)
    (points : Array (Prod F F)) (params : GSInterpParams)
    (checksumCandidates : Array (CPolynomial F) → Nat)
    (rothContext alekContext : GSRootContext F)
    (backends : Array (PerturbedBackend F)) : Array PerturbedRowSpec :=
  backends.flatMap fun backend ↦
    let runFor : GSRootContext F → Nat → Nat := fun rootContext _ ↦
      let candidates :=
        if filtered then
          gsFilteredCore points backend.ctx rootContext params radius
        else
          gsCore points backend.ctx rootContext params
      checksumCandidates
        (candidates.filter (passesCandidateDistance points radius))
    #[
      { key :=
          s!"guruswami-sudan-{groupKeyPart}-{backend.keyPart}-noncodeword-{sizeKey}{fieldSuffix}"
        method := s!"{backend.method} + RR roots{methodSuffix}"
        field := fieldName
        measured := backend.measured preset
        run := runFor rothContext },
      { key :=
          s!"guruswami-sudan-{groupKeyPart}-{backend.keyPart}" ++
            s!"-noncodeword-{sizeKey}-alekhnovich{fieldSuffix}"
        method := s!"{backend.method} + Alekhnovich roots{methodSuffix}"
        field := fieldName
        measured := backend.measured preset
        run := runFor alekContext }
    ]

/-! ### Backend tables -/

private def gsNonCodewordSmallSlowBackends :
    Array (PerturbedBackend KoalaBear.Field) := #[
  ⟨"dense", "Dense linear", koalaBearDenseInterpContext, 1, 1, 1⟩,
  ⟨"koetter", "Koetter", koalaBearKoetterInterpContext, 6, 1, 1⟩,
  ⟨"lee-direct", "Lee-O'Sullivan direct", koalaBearLeeDirectInterpContext,
    15, 2, 1⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    koalaBearLeeSubproductInterpContext, 15, 2, 1⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    koalaBearApproximantBasisDirectInterpContext, 2, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    koalaBearApproximantBasisSubproductInterpContext, 2, 1, 1⟩
]

private def gsNonCodewordSmallFastBackends :
    Array (PerturbedBackend KoalaBear.Fast.Field) := #[
  ⟨"dense", "Dense linear", fastKoalaBearDenseInterpContext, 1, 1, 1⟩,
  ⟨"koetter", "Koetter", fastKoalaBearKoetterInterpContext, 30, 4, 1⟩,
  ⟨"lee-direct", "Lee-O'Sullivan direct", fastKoalaBearLeeDirectInterpContext,
    80, 11, 2⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    fastKoalaBearLeeSubproductInterpContext, 70, 10, 2⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    fastKoalaBearApproximantBasisDirectInterpContext, 6, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    fastKoalaBearApproximantBasisSubproductInterpContext, 6, 1, 1⟩
]

private def gsNonCodewordLargeSlowBackends :
    Array (PerturbedBackend KoalaBear.Field) := #[
  ⟨"koetter", "Koetter", koalaBearKoetterInterpContext, 1, 1, 1⟩,
  ⟨"lee-direct", "Lee-O'Sullivan direct", koalaBearLeeDirectInterpContext,
    2, 1, 1⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    koalaBearLeeSubproductInterpContext, 2, 1, 1⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    koalaBearApproximantBasisDirectInterpContext, 1, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    koalaBearApproximantBasisSubproductInterpContext, 1, 1, 1⟩
]

private def gsNonCodewordLargeFastBackends :
    Array (PerturbedBackend KoalaBear.Fast.Field) := #[
  ⟨"koetter", "Koetter", fastKoalaBearKoetterInterpContext, 2, 1, 1⟩,
  ⟨"lee-direct", "Lee-O'Sullivan direct", fastKoalaBearLeeDirectInterpContext,
    10, 1, 1⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    fastKoalaBearLeeSubproductInterpContext, 10, 1, 1⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    fastKoalaBearApproximantBasisDirectInterpContext, 1, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    fastKoalaBearApproximantBasisSubproductInterpContext, 1, 1, 1⟩
]

/-! ### Group metadata -/

/-- Benchmark group metadata for perturbed received-word rows. -/
def guruswamiSudanReceivedWordGroupInfos : List BenchGroupInfo := [
  ⟨"guruswami-sudan-interp-noncodeword-small-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-noncodeword-large-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, large (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-noncodeword-small-koalabear",
    "Guruswami-Sudan full core on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-noncodeword-large-koalabear",
    "Guruswami-Sudan full core on perturbed received word, large (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear",
    "Guruswami-Sudan filtered core on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-noncodeword-large-koalabear",
    "Guruswami-Sudan filtered core on perturbed received word, large (KoalaBear)"⟩
]

/-! ### Shared per-shape inputs -/

private structure PerturbedInputs where
  points : Array (Prod KoalaBear.Field KoalaBear.Field)
  fastPoints : Array (Prod KoalaBear.Fast.Field KoalaBear.Fast.Field)

private def perturbedSmallInputs (gen : StdGen) : PerturbedInputs × StdGen :=
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := perturbEveryNthY gsNonCodewordSmallPeriod
    (codewordPointsWithCount gsSmallPointCount message)
  let fastPoints := perturbEveryNthY gsNonCodewordSmallPeriod
    (codewordPointsWithCount gsSmallPointCount fastMessage)
  ({ points := points, fastPoints := fastPoints }, gen)

private def perturbedLargeInputs (gen : StdGen) : PerturbedInputs × StdGen :=
  let (coeffs, gen) := (koalaBearArray gsLargeInterpMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := perturbEveryNthY gsNonCodewordLargePeriod
    (codewordPointsWithCount gsLargeInterpPointCount message)
  let fastPoints := perturbEveryNthY gsNonCodewordLargePeriod
    (codewordPointsWithCount gsLargeInterpPointCount fastMessage)
  ({ points := points, fastPoints := fastPoints }, gen)

/-! ### Group runners -/

private def runGsInterpolationNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let rows :=
    perturbedInterpRows "KoalaBear.Field" "" "small" preset
      inputs.points gsSmallParams gsNonCodewordSmallSlowBackends ++
    perturbedInterpRows "KoalaBear.Fast.Field" "-fast" "small" preset
      inputs.fastPoints gsSmallParams gsNonCodewordSmallFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 0
      ⟨"guruswami-sudan-interp-noncodeword-small-koalabear", ""⟩)
    gsNonCodewordSmallInputShape preset rows
  pure (group, gen)

private def runGsInterpolationNonCodewordLargeKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedLargeInputs gen
  let rows :=
    perturbedInterpRows "KoalaBear.Field" "" "large" preset
      inputs.points gsLargeInterpParams gsNonCodewordLargeSlowBackends ++
    perturbedInterpRows "KoalaBear.Fast.Field" "-fast" "large" preset
      inputs.fastPoints gsLargeInterpParams gsNonCodewordLargeFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 1
      ⟨"guruswami-sudan-interp-noncodeword-large-koalabear", ""⟩)
    gsNonCodewordLargeInputShape preset rows
  pure (group, gen)

private def runGsCoreNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let rows :=
    perturbedCoreRows "core" "KoalaBear.Field" "" "small" "" false
      gsNonCodewordSmallErrors preset
      inputs.points gsSmallParams checksumPolynomialArrayKoala
      koalaBearRothRootContext koalaBearAlekhnovichRootContext
      gsNonCodewordSmallSlowBackends ++
    perturbedCoreRows "core" "KoalaBear.Fast.Field" "-fast" "small" "" false
      gsNonCodewordSmallErrors preset
      inputs.fastPoints gsSmallParams checksumPolynomialArrayKoalaFast
      fastKoalaBearRothRootContext fastKoalaBearAlekhnovichRootContext
      gsNonCodewordSmallFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 2
      ⟨"guruswami-sudan-core-noncodeword-small-koalabear", ""⟩)
    gsNonCodewordSmallInputShape preset rows
  pure (group, gen)

private def runGsCoreNonCodewordLargeKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedLargeInputs gen
  let rows :=
    perturbedCoreRows "core" "KoalaBear.Field" "" "large" "" false
      gsNonCodewordLargeErrors preset
      inputs.points gsLargeInterpParams checksumPolynomialArrayKoala
      koalaBearRothRootContext koalaBearAlekhnovichRootContext
      gsNonCodewordLargeSlowBackends ++
    perturbedCoreRows "core" "KoalaBear.Fast.Field" "-fast" "large" "" false
      gsNonCodewordLargeErrors preset
      inputs.fastPoints gsLargeInterpParams checksumPolynomialArrayKoalaFast
      fastKoalaBearRothRootContext fastKoalaBearAlekhnovichRootContext
      gsNonCodewordLargeFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 3
      ⟨"guruswami-sudan-core-noncodeword-large-koalabear", ""⟩)
    gsNonCodewordLargeInputShape preset rows
  pure (group, gen)

private def runGsFilteredCoreNonCodewordSmallKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedSmallInputs gen
  let rows :=
    perturbedCoreRows "filtered-core" "KoalaBear.Field" "" "small" " + filter"
      true gsNonCodewordSmallErrors preset
      inputs.points gsSmallParams checksumPolynomialArrayKoala
      koalaBearRothRootContext koalaBearAlekhnovichRootContext
      gsNonCodewordSmallSlowBackends ++
    perturbedCoreRows "filtered-core" "KoalaBear.Fast.Field" "-fast" "small"
      " + filter" true gsNonCodewordSmallErrors preset
      inputs.fastPoints gsSmallParams checksumPolynomialArrayKoalaFast
      fastKoalaBearRothRootContext fastKoalaBearAlekhnovichRootContext
      gsNonCodewordSmallFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 4
      ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear", ""⟩)
    gsNonCodewordSmallFilteredShape preset rows
  pure (group, gen)

private def runGsFilteredCoreNonCodewordLargeKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedLargeInputs gen
  let rows :=
    perturbedCoreRows "filtered-core" "KoalaBear.Field" "" "large" " + filter"
      true gsNonCodewordLargeErrors preset
      inputs.points gsLargeInterpParams checksumPolynomialArrayKoala
      koalaBearRothRootContext koalaBearAlekhnovichRootContext
      gsNonCodewordLargeSlowBackends ++
    perturbedCoreRows "filtered-core" "KoalaBear.Fast.Field" "-fast" "large"
      " + filter" true gsNonCodewordLargeErrors preset
      inputs.fastPoints gsLargeInterpParams checksumPolynomialArrayKoalaFast
      fastKoalaBearRothRootContext fastKoalaBearAlekhnovichRootContext
      gsNonCodewordLargeFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 5
      ⟨"guruswami-sudan-filtered-core-noncodeword-large-koalabear", ""⟩)
    gsNonCodewordLargeFilteredShape preset rows
  pure (group, gen)

/-- Runnable received-word GS benchmark tasks. -/
def guruswamiSudanReceivedWordTasks : List BenchTask := [
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 0
    ⟨"guruswami-sudan-interp-noncodeword-small-koalabear", ""⟩)
    runGsInterpolationNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 1
    ⟨"guruswami-sudan-interp-noncodeword-large-koalabear", ""⟩)
    runGsInterpolationNonCodewordLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 2
    ⟨"guruswami-sudan-core-noncodeword-small-koalabear", ""⟩)
    runGsCoreNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 3
    ⟨"guruswami-sudan-core-noncodeword-large-koalabear", ""⟩)
    runGsCoreNonCodewordLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 4
    ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear", ""⟩)
    runGsFilteredCoreNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 5
    ⟨"guruswami-sudan-filtered-core-noncodeword-large-koalabear", ""⟩)
    runGsFilteredCoreNonCodewordLargeKoala
]

end CompPolyBench
