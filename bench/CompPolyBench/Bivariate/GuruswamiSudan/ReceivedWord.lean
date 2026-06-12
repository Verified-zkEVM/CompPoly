/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.GuruswamiSudan.Shared

/-!
# Guruswami-Sudan Perturbed Received-Word Benchmarks

Perturbed (non-codeword) counterparts of the codeword interpolation, core, and
filtered-core benchmark groups, over the same small and medium input shapes and
the same backend rows, plus a long-code large interpolation group comparing
only the Lee-O'Sullivan and approximant backends. Perturbations stay within
the Guruswami-Sudan decoding radius, so the full pipeline still recovers the
original message.

Different interpolation backends may return different valid witnesses on the
same perturbed word, so interpolation rows checksum the witness validity class
rather than coefficients; core rows checksum the decoded candidate lists.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

/-! ### Perturbation shapes

The small shape perturbs every 3rd symbol (22 errors at `n=64`, inside the
`m=2, D=75` decoding radius of 26), the medium and large shapes every 7th
symbol (28 errors at `n=192`, inside the radius of 71; 720 errors at
`n=5040`, inside the `m=2, D=6300` radius of 1890). Filtered groups use the
exact error count as the distance radius.
-/

private def gsNonCodewordSmallPeriod : Nat := 3

private def gsNonCodewordMediumPeriod : Nat := 7

private def gsNonCodewordLargePeriod : Nat := 7

private def gsNonCodewordSmallErrors : Nat :=
  (gsSmallPointCount + gsNonCodewordSmallPeriod - 1) / gsNonCodewordSmallPeriod

private def gsNonCodewordMediumErrors : Nat :=
  (gsMediumInterpPointCount + gsNonCodewordMediumPeriod - 1) /
    gsNonCodewordMediumPeriod

private def gsNonCodewordSmallInputShape : String :=
  gsSmallInterpInputShape ++ s!",errors=every{gsNonCodewordSmallPeriod}"

private def gsNonCodewordMediumInputShape : String :=
  gsMediumInterpInputShape ++ s!",errors=every{gsNonCodewordMediumPeriod}"

private def gsNonCodewordLargeInputShape : String :=
  gsLargeInterpInputShape ++ s!",errors=every{gsNonCodewordLargePeriod}"

private def gsNonCodewordSmallFilteredShape : String :=
  gsNonCodewordSmallInputShape ++ s!",r={gsNonCodewordSmallErrors}"

private def gsNonCodewordMediumFilteredShape : String :=
  gsNonCodewordMediumInputShape ++ s!",r={gsNonCodewordMediumErrors}"

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

/-- Interpolation rows for one field implementation.  `checksumQ` maps the
returned witness option to its checksum class. -/
private def perturbedInterpRows {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F]
    (fieldName fieldSuffix sizeKey : String) (preset : BenchPreset)
    (points : Array (Prod F F)) (params : GSInterpParams)
    (checksumQ :
      Array (Prod F F) → GSInterpParams → Option (CBivariate F) → Nat)
    (backends : Array (PerturbedBackend F)) : Array PerturbedRowSpec :=
  backends.map fun backend ↦
    { key :=
        s!"guruswami-sudan-interp-{backend.keyPart}-noncodeword-{sizeKey}{fieldSuffix}"
      method := backend.method
      field := fieldName
      measured := backend.measured preset
      run := fun _ ↦
        checksumQ points params (backend.ctx.interpolate points params) }

/-- Witness validity class through the divisibility-based full check: the
per-point Hasse check costs `O(n * m^2 * l * D)` term evaluations — minutes
per row at `n ≈ 5000`, dominating every backend inside the timed closure — so
the large group validates witnesses through the base-`(Y - R)` digit
divisibility characterization, which checks the multiplicity constraints at
every point in seconds with NTT-backed contexts. -/
private def checksumDivisibilityInterpolationValidityOption {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (Mul : CPolynomial.MulContext F) (Mod : CPolynomial.ModContext F)
    (points : Array (F × F)) (params : GSInterpParams)
    (Q? : Option (CBivariate F)) : Nat :=
  match Q? with
  | none => 0
  | some Q =>
      if interpolationWitnessIsValidViaDivisibilityBool V E Mul Mod
          points params Q then
        2
      else
        1

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
  ⟨"lee-direct", "Lee-O'Sullivan direct", koalaBearLeeDirectInterpContext,
    15, 2, 1⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    koalaBearLeeSubproductInterpContext, 15, 2, 1⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    koalaBearApproximantBasisDirectInterpContext, 2, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    koalaBearApproximantBasisSubproductInterpContext, 2, 1, 1⟩,
  ⟨"hybrid", "Hybrid", koalaBearHybridInterpContext, 8, 1, 1⟩
]

private def gsNonCodewordSmallFastBackends :
    Array (PerturbedBackend KoalaBear.Fast.Field) := #[
  ⟨"dense", "Dense linear", fastKoalaBearDenseInterpContext, 1, 1, 1⟩,
  ⟨"lee-direct", "Lee-O'Sullivan direct", fastKoalaBearLeeDirectInterpContext,
    80, 11, 2⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    fastKoalaBearLeeSubproductInterpContext, 70, 10, 2⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    fastKoalaBearApproximantBasisDirectInterpContext, 6, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    fastKoalaBearApproximantBasisSubproductInterpContext, 6, 1, 1⟩,
  ⟨"hybrid", "Hybrid", fastKoalaBearHybridInterpContext, 35, 5, 1⟩
]

private def gsNonCodewordMediumSlowBackends :
    Array (PerturbedBackend KoalaBear.Field) := #[
  ⟨"lee-direct", "Lee-O'Sullivan direct", koalaBearLeeDirectInterpContext,
    2, 1, 1⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    koalaBearLeeSubproductInterpContext, 2, 1, 1⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    koalaBearApproximantBasisDirectInterpContext, 1, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    koalaBearApproximantBasisSubproductInterpContext, 1, 1, 1⟩,
  ⟨"hybrid", "Hybrid", koalaBearHybridInterpContext, 1, 1, 1⟩
]

private def gsNonCodewordMediumFastBackends :
    Array (PerturbedBackend KoalaBear.Fast.Field) := #[
  ⟨"lee-direct", "Lee-O'Sullivan direct", fastKoalaBearLeeDirectInterpContext,
    10, 1, 1⟩,
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    fastKoalaBearLeeSubproductInterpContext, 10, 1, 1⟩,
  ⟨"approximant-direct", "Approximant basis direct",
    fastKoalaBearApproximantBasisDirectInterpContext, 1, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    fastKoalaBearApproximantBasisSubproductInterpContext, 1, 1, 1⟩,
  ⟨"hybrid", "Hybrid", fastKoalaBearHybridInterpContext, 5, 1, 1⟩
]

/-- Long-code interpolation backends: only the two reduction-based backends
stay tractable at `n ≈ 5000` (Koetter grows like `~n^3.4` and the dense
solver far faster), so the large group benchmarks Lee-O'Sullivan against the
approximant basis, and only over the native-word fast field — canonical
KoalaBear multiplies every row by another ~3-5x without changing the
comparison. Only the subproduct variants run: the direct variants differ
just in the quadratic-in-`n` setup (vanishing polynomial, interpolant, and
modular products without a subproduct tree), which dominates their rows at
this size and adds minutes without informing the solver comparison. -/
private def gsNonCodewordLargeFastBackends :
    Array (PerturbedBackend KoalaBear.Fast.Field) := #[
  ⟨"lee-subproduct", "Lee-O'Sullivan subproduct",
    fastKoalaBearLeeSubproductInterpContext, 2, 1, 1⟩,
  ⟨"approximant-subproduct", "Approximant basis subproduct",
    fastKoalaBearApproximantBasisSubproductInterpContext, 4, 2, 1⟩,
  ⟨"hybrid", "Hybrid", fastKoalaBearHybridInterpContext, 2, 1, 1⟩
]

/-! ### Group metadata -/

/-- Benchmark group metadata for perturbed received-word rows. -/
def guruswamiSudanReceivedWordGroupInfos : List BenchGroupInfo := [
  ⟨"guruswami-sudan-interp-noncodeword-small-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-noncodeword-medium-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, medium (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-noncodeword-small-koalabear",
    "Guruswami-Sudan full core on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-noncodeword-medium-koalabear",
    "Guruswami-Sudan full core on perturbed received word, medium (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear",
    "Guruswami-Sudan filtered core on perturbed received word, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-noncodeword-medium-koalabear",
    "Guruswami-Sudan filtered core on perturbed received word, medium (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-noncodeword-large-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, large (KoalaBear)"⟩
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

private def perturbedMediumInputs (gen : StdGen) : PerturbedInputs × StdGen :=
  let (coeffs, gen) := (koalaBearArray gsMediumInterpMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := perturbEveryNthY gsNonCodewordMediumPeriod
    (codewordPointsWithCount gsMediumInterpPointCount message)
  let fastPoints := perturbEveryNthY gsNonCodewordMediumPeriod
    (codewordPointsWithCount gsMediumInterpPointCount fastMessage)
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
      inputs.points gsSmallParams checksumInterpolationValidityOption
      gsNonCodewordSmallSlowBackends ++
    perturbedInterpRows "KoalaBear.Fast.Field" "-fast" "small" preset
      inputs.fastPoints gsSmallParams checksumInterpolationValidityOption
      gsNonCodewordSmallFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 0
      ⟨"guruswami-sudan-interp-noncodeword-small-koalabear", ""⟩)
    gsNonCodewordSmallInputShape preset rows
  pure (group, gen)

private def runGsInterpolationNonCodewordMediumKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedMediumInputs gen
  let rows :=
    perturbedInterpRows "KoalaBear.Field" "" "medium" preset
      inputs.points gsMediumInterpParams checksumInterpolationValidityOption
      gsNonCodewordMediumSlowBackends ++
    perturbedInterpRows "KoalaBear.Fast.Field" "-fast" "medium" preset
      inputs.fastPoints gsMediumInterpParams checksumInterpolationValidityOption
      gsNonCodewordMediumFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 1
      ⟨"guruswami-sudan-interp-noncodeword-medium-koalabear", ""⟩)
    gsNonCodewordMediumInputShape preset rows
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

private def runGsCoreNonCodewordMediumKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedMediumInputs gen
  let rows :=
    perturbedCoreRows "core" "KoalaBear.Field" "" "medium" "" false
      gsNonCodewordMediumErrors preset
      inputs.points gsMediumInterpParams checksumPolynomialArrayKoala
      koalaBearRothRootContext koalaBearAlekhnovichRootContext
      gsNonCodewordMediumSlowBackends ++
    perturbedCoreRows "core" "KoalaBear.Fast.Field" "-fast" "medium" "" false
      gsNonCodewordMediumErrors preset
      inputs.fastPoints gsMediumInterpParams checksumPolynomialArrayKoalaFast
      fastKoalaBearRothRootContext fastKoalaBearAlekhnovichRootContext
      gsNonCodewordMediumFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 3
      ⟨"guruswami-sudan-core-noncodeword-medium-koalabear", ""⟩)
    gsNonCodewordMediumInputShape preset rows
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

private def runGsFilteredCoreNonCodewordMediumKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedMediumInputs gen
  let rows :=
    perturbedCoreRows "filtered-core" "KoalaBear.Field" "" "medium" " + filter"
      true gsNonCodewordMediumErrors preset
      inputs.points gsMediumInterpParams checksumPolynomialArrayKoala
      koalaBearRothRootContext koalaBearAlekhnovichRootContext
      gsNonCodewordMediumSlowBackends ++
    perturbedCoreRows "filtered-core" "KoalaBear.Fast.Field" "-fast" "medium"
      " + filter" true gsNonCodewordMediumErrors preset
      inputs.fastPoints gsMediumInterpParams checksumPolynomialArrayKoalaFast
      fastKoalaBearRothRootContext fastKoalaBearAlekhnovichRootContext
      gsNonCodewordMediumFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 5
      ⟨"guruswami-sudan-filtered-core-noncodeword-medium-koalabear", ""⟩)
    gsNonCodewordMediumFilteredShape preset rows
  pure (group, gen)

private def runGsInterpolationNonCodewordLargeKoala (preset : BenchPreset)
    (gen : StdGen) : IO (Prod BenchGroup StdGen) := do
  let (inputs, gen) := perturbedLargeInputs gen
  let rows :=
    perturbedInterpRows "KoalaBear.Fast.Field" "-fast" "large" preset
      inputs.fastPoints gsLargeInterpParams
      (checksumDivisibilityInterpolationValidityOption
        (CPolynomial.VanishingPolynomialContext.subproduct
          fastKoalaBearNttFastMulContext)
        fastKoalaBearNttFastBatchEvalContext
        fastKoalaBearNttFastMulContext fastKoalaBearNttFastModContext)
      gsNonCodewordLargeFastBackends
  let group ← runPerturbedGroup
    (guruswamiSudanReceivedWordGroupInfos.getD 6
      ⟨"guruswami-sudan-interp-noncodeword-large-koalabear", ""⟩)
    gsNonCodewordLargeInputShape preset rows
  pure (group, gen)

/-- Runnable received-word GS benchmark tasks. -/
def guruswamiSudanReceivedWordTasks : List BenchTask := [
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 0
    ⟨"guruswami-sudan-interp-noncodeword-small-koalabear", ""⟩)
    runGsInterpolationNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 1
    ⟨"guruswami-sudan-interp-noncodeword-medium-koalabear", ""⟩)
    runGsInterpolationNonCodewordMediumKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 2
    ⟨"guruswami-sudan-core-noncodeword-small-koalabear", ""⟩)
    runGsCoreNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 3
    ⟨"guruswami-sudan-core-noncodeword-medium-koalabear", ""⟩)
    runGsCoreNonCodewordMediumKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 4
    ⟨"guruswami-sudan-filtered-core-noncodeword-small-koalabear", ""⟩)
    runGsFilteredCoreNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 5
    ⟨"guruswami-sudan-filtered-core-noncodeword-medium-koalabear", ""⟩)
    runGsFilteredCoreNonCodewordMediumKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 6
    ⟨"guruswami-sudan-interp-noncodeword-large-koalabear", ""⟩)
    runGsInterpolationNonCodewordLargeKoala
]

end CompPolyBench
