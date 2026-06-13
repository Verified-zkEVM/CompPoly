/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.OddTrial
import CompPoly.Univariate.Roots.LasVegas.Probability.Recursive

/-!
# Repeated Odd Trials and Geometric Fallback Bounds

Independent repeated odd-field split trials for one unresolved factor, the
geometric bound on reaching enumeration fallback, and the one-factor witness of
the recursive fallback model. The `_of_uniformProbe` variants discharge the
per-trial half-success hypothesis from the actual uniform probe source.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Independent repeated odd-field split trials for one unresolved factor. -/
noncomputable def repeatedOddSplitTrialsPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) :
    Nat → Nat → PMF (List (TrialResult F))
  | 0, _offset => pure []
  | attempts + 1, offset => do
      let trial ← oddSplitTrialPMF M D enumeration q coefficientCount g offset
      let trials ← repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
        (offset + 1)
      pure (trial :: trials)

/-- Probability that the one-factor loop reaches fallback after all split attempts fail. -/
noncomputable def fallbackAfterOddAttemptsProbability {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat) :
    ℝ≥0∞ :=
  eventProbability
    (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts offset)
    {trials | TrialResult.allFailed trials}

private theorem toOuterMeasure_map_cons_allFailed {F : Type*} [Zero F]
    (dist : PMF (List (TrialResult F))) (trial : TrialResult F) :
    (dist.map (List.cons trial)).toOuterMeasure {trials | TrialResult.allFailed trials} =
      if ¬ trial.IsSuccess then
        dist.toOuterMeasure {trials | TrialResult.allFailed trials}
      else
        0 := by
  cases trial <;>
    simp [PMF.toOuterMeasure_map_apply, TrialResult.IsSuccess, TrialResult.allFailed]

private theorem fallbackAfterOddAttemptsProbability_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat) :
    fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g
        (attempts + 1) offset =
      eventProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g offset)
          {trial | ¬ trial.IsSuccess} *
        fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g
          attempts (offset + 1) := by
  change (PMF.bind (oddSplitTrialPMF M D enumeration q coefficientCount g offset)
      (fun trial ↦ PMF.map (List.cons trial)
        (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
          (offset + 1)))).toOuterMeasure
        {trials | TrialResult.allFailed trials} =
    (oddSplitTrialPMF M D enumeration q coefficientCount g offset).toOuterMeasure
      {trial | ¬ trial.IsSuccess} *
      (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
        (offset + 1)).toOuterMeasure
        {trials | TrialResult.allFailed trials}
  rw [PMF.toOuterMeasure_bind_apply]
  trans (∑' trial, (if ¬ trial.IsSuccess then
        (oddSplitTrialPMF M D enumeration q coefficientCount g offset) trial else 0) *
        (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
          (offset + 1)).toOuterMeasure
          {trials | TrialResult.allFailed trials})
  · apply tsum_congr
    intro trial
    rw [toOuterMeasure_map_cons_allFailed]
    by_cases hfail : ¬ trial.IsSuccess <;> simp [hfail]
  · conv_rhs =>
      rw [PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro trial
    by_cases hsuccess : trial.IsSuccess <;> simp [hsuccess]

/--
If every one-factor trial succeeds with probability at least `1 / 2`, the
probability of using fallback after `attempts` trials is at most `2^-attempts`.
-/
theorem fallbackAfterOddAttempts_probability_le_geometric {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat)
    (hstep : ∀ i, i < attempts →
      (2 : ℝ≥0∞)⁻¹ ≤
        trialSuccessProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g (offset + i))) :
    fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g attempts offset ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  induction attempts generalizing offset with
  | zero =>
      rw [fallbackAfterOddAttemptsProbability, eventProbability, repeatedOddSplitTrialsPMF]
      exact le_trans
        ((pure ([] : List (TrialResult F)) : PMF (List (TrialResult F))).toOuterMeasure.mono
          (Set.subset_univ _))
        (by simp [PMF.toOuterMeasure_apply])
  | succ attempts ih =>
      rw [fallbackAfterOddAttemptsProbability_succ]
      let half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹
      have hfail : eventProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g offset)
          {trial | ¬ trial.IsSuccess} ≤ half := by
        exact trialFailureProbability_le_half_of_success _ (hstep 0 (by omega))
      have hrest :
          fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g attempts
              (offset + 1) ≤
            half ^ attempts := by
        exact ih (offset + 1) (by
          intro i hi
          have h := hstep (i + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      refine (mul_le_mul' hfail hrest).trans ?_
      change half * half ^ attempts ≤ half ^ (attempts + 1)
      rw [pow_succ]
      exact le_of_eq (_root_.mul_comm (a := half) (b := half ^ attempts))

/--
For a squarefree finite-field root product over an odd field, the uniform probe
source reaches enumeration fallback after `attempts` one-factor trials with
probability at most `2^-attempts`.
-/
theorem fallbackAfterOddAttempts_probability_le_geometric_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts offset : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    fallbackAfterOddAttemptsProbability M D enumeration.toFieldEnumeration q
        (CPolynomial.natDegree g) g attempts offset ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  apply fallbackAfterOddAttempts_probability_le_geometric
  intro i _hi
  exact oddSplitTrial_success_probability_ge_half M D enumeration g (offset + i)
    hfield hrootProduct hdegree

/--
The repeated one-factor odd-field trial source satisfies the recursive fallback
model by concentrating the bad-rank mass at rank `0`.
-/
theorem repeatedOddSplitTrialsPMF_recursiveFallbackProbabilityModel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset degree : Nat)
    (hdegree : 2 ≤ degree)
    (hstep : ∀ i, i < attempts →
      (2 : ℝ≥0∞)⁻¹ ≤
        trialSuccessProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g (offset + i))) :
    RecursiveFallbackProbabilityModel
      (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts offset)
      {trials | TrialResult.allFailed trials}
      attempts degree := by
  refine
    ⟨fun j ↦ if j = 0 then {trials | TrialResult.allFailed trials} else ∅,
      ?_, ?_, ?_⟩
  · intro trials htrials
    exact Set.mem_iUnion.mpr ⟨0, by simpa using htrials⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      have hzero_mem : 0 ∈ Finset.range (degree - 1) := by
        simp
        omega
      exact (hj hzero_mem).elim
    · simp [hj0, eventProbability]
  · intro j _hj
    by_cases hj0 : j = 0
    · subst j
      simpa [fallbackAfterOddAttemptsProbability] using
        fallbackAfterOddAttempts_probability_le_geometric M D enumeration q coefficientCount
          g attempts offset hstep
    · simp [hj0, eventProbability]

/--
The one-factor recursive fallback model witness, with the per-trial
half-success hypothesis discharged from the actual uniform probe source.
-/
theorem repeatedOddSplitTrialsPMF_recursiveFallbackProbabilityModel_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts offset degree : Nat)
    (hdeg : 2 ≤ degree)
    (hfield : OddUniformFieldModel F q enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    RecursiveFallbackProbabilityModel
      (repeatedOddSplitTrialsPMF M D enumeration.toFieldEnumeration q
        (CPolynomial.natDegree g) g attempts offset)
      {trials | TrialResult.allFailed trials}
      attempts degree := by
  apply repeatedOddSplitTrialsPMF_recursiveFallbackProbabilityModel M D
    enumeration.toFieldEnumeration q (CPolynomial.natDegree g) g attempts offset degree hdeg
  intro i _hi
  exact oddSplitTrial_success_probability_ge_half M D enumeration g (offset + i)
    hfield hrootProduct hdegree

set_option maxHeartbeats 1600000 in
/--
Bridge to the executable retry loop: the deterministic `tryOddSplitAttemptsWith`,
driven by a probe table whose entries are sampled independently and uniformly,
exhausts all attempts with probability at most `2 ^ -attempts`.

Unlike the trial-PMF theorems, the randomized object here is the actual
runtime function applied to an honestly sampled `ProbeFamily`.
-/
theorem tryOddSplitAttemptsWith_uniformTable_none_le_geometric {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat) (g : CPolynomial F)
    (hstep : (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability (oddSplitTrialPMF M D enumeration q coefficientCount g 0)) :
    ∀ attempts : Nat,
      eventProbability (uniformProbeTablePMF enumeration coefficientCount attempts)
        {table : List (CPolynomial F) |
          tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0 = none} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  have hfailset : ((fun h : CPolynomial F ↦
      (match cantorZassenhausOddAttemptWith M D q
          ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 with
        | some children => TrialResult.split children
        | none => TrialResult.failed)) ⁻¹'
        {trial : TrialResult F | ¬ trial.IsSuccess}) =
      {h : CPolynomial F | cantorZassenhausOddAttemptWith M D q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none} := by
    ext h
    cases h0 : cantorZassenhausOddAttemptWith M D q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 <;>
      simp [h0, TrialResult.IsSuccess]
  have hfail : (uniformProbePMF enumeration coefficientCount).toOuterMeasure
      {h : CPolynomial F | cantorZassenhausOddAttemptWith M D q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none} ≤
      (2 : ℝ≥0∞)⁻¹ := by
    rw [← hfailset, ← PMF.toOuterMeasure_map_apply]
    have hhalf := trialFailureProbability_le_half_of_success
      (oddSplitTrialPMF M D enumeration q coefficientCount g 0) hstep
    rw [eventProbability, oddSplitTrialPMF] at hhalf
    exact hhalf
  intro attempts
  induction attempts with
  | zero =>
      rw [eventProbability, uniformProbeTablePMF, PMF.toOuterMeasure_pure_apply,
        if_pos (by
          rw [Set.mem_setOf_eq]
          unfold tryOddSplitAttemptsWith
          rfl)]
      simp
  | succ attempts ih =>
      rw [eventProbability, uniformProbeTablePMF, PMF.toOuterMeasure_bind_apply]
      have hsection : ∀ (h : CPolynomial F) (rest : List (CPolynomial F)),
          (tryOddSplitAttemptsWith M D q (tableProbeFamily (h :: rest)) g
            (attempts + 1) 0 = none) ↔
          (cantorZassenhausOddAttemptWith M D q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none ∧
            tryOddSplitAttemptsWith M D q (tableProbeFamily rest) g attempts 0 = none) := by
        intro h rest
        unfold tryOddSplitAttemptsWith
        rw [cantorZassenhausOddAttemptWith_probe_congr M D q (g := g)
          (p2 := ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F))
          (a2 := 0) (by simp [tableProbeFamily])]
        rw [tryOddSplitAttemptsWith_probe_congr M D q
          (p1 := tableProbeFamily (h :: rest)) (p2 := tableProbeFamily rest) (g := g)
          attempts (0 + 1) 0 (by
            intro i _hi
            simp [tableProbeFamily, Nat.add_comm])]
        cases h0 : cantorZassenhausOddAttemptWith M D q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 with
        | some c => simp
        | none =>
            rw [← tryOddSplitAttemptsWith.eq_def]
            simp
      have hweight : ∀ h : CPolynomial F,
          ((uniformProbeTablePMF enumeration coefficientCount attempts).map
            (List.cons h)).toOuterMeasure
            {table : List (CPolynomial F) |
              tryOddSplitAttemptsWith M D q (tableProbeFamily table) g
                (attempts + 1) 0 = none} =
          if cantorZassenhausOddAttemptWith M D q
              ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none then
            (uniformProbeTablePMF enumeration coefficientCount attempts).toOuterMeasure
              {table : List (CPolynomial F) |
                tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0 = none}
          else 0 := by
        intro h
        rw [PMF.toOuterMeasure_map_apply]
        by_cases h0 : cantorZassenhausOddAttemptWith M D q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none
        · rw [if_pos h0]
          congr 1
          ext rest
          rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, hsection h rest]
          simp [h0]
        · rw [if_neg h0]
          have hempty : (List.cons h ⁻¹'
              {table : List (CPolynomial F) |
                tryOddSplitAttemptsWith M D q (tableProbeFamily table) g
                  (attempts + 1) 0 = none}) = ∅ := by
            ext rest
            rw [Set.mem_preimage, Set.mem_setOf_eq, hsection h rest]
            simp [h0]
          rw [hempty]
          simp
      calc (∑' h : CPolynomial F, uniformProbePMF enumeration coefficientCount h *
              ((uniformProbeTablePMF enumeration coefficientCount attempts).map
                (List.cons h)).toOuterMeasure
                {table : List (CPolynomial F) |
                  tryOddSplitAttemptsWith M D q (tableProbeFamily table) g
                    (attempts + 1) 0 = none})
          ≤ ∑' h : CPolynomial F,
              (if cantorZassenhausOddAttemptWith M D q
                  ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none
                then uniformProbePMF enumeration coefficientCount h else 0) *
                ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
            apply ENNReal.tsum_le_tsum
            intro h
            rw [hweight h]
            by_cases h0 : cantorZassenhausOddAttemptWith M D q
                ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none
            · rw [if_pos h0, if_pos h0]
              exact mul_le_mul' le_rfl (by
                have := ih
                rwa [eventProbability] at this)
            · rw [if_neg h0, if_neg h0]
              simp
        _ = (uniformProbePMF enumeration coefficientCount).toOuterMeasure
              {h : CPolynomial F | cantorZassenhausOddAttemptWith M D q
                ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none} *
              ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
            rw [ENNReal.tsum_mul_right]
            congr 1
            rw [PMF.toOuterMeasure_apply]
            apply tsum_congr
            intro h
            rw [Set.indicator_apply]
            rfl
        _ ≤ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ attempts :=
            _root_.mul_le_mul_left hfail _
        _ = ((2 : ℝ≥0∞)⁻¹) ^ (attempts + 1) := by
            rw [pow_succ, _root_.mul_comm]

/--
For a squarefree odd-field root product, the executable retry loop driven by an
honestly sampled uniform probe table reaches fallback with probability at most
`2 ^ -attempts`.
-/
theorem tryOddSplitAttemptsWith_uniformTable_none_le_geometric_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    eventProbability
      (uniformProbeTablePMF enumeration.toFieldEnumeration
        (CPolynomial.natDegree g) attempts)
      {table : List (CPolynomial F) |
        tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0 = none} ≤
    ((2 : ℝ≥0∞)⁻¹) ^ attempts :=
  tryOddSplitAttemptsWith_uniformTable_none_le_geometric M D
    enumeration.toFieldEnumeration q (CPolynomial.natDegree g) g
    (oddSplitTrial_success_probability_ge_half M D enumeration g 0 hfield
      hrootProduct hdegree)
    attempts

/--
Deterministic multi-factor splitter driven by per-factor probe tables: the
`n`-th processed splittable factor is handed the `n`-th table through the
abstract per-factor split function `tryTable`. This is a table-driven, fully
computable mirror of the randomized branch of `lasVegasSplitLoopWith`,
recording per-factor fallback flags.
-/
def recursiveSplitWithTables {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (tryTable : List (CPolynomial F) → CPolynomial F → Option (Array (CPolynomial F))) :
    Nat → List (CPolynomial F) → List (List (CPolynomial F)) → List Bool
  | 0, _stack, _tables => []
  | _fuel + 1, [], _tables => []
  | fuel + 1, g :: stack, tables =>
      if CPolynomial.natDegree g < 2 then
        recursiveSplitWithTables tryTable fuel stack tables
      else
        match tables with
        | [] => []
        | table :: tables =>
            match tryTable table g with
            | none => true :: recursiveSplitWithTables tryTable fuel stack tables
            | some children =>
                false :: recursiveSplitWithTables tryTable fuel
                  (children.toList ++ stack) tables

/-- Independent uniform probe tables, one per processed factor. -/
noncomputable def uniformProbeTablesPMF {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (coefficientCount attempts : Nat) :
    Nat → PMF (List (List (CPolynomial F)))
  | 0 => PMF.pure []
  | n + 1 =>
      (uniformProbeTablePMF enumeration coefficientCount attempts).bind fun table ↦
        (uniformProbeTablesPMF enumeration coefficientCount attempts n).map
          (List.cons table)

section RecursiveTables

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]
variable (tryTable : List (CPolynomial F) → CPolynomial F → Option (Array (CPolynomial F)))

private theorem recursiveSplitWithTables_skip (fuel : Nat) {g : CPolynomial F}
    (stack : List (CPolynomial F)) (hdeg : CPolynomial.natDegree g < 2)
    (tables : List (List (CPolynomial F))) :
    recursiveSplitWithTables tryTable (fuel + 1) (g :: stack) tables =
      recursiveSplitWithTables tryTable fuel stack tables := by
  rw [recursiveSplitWithTables.eq_def]
  dsimp only
  rw [if_pos hdeg]

private theorem recursiveSplitWithTables_nil_tables (fuel : Nat) {g : CPolynomial F}
    (stack : List (CPolynomial F)) (hdeg : ¬ CPolynomial.natDegree g < 2) :
    recursiveSplitWithTables tryTable (fuel + 1) (g :: stack) [] = [] := by
  rw [recursiveSplitWithTables.eq_def]
  dsimp only
  rw [if_neg hdeg]

private theorem recursiveSplitWithTables_cons_none (fuel : Nat) {g : CPolynomial F}
    (stack : List (CPolynomial F)) (hdeg : ¬ CPolynomial.natDegree g < 2)
    {table : List (CPolynomial F)} (tables : List (List (CPolynomial F)))
    (htry : tryTable table g = none) :
    recursiveSplitWithTables tryTable (fuel + 1) (g :: stack) (table :: tables) =
      true :: recursiveSplitWithTables tryTable fuel stack tables := by
  rw [recursiveSplitWithTables.eq_def]
  dsimp only
  rw [if_neg hdeg]
  simp [htry]

private theorem recursiveSplitWithTables_cons_some (fuel : Nat) {g : CPolynomial F}
    (stack : List (CPolynomial F)) (hdeg : ¬ CPolynomial.natDegree g < 2)
    {table : List (CPolynomial F)} (tables : List (List (CPolynomial F)))
    {children : Array (CPolynomial F)}
    (htry : tryTable table g = some children) :
    recursiveSplitWithTables tryTable (fuel + 1) (g :: stack) (table :: tables) =
      false :: recursiveSplitWithTables tryTable fuel
        (children.toList ++ stack) tables := by
  rw [recursiveSplitWithTables.eq_def]
  dsimp only
  rw [if_neg hdeg]
  simp [htry]

/-- Table-driven traces never exceed the split budget of the initial stack. -/
theorem recursiveSplitWithTables_length_le
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (table : List (CPolynomial F)) (children : Array (CPolynomial F)),
        tryTable table g = some children → IsSplitStep g children) :
    ∀ fuel (stack : List (CPolynomial F)) (tables : List (List (CPolynomial F))),
      (recursiveSplitWithTables tryTable fuel stack tables).length ≤
        stackSplitBudget stack := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack tables
      rw [recursiveSplitWithTables.eq_def]
      simp
  | succ fuel ih =>
      intro stack tables
      cases stack with
      | nil =>
          rw [recursiveSplitWithTables.eq_def]
          simp
      | cons g stack =>
          by_cases hdeg : CPolynomial.natDegree g < 2
          · rw [recursiveSplitWithTables_skip tryTable fuel stack hdeg tables]
            refine le_trans (ih stack tables) ?_
            simp only [stackSplitBudget]
            omega
          · have hdeg2 : 2 ≤ g.toPoly.natDegree := by
              have h := Nat.le_of_not_lt hdeg
              rwa [CPolynomial.natDegree_toPoly] at h
            cases tables with
            | nil =>
                rw [recursiveSplitWithTables_nil_tables tryTable fuel stack hdeg]
                simp
            | cons table tables =>
                have hg : g ≠ 0 := by
                  intro h0
                  apply hdeg
                  rw [h0]
                  have hzero : CPolynomial.natDegree (0 : CPolynomial F) = 0 := rfl
                  omega
                cases htry : tryTable table g with
                | none =>
                    rw [recursiveSplitWithTables_cons_none tryTable fuel stack hdeg
                      tables htry]
                    have hlen := ih stack tables
                    simp only [stackSplitBudget, List.length_cons]
                    omega
                | some children =>
                    rw [recursiveSplitWithTables_cons_some tryTable fuel stack hdeg
                      tables htry]
                    have hlen := ih (children.toList ++ stack) tables
                    rw [stackSplitBudget_append] at hlen
                    obtain ⟨hsize2, hchild, hwork⟩ := hsplit g hg table children htry
                    have hsw := stackWork_eq_two_mul_budget_add_length children.toList
                      fun c hc ↦ (hchild c hc).2.2
                    have hlen2 : children.toList.length = children.size := by simp
                    simp only [splitWork] at hwork
                    simp only [stackSplitBudget, List.length_cons]
                    omega

/--
Each processed factor of the table-driven splitter falls back with probability
at most `2 ^ -attempts` under independently sampled uniform probe tables.
-/
theorem recursiveSplitWithTables_rank_le_geometric {q : Nat}
    (enumeration : FieldEnumeration F) (coefficientCount attempts : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (table : List (CPolynomial F)) (children : Array (CPolynomial F)),
        tryTable table g = some children → IsSplitStep g children)
    (hfail : ∀ (g : CPolynomial F), lasVegasSplitterInput q g →
      2 ≤ CPolynomial.natDegree g →
      (uniformProbeTablePMF enumeration coefficientCount attempts).toOuterMeasure
        {table : List (CPolynomial F) | tryTable table g = none} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts) :
    ∀ fuel (stack : List (CPolynomial F)) (j n : Nat),
      (∀ g ∈ stack, lasVegasSplitterInput q g) →
      eventProbability
        (uniformProbeTablesPMF enumeration coefficientCount attempts n)
        {tables : List (List (CPolynomial F)) |
          (recursiveSplitWithTables tryTable fuel stack tables)[j]? = some true} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack j n _hstack
      have hE : {tables : List (List (CPolynomial F)) |
          (recursiveSplitWithTables tryTable 0 stack tables)[j]? = some true} =
          (∅ : Set (List (List (CPolynomial F)))) := by
        ext tables
        rw [Set.mem_setOf_eq, recursiveSplitWithTables.eq_def]
        simp
      rw [eventProbability, hE]
      simp
  | succ fuel ih =>
      intro stack j n hstack
      cases stack with
      | nil =>
          have hE : {tables : List (List (CPolynomial F)) |
              (recursiveSplitWithTables tryTable (fuel + 1) [] tables)[j]? =
                some true} = (∅ : Set (List (List (CPolynomial F)))) := by
            ext tables
            rw [Set.mem_setOf_eq, recursiveSplitWithTables.eq_def]
            simp
          rw [eventProbability, hE]
          simp
      | cons g stack =>
          by_cases hdeg : CPolynomial.natDegree g < 2
          · have hE : {tables : List (List (CPolynomial F)) |
                (recursiveSplitWithTables tryTable (fuel + 1) (g :: stack)
                  tables)[j]? = some true} =
                {tables : List (List (CPolynomial F)) |
                  (recursiveSplitWithTables tryTable fuel stack tables)[j]? =
                    some true} := by
              ext tables
              rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
                recursiveSplitWithTables_skip tryTable fuel stack hdeg tables]
            rw [hE]
            exact ih stack j n fun x hx ↦ hstack x (by simp [hx])
          · have hvalid := hstack g (by simp)
            have hg : g ≠ 0 := hvalid.1
            have hdeg2 : 2 ≤ CPolynomial.natDegree g := Nat.le_of_not_lt hdeg
            have hbridge := hfail g hvalid hdeg2
            cases n with
            | zero =>
                rw [uniformProbeTablesPMF, eventProbability,
                  PMF.toOuterMeasure_pure_apply, if_neg (by
                    rw [Set.mem_setOf_eq,
                      recursiveSplitWithTables_nil_tables tryTable fuel stack hdeg]
                    simp)]
                exact zero_le'
            | succ n =>
                rw [uniformProbeTablesPMF, eventProbability,
                  PMF.toOuterMeasure_bind_apply]
                cases j with
                | zero =>
                    trans (∑' table : List (CPolynomial F),
                      (if tryTable table g = none then
                        uniformProbeTablePMF enumeration coefficientCount attempts table
                      else 0))
                    · apply ENNReal.tsum_le_tsum
                      intro table
                      rw [PMF.toOuterMeasure_map_apply]
                      by_cases htry : tryTable table g = none
                      · rw [if_pos htry]
                        refine le_trans (mul_le_mul' le_rfl
                          (toOuterMeasure_apply_le_one _ _)) ?_
                        rw [MulOneClass.mul_one]
                      · rw [if_neg htry]
                        obtain ⟨children, hchildren⟩ :=
                          Option.ne_none_iff_exists'.mp htry
                        have hpre : (List.cons table ⁻¹'
                            {tables : List (List (CPolynomial F)) |
                              (recursiveSplitWithTables tryTable (fuel + 1)
                                (g :: stack) tables)[0]? = some true}) = ∅ := by
                          ext tables
                          rw [Set.mem_preimage, Set.mem_setOf_eq,
                            recursiveSplitWithTables_cons_some tryTable fuel
                              stack hdeg tables hchildren]
                          simp
                        rw [hpre]
                        simp
                    · refine le_trans (le_of_eq ?_) hbridge
                      rw [PMF.toOuterMeasure_apply]
                      apply tsum_congr
                      intro table
                      rw [Set.indicator_apply]
                      rfl
                | succ j' =>
                    trans (∑' table : List (CPolynomial F),
                      uniformProbeTablePMF enumeration coefficientCount attempts table *
                        ((2 : ℝ≥0∞)⁻¹) ^ attempts)
                    · apply ENNReal.tsum_le_tsum
                      intro table
                      apply mul_le_mul' le_rfl
                      rw [PMF.toOuterMeasure_map_apply]
                      cases htry : tryTable table g with
                      | none =>
                          have hpre : (List.cons table ⁻¹'
                              {tables : List (List (CPolynomial F)) |
                                (recursiveSplitWithTables tryTable (fuel + 1)
                                  (g :: stack) tables)[j' + 1]? = some true}) =
                              {tables : List (List (CPolynomial F)) |
                                (recursiveSplitWithTables tryTable fuel stack
                                  tables)[j']? = some true} := by
                            ext tables
                            rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq,
                              recursiveSplitWithTables_cons_none tryTable fuel
                                stack hdeg tables htry]
                            simp
                          rw [hpre]
                          exact ih stack j' n fun x hx ↦ hstack x (by simp [hx])
                      | some children =>
                          have hpre : (List.cons table ⁻¹'
                              {tables : List (List (CPolynomial F)) |
                                (recursiveSplitWithTables tryTable (fuel + 1)
                                  (g :: stack) tables)[j' + 1]? = some true}) =
                              {tables : List (List (CPolynomial F)) |
                                (recursiveSplitWithTables tryTable fuel
                                  (children.toList ++ stack) tables)[j']? =
                                    some true} := by
                            ext tables
                            rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq,
                              recursiveSplitWithTables_cons_some tryTable fuel
                                stack hdeg tables htry]
                            simp
                          rw [hpre]
                          obtain ⟨_hsize2, hchild, _hwork⟩ :=
                            hsplit g hg table children htry
                          apply ih (children.toList ++ stack) j' n
                          intro x hx
                          rw [List.mem_append] at hx
                          rcases hx with hx | hx
                          · exact ⟨(hchild x hx).1, (hchild x hx).2.1.trans hvalid.2⟩
                          · exact hstack x (by simp [hx])
                    · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, _root_.one_mul]

/-- Table-driven trace entries beyond the split budget never appear. -/
theorem recursiveSplitWithTables_rank_eq_zero_of_budget_le
    (enumeration : FieldEnumeration F) (coefficientCount attempts fuel n : Nat)
    (stack : List (CPolynomial F)) {j : Nat}
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (table : List (CPolynomial F)) (children : Array (CPolynomial F)),
        tryTable table g = some children → IsSplitStep g children)
    (hj : stackSplitBudget stack ≤ j) :
    eventProbability
      (uniformProbeTablesPMF enumeration coefficientCount attempts n)
      {tables : List (List (CPolynomial F)) |
        (recursiveSplitWithTables tryTable fuel stack tables)[j]? = some true} =
    0 := by
  have hE : {tables : List (List (CPolynomial F)) |
      (recursiveSplitWithTables tryTable fuel stack tables)[j]? = some true} =
      (∅ : Set (List (List (CPolynomial F)))) := by
    ext tables
    rw [Set.mem_setOf_eq]
    have hlen := recursiveSplitWithTables_length_le tryTable hsplit fuel stack tables
    rw [List.getElem?_eq_none (by omega)]
    simp
  rw [eventProbability, hE]
  simp

/--
The table-driven splitter satisfies the recursive fallback model under
independently sampled uniform probe tables.
-/
theorem recursiveSplitWithTables_recursiveFallbackProbabilityModel {q : Nat}
    (enumeration : FieldEnumeration F)
    (g : CPolynomial F) (coefficientCount attempts fuel n : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (table : List (CPolynomial F)) (children : Array (CPolynomial F)),
        tryTable table g = some children → IsSplitStep g children)
    (hfail : ∀ (g : CPolynomial F), lasVegasSplitterInput q g →
      2 ≤ CPolynomial.natDegree g →
      (uniformProbeTablePMF enumeration coefficientCount attempts).toOuterMeasure
        {table : List (CPolynomial F) | tryTable table g = none} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    RecursiveFallbackProbabilityModel
      (uniformProbeTablesPMF enumeration coefficientCount attempts n)
      {tables : List (List (CPolynomial F)) |
        true ∈ recursiveSplitWithTables tryTable fuel [g] tables}
      attempts (CPolynomial.natDegree g) := by
  refine ⟨fun j ↦ {tables : List (List (CPolynomial F)) |
    (recursiveSplitWithTables tryTable fuel [g] tables)[j]? = some true},
    ?_, ?_, ?_⟩
  · intro tables htables
    rw [Set.mem_setOf_eq] at htables
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htables
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    apply recursiveSplitWithTables_rank_eq_zero_of_budget_le tryTable enumeration
      coefficientCount attempts fuel n [g] hsplit
    have hbudget : stackSplitBudget [g] = g.toPoly.natDegree - 1 := by
      simp [stackSplitBudget]
    have hdeg := (CPolynomial.natDegree_toPoly g).symm
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    have hrank := recursiveSplitWithTables_rank_le_geometric tryTable enumeration
      coefficientCount attempts hsplit hfail fuel [g] j n (by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact hvalid)
    refine le_trans hrank ?_
    have hjk : j ≤ attempts := by omega
    have hC : (1 : ℝ≥0∞) ≤ (Nat.choose attempts j : ℝ≥0∞) := by
      exact_mod_cast Nat.choose_pos hjk
    exact le_mul_of_one_le_right' hC

/--
Generic recursive table bridge: the deterministic table-driven splitter, with
one independently sampled uniform probe table per processed factor, reaches
exhaustive enumeration anywhere in the recursion with probability at most the
binomial tail.
-/
theorem recursiveSplitWithTables_fallback_probability_le_binomialTail {q : Nat}
    (enumeration : FieldEnumeration F)
    (g : CPolynomial F) (coefficientCount attempts fuel n : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (table : List (CPolynomial F)) (children : Array (CPolynomial F)),
        tryTable table g = some children → IsSplitStep g children)
    (hfail : ∀ (g : CPolynomial F), lasVegasSplitterInput q g →
      2 ≤ CPolynomial.natDegree g →
      (uniformProbeTablePMF enumeration coefficientCount attempts).toOuterMeasure
        {table : List (CPolynomial F) | tryTable table g = none} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (uniformProbeTablesPMF enumeration coefficientCount attempts n)
      {tables : List (List (CPolynomial F)) |
        true ∈ recursiveSplitWithTables tryTable fuel [g] tables} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) :=
  recursiveFallback_probability_le_binomialTail _ _ _ _
    (recursiveSplitWithTables_recursiveFallbackProbabilityModel tryTable enumeration g
      coefficientCount attempts fuel n hsplit hfail hvalid hattempts)

end RecursiveTables

/-- Multi-factor odd Cantor-Zassenhaus splitting driven by probe tables. -/
def recursiveOddSplitWithTables {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q attempts : Nat) :
    Nat → List (CPolynomial F) → List (List (CPolynomial F)) → List Bool :=
  recursiveSplitWithTables fun table g ↦
    tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0

/--
Recursive table bridge for the odd branch: the deterministic table-driven
splitter, run on a splitter-valid input of degree `d` with one independently
sampled uniform probe table per processed factor, reaches exhaustive
enumeration anywhere in the recursion with probability at most the binomial
tail `2 ^ -attempts * ∑_{j ≤ d - 2} C(attempts, j)`.

The number `n` of supplied tables is arbitrary: missing tables only truncate
the run, and `d - 1` tables always suffice.
-/
theorem recursiveOddSplitWithTables_fallback_probability_le_binomialTail {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (coefficientCount attempts fuel n : Nat)
    (hcount : 2 ≤ coefficientCount)
    (hfield : OddUniformFieldModel F q enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (uniformProbeTablesPMF enumeration.toFieldEnumeration coefficientCount attempts n)
      {tables : List (List (CPolynomial F)) |
        true ∈ recursiveOddSplitWithTables M D q attempts fuel [g] tables} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) := by
  apply recursiveSplitWithTables_fallback_probability_le_binomialTail _
    enumeration.toFieldEnumeration g coefficientCount attempts fuel n
    (fun _g hg _table _children htry ↦
      tryOddSplitAttemptsWith_isSplitStep M D q _ hg htry)
    ?_ hvalid hattempts
  intro g hvalid hdeg
  have hinput : RootProductProbabilityInput q g :=
    rootProductProbabilityInput_of_lasVegasSplitterInput hvalid hfield.card_eq
  have hbridge := tryOddSplitAttemptsWith_uniformTable_none_le_geometric M D
    enumeration.toFieldEnumeration q coefficientCount g
    (oddSplitTrial_success_probability_ge_half_of_two_le M D enumeration g
      coefficientCount 0 hcount hfield (hinput.hasTwoDistinctRoots hdeg) hvalid.1)
    attempts
  rwa [eventProbability] at hbridge

/--
Per-factor table-driven split attempt of the full Las Vegas backend: the odd
Cantor-Zassenhaus retry loop for odd `q`, the characteristic-two trace retry
loop when trace metadata is supplied, mirroring the branch selection of
`lasVegasSplitLoopWith`.
-/
def lasVegasTryTableSplit {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F)) (q attempts : Nat)
    (table : List (CPolynomial F)) (g : CPolynomial F) :
    Option (Array (CPolynomial F)) :=
  match traceCtx? with
  | some traceCtx =>
      if q % 2 = 1 then
        tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0
      else
        tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
          attempts 0
  | none => tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0

/-- The full Las Vegas backend driven by per-factor probe tables. -/
def lasVegasSplitWithTables {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F)) (q attempts : Nat) :
    Nat → List (CPolynomial F) → List (List (CPolynomial F)) → List Bool :=
  recursiveSplitWithTables (lasVegasTryTableSplit M D traceCtx? q attempts)

/-- Successful backend table attempts are split steps. -/
theorem lasVegasTryTableSplit_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F)) (q attempts : Nat)
    {g : CPolynomial F} (hg : g ≠ 0)
    {table : List (CPolynomial F)} {children : Array (CPolynomial F)}
    (htry : lasVegasTryTableSplit M D traceCtx? q attempts table g = some children) :
    IsSplitStep g children := by
  unfold lasVegasTryTableSplit at htry
  cases traceCtx? with
  | none => exact tryOddSplitAttemptsWith_isSplitStep M D q _ hg htry
  | some traceCtx =>
      dsimp only at htry
      by_cases hodd : q % 2 = 1
      · rw [if_pos hodd] at htry
        exact tryOddSplitAttemptsWith_isSplitStep M D q _ hg htry
      · rw [if_neg hodd] at htry
        exact tryEvenTraceSplitAttemptsWith_isSplitStep M D traceCtx q _ hg htry

/-- Backend table attempts on splitter-valid factors fail with probability at
most `2 ^ -attempts`. -/
theorem lasVegasTryTableSplit_uniformTable_none_le_geometric {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (coefficientCount attempts : Nat)
    (hcount : 2 ≤ coefficientCount)
    (hmodel : LasVegasUniformFieldModel F q traceCtx? enumeration)
    (g : CPolynomial F) (hvalid : lasVegasSplitterInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    (uniformProbeTablePMF enumeration.toFieldEnumeration coefficientCount
      attempts).toOuterMeasure
      {table : List (CPolynomial F) |
        lasVegasTryTableSplit M D traceCtx? q attempts table g = none} ≤
    ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  have hinput : RootProductProbabilityInput q g :=
    rootProductProbabilityInput_of_lasVegasSplitterInput hvalid hmodel.card_eq
  have hg : g ≠ 0 := hvalid.1
  cases hmodel with
  | odd hodd hfield =>
      have hset : {table : List (CPolynomial F) |
          lasVegasTryTableSplit M D traceCtx? q attempts table g = none} =
          {table : List (CPolynomial F) |
            tryOddSplitAttemptsWith M D q (tableProbeFamily table) g attempts 0 =
              none} := by
        ext table
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
        unfold lasVegasTryTableSplit
        cases traceCtx? <;> simp [hodd]
      rw [hset]
      have hbridge := tryOddSplitAttemptsWith_uniformTable_none_le_geometric M D
        enumeration.toFieldEnumeration q coefficientCount g
        (oddSplitTrial_success_probability_ge_half_of_two_le M D enumeration g
          coefficientCount 0 hcount hfield (hinput.hasTwoDistinctRoots hdegree) hg)
        attempts
      rwa [eventProbability] at hbridge
  | evenTrace traceCtx hctx heven hfield =>
      have hset : {table : List (CPolynomial F) |
          lasVegasTryTableSplit M D traceCtx? q attempts table g = none} =
          {table : List (CPolynomial F) |
            tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
              attempts 0 = none} := by
        ext table
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
        unfold lasVegasTryTableSplit
        rw [hctx]
        dsimp only
        rw [if_neg (by omega : ¬ q % 2 = 1)]
      rw [hset]
      have hbridge := tryEvenTraceSplitAttemptsWith_uniformTable_none_le_geometric M D
        traceCtx enumeration.toFieldEnumeration q coefficientCount g
        (evenTraceTrial_success_probability_ge_half_of_two_le M D traceCtx enumeration g
          coefficientCount 0 hcount hfield (hinput.hasTwoDistinctRoots hdegree) hg)
        attempts
      rwa [eventProbability] at hbridge

/--
Backend recursive table bridge: over any finite field — odd, or binary with
matching trace metadata — the deterministic table-driven Las Vegas backend, run
on a splitter-valid input of degree `d` with one independently sampled uniform
probe table per processed factor, reaches exhaustive enumeration anywhere in
the recursion with probability at most the binomial tail
`2 ^ -attempts * ∑_{j ≤ d - 2} C(attempts, j)`.
-/
theorem lasVegasSplitWithTables_fallback_probability_le_binomialTail {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (coefficientCount attempts fuel n : Nat)
    (hcount : 2 ≤ coefficientCount)
    (hmodel : LasVegasUniformFieldModel F q traceCtx? enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (uniformProbeTablesPMF enumeration.toFieldEnumeration coefficientCount attempts n)
      {tables : List (List (CPolynomial F)) |
        true ∈ lasVegasSplitWithTables M D traceCtx? q attempts fuel [g] tables} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) :=
  recursiveSplitWithTables_fallback_probability_le_binomialTail _
    enumeration.toFieldEnumeration g coefficientCount attempts fuel n
    (fun _g hg _table _children htry ↦
      lasVegasTryTableSplit_isSplitStep M D traceCtx? q attempts hg htry)
    (fun g hvalid hdeg ↦
      lasVegasTryTableSplit_uniformTable_none_le_geometric M D traceCtx? enumeration
        coefficientCount attempts hcount hmodel g hvalid hdeg)
    hvalid hattempts

end FiniteField

end Roots

end CPolynomial

end CompPoly
