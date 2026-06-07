/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability Surface for Las Vegas Root Splitting

PMF-based theorem surface for the randomized performance story of the Las Vegas
finite-field root splitter. This module is intentionally separate from the
executable splitter modules: runtime root search remains pure and deterministic
for a fixed `ProbeFamily`, while this file models idealized uniform probes.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

namespace FieldEnumeration

/-- A complete field enumeration is nonempty when the field type has a zero. -/
theorem size_pos {F : Type*} [Zero F] (enumeration : FieldEnumeration F) :
    0 < enumeration.size := by
  rcases enumeration.complete 0 with ⟨i, _hi⟩
  exact Nat.zero_lt_of_lt i.isLt

end FieldEnumeration

/--
Probability-only strengthening of `FieldEnumeration`: the lazy enumeration has
no duplicate indices and its size is the finite-field cardinality `q`.
-/
structure UniformFieldEnumeration (F : Type*) (q : Nat) where
  toFieldEnumeration : FieldEnumeration F
  injective_elem : Function.Injective toFieldEnumeration.elem
  size_eq_q : toFieldEnumeration.size = q

namespace UniformFieldEnumeration

/-- A probability-uniform enumeration has positive cardinality. -/
theorem q_pos {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) :
    0 < q := by
  rw [← enumeration.size_eq_q]
  exact enumeration.toFieldEnumeration.size_pos

end UniformFieldEnumeration

/-- Uniform sampling from enumeration indices. -/
noncomputable def uniformFieldIndexPMF {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    PMF (Fin enumeration.size) :=
  PMF.ofFinset
    (fun _ : Fin enumeration.size ↦ (enumeration.size : ℝ≥0∞)⁻¹)
    Finset.univ
    (by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hne : (enumeration.size : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt enumeration.size_pos
      simpa [Fintype.card_fin] using
        ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top enumeration.size))
    (by
      intro i hi
      exact (hi (Finset.mem_univ i)).elim)

/-- Uniform field-element sampling induced by a lazy enumeration. -/
noncomputable def uniformFieldElementPMF {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    PMF F :=
  (uniformFieldIndexPMF enumeration).map enumeration.elem

/-- Complete injective enumerations put every field element in the PMF support. -/
theorem uniformFieldElementPMF_support_eq_univ {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) :
    (uniformFieldElementPMF enumeration.toFieldEnumeration).support = Set.univ := by
  ext a
  simp [uniformFieldElementPMF, uniformFieldIndexPMF]
  exact enumeration.toFieldEnumeration.complete a

/-- Every field element has probability `1 / q` under a uniform field enumeration. -/
theorem uniformFieldElementPMF_apply {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) (a : F) :
    uniformFieldElementPMF enumeration.toFieldEnumeration a = (q : ℝ≥0∞)⁻¹ := by
  rcases enumeration.toFieldEnumeration.complete a with ⟨i, hi⟩
  simp [uniformFieldElementPMF, uniformFieldIndexPMF, enumeration.size_eq_q]
  trans ∑ j : Fin enumeration.toFieldEnumeration.size, if j = i then (q : ℝ≥0∞)⁻¹ else 0
  · apply Finset.sum_congr rfl
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [hi]
    · have hne : a ≠ enumeration.toFieldEnumeration.elem j := by
        intro haj
        apply hji
        apply enumeration.injective_elem
        rw [hi]
        exact haj.symm
      simp [hne, hji]
  · simp

/--
Uniform PMF over coefficient arrays of fixed length, sampled independently from
the supplied field enumeration.
-/
noncomputable def uniformCoefficientArrayPMF {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    Nat → PMF (Array F)
  | 0 => pure #[]
  | n + 1 => do
      let coeffs ← uniformCoefficientArrayPMF enumeration n
      let coeff ← uniformFieldElementPMF enumeration
      pure (coeffs.push coeff)

private theorem uniformCoefficientArrayPMF_support_size {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    ∀ coefficientCount {coeffs : Array F},
      coeffs ∈ (uniformCoefficientArrayPMF enumeration coefficientCount).support →
        coeffs.size = coefficientCount := by
  intro coefficientCount
  induction coefficientCount with
  | zero =>
      intro coeffs hcoeffs
      rw [uniformCoefficientArrayPMF] at hcoeffs
      have heq : coeffs = #[] :=
        (PMF.mem_support_pure_iff (a := (#[] : Array F)) (a' := coeffs)).mp hcoeffs
      simp [heq]
  | succ n ih =>
      intro coeffs hcoeffs
      rw [uniformCoefficientArrayPMF] at hcoeffs
      change coeffs ∈
        ((uniformCoefficientArrayPMF enumeration n).bind fun coeffs0 ↦
          (uniformFieldElementPMF enumeration).bind fun coeff ↦
            pure (coeffs0.push coeff)).support at hcoeffs
      rw [PMF.mem_support_bind_iff] at hcoeffs
      rcases hcoeffs with ⟨coeffs0, hcoeffs0, htail⟩
      rw [PMF.mem_support_bind_iff] at htail
      rcases htail with ⟨coeff, _hcoeff, hpush⟩
      have hpush_eq : coeffs = coeffs0.push coeff :=
        (PMF.mem_support_pure_iff (a := coeffs0.push coeff) (a' := coeffs)).mp hpush
      subst coeffs
      simp [ih hcoeffs0]

private theorem ofArray_natDegree_lt_size_or_eq_zero {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F] (coeffs : Array F) :
    (CPolynomial.ofArray coeffs).natDegree < coeffs.size ∨ CPolynomial.ofArray coeffs = 0 := by
  cases hval : (CPolynomial.ofArray coeffs).val.size with
  | zero =>
      right
      apply CPolynomial.ext
      exact Array.eq_empty_of_size_eq_zero hval
  | succ n =>
      left
      have hnat : (CPolynomial.ofArray coeffs).natDegree = n := by
        simp [CPolynomial.natDegree, hval]
      have htrim_le : (CPolynomial.ofArray coeffs).val.size ≤ coeffs.size := by
        simpa [CPolynomial.ofArray] using
          CPolynomial.Raw.Trim.size_le_size (p := (coeffs : CPolynomial.Raw F))
      omega

/-- Uniform probe polynomial of degree bounded by the supplied coefficient count. -/
noncomputable def uniformProbePMF {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (coefficientCount : Nat) :
    PMF (CPolynomial F) :=
  (uniformCoefficientArrayPMF enumeration coefficientCount).map fun coeffs ↦
    CPolynomial.ofArray coeffs

/--
Probes sampled with `coefficientCount` coefficients have degree below that
bound, unless zero.
-/
theorem uniformProbePMF_support_natDegree_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (coefficientCount : Nat)
    {probe : CPolynomial F}
    (hprobe : probe ∈ (uniformProbePMF enumeration coefficientCount).support) :
    CPolynomial.natDegree probe < coefficientCount ∨ probe = 0 := by
  rw [uniformProbePMF, PMF.mem_support_map_iff] at hprobe
  rcases hprobe with ⟨coeffs, hcoeffs, hprobe_eq⟩
  subst probe
  have hsize := uniformCoefficientArrayPMF_support_size enumeration coefficientCount hcoeffs
  simpa [hsize] using ofArray_natDegree_lt_size_or_eq_zero (F := F) coeffs

/-- Result of one randomized split trial. -/
inductive TrialResult (F : Type*) [Zero F] where
  | split (children : Array (CPolynomial F))
  | failed

namespace TrialResult

/-- A trial succeeds when it returns proper child factors. -/
def IsSuccess {F : Type*} [Zero F] : TrialResult F → Prop
  | split _children => True
  | failed => False

/-- Child factors returned by a successful trial, or an empty array after failure. -/
def children {F : Type*} [Zero F] : TrialResult F → Array (CPolynomial F)
  | split children => children
  | failed => #[]

/-- A list of trials has not split the current factor. -/
def allFailed {F : Type*} [Zero F] : List (TrialResult F) → Prop
  | [] => True
  | trial :: trials => ¬ trial.IsSuccess ∧ allFailed trials

end TrialResult

/-- Probability of an event under a PMF, expressed through the PMF outer measure. -/
noncomputable def eventProbability {α : Type*} (dist : PMF α) (event : Set α) : ℝ≥0∞ :=
  dist.toOuterMeasure event

/-- Probability that a split trial succeeds. -/
noncomputable def trialSuccessProbability {F : Type*} [Zero F]
    (dist : PMF (TrialResult F)) :
    ℝ≥0∞ :=
  eventProbability dist {trial | trial.IsSuccess}

/--
The algebraic validity expected from a successful randomized split: nontrivial
proper children, divisibility by the parent, and root preservation.
-/
def IsProperRootPreservingSplit {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (parent : CPolynomial F) (children : Array (CPolynomial F)) : Prop :=
  2 ≤ children.size ∧
    (∀ child, child ∈ children.toList →
      child ≠ 0 ∧ child ≠ 1 ∧ child.val.size < parent.val.size ∧
        child.toPoly ∣ parent.toPoly) ∧
      (∀ a : F, CPolynomial.eval a parent = 0 →
        ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0)

/-- One odd-field Cantor-Zassenhaus trial under a uniform probe distribution. -/
noncomputable def oddSplitTrialPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempt : Nat) :
    PMF (TrialResult F) :=
  (uniformProbePMF enumeration coefficientCount).map fun h ↦
    match cantorZassenhausOddAttemptWith M D q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g attempt with
    | some children => TrialResult.split children
    | none => TrialResult.failed

/-- A successful trial in the support of the PMF is an algebraically valid split. -/
theorem oddSplitTrialPMF_support_success_valid {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempt : Nat) {children : Array (CPolynomial F)}
    (hmem : TrialResult.split children ∈
      (oddSplitTrialPMF M D enumeration q coefficientCount g attempt).support) :
    IsProperRootPreservingSplit g children := by
  rw [oddSplitTrialPMF, PMF.mem_support_map_iff] at hmem
  rcases hmem with ⟨probe, _hprobe, htrial⟩
  let probes : ProbeFamily F := { probe := fun _q _factor _attempt ↦ probe }
  cases htry : cantorZassenhausOddAttemptWith M D q probes g attempt with
  | none =>
      simp [probes, htry] at htrial
  | some splitChildren =>
      simp [probes, htry] at htrial
      subst children
      refine ⟨?_, ?_, ?_⟩
      · simpa using cantorZassenhausOddAttemptWith_size_ge_two M D q probes htry
      · intro child hchild
        have hproper := cantorZassenhausOddAttemptWith_child_proper M D q probes htry hchild
        unfold isNontrivialProperChild at hproper
        simp at hproper
        have hnormSizeLe : (CPolynomial.monicNormalize g).val.size ≤ g.val.size :=
          monicNormalize_size_le_self g
        exact ⟨hproper.1.1, hproper.1.2, by omega,
          cantorZassenhausOddAttemptWith_child_dvd_input M D q probes htry hchild⟩
      · intro a hroot
        exact cantorZassenhausOddAttemptWith_root_preserved M D q probes htry hroot

/--
Model predicate for the finite-field counting argument behind one odd-field
Cantor-Zassenhaus trial.
-/
def OddSplitTrialHalfSuccessModel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempt : Nat) : Prop :=
  (2 : ℝ≥0∞)⁻¹ ≤
    trialSuccessProbability
      (oddSplitTrialPMF M D enumeration.toFieldEnumeration q
        (CPolynomial.natDegree g) g attempt)

/--
For a squarefree finite-field root product over an odd field, one uniform
Cantor-Zassenhaus trial succeeds with probability at least `1 / 2`.
-/
theorem oddSplitTrial_success_probability_ge_half {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempt : Nat)
    (hvalid : lasVegasSplitterInput q g)
    (hodd : q % 2 = 1)
    (hdegree : 2 ≤ CPolynomial.natDegree g)
    (hmodel : lasVegasSplitterInput q g →
      q % 2 = 1 →
      2 ≤ CPolynomial.natDegree g →
        OddSplitTrialHalfSuccessModel M D enumeration g attempt) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (oddSplitTrialPMF M D enumeration.toFieldEnumeration q
          (CPolynomial.natDegree g) g attempt) := by
  exact hmodel hvalid hodd hdegree

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

private theorem trialFailureProbability_eq_failed_mass {F : Type*} [Zero F]
    (dist : PMF (TrialResult F)) :
    eventProbability dist {trial | ¬ trial.IsSuccess} = dist TrialResult.failed := by
  rw [eventProbability, ← PMF.toOuterMeasure_apply_singleton dist TrialResult.failed]
  congr
  ext trial
  cases trial with
  | split children =>
      constructor
      · intro h
        exact (h trivial).elim
      · intro h
        cases h
  | failed =>
      constructor
      · intro _h
        rfl
      · intro _h hfalse
        exact hfalse

private theorem trialSuccessProbability_add_failed_mass {F : Type*} [Zero F]
    (dist : PMF (TrialResult F)) :
    dist TrialResult.failed + trialSuccessProbability dist = 1 := by
  rw [trialSuccessProbability, eventProbability, PMF.toOuterMeasure_apply]
  trans dist TrialResult.failed + ∑' trial, if trial = TrialResult.failed then 0 else dist trial
  · congr 1
    apply tsum_congr
    intro trial
    cases trial <;> simp [TrialResult.IsSuccess]
  · rw [← ENNReal.tsum_eq_add_tsum_ite
        (f := fun trial : TrialResult F ↦ dist trial) TrialResult.failed]
    exact dist.tsum_coe

private theorem trialFailureProbability_le_half_of_success {F : Type*} [Zero F]
    (dist : PMF (TrialResult F))
    (hsuccess : (2 : ℝ≥0∞)⁻¹ ≤ trialSuccessProbability dist) :
    eventProbability dist {trial | ¬ trial.IsSuccess} ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [trialFailureProbability_eq_failed_mass]
  have htotal := trialSuccessProbability_add_failed_mass dist
  have hsum_le : dist TrialResult.failed + (2 : ℝ≥0∞)⁻¹ ≤ 1 := by
    rw [← htotal]
    exact add_le_add le_rfl hsuccess
  simpa [ENNReal.one_sub_inv_two] using
    ENNReal.le_sub_of_add_le_right (by simp : (2 : ℝ≥0∞)⁻¹ ≠ ∞) hsum_le

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
Binomial-tail expression used by the planned full-recursion fallback bound.
`Finset.range (degree - 1)` indexes `0, ..., degree - 2`.
-/
noncomputable def binomialFallbackTail (attempts degree : Nat) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ attempts *
    ((Finset.range (degree - 1)).sum fun j ↦ (Nat.choose attempts j : ℝ≥0∞))

/-- A cutoff meets the binomial-tail target for field cardinality `q`. -/
def binomialTailCutoffPredicate (q degree attempts : Nat) : Prop :=
  binomialFallbackTail attempts degree ≤ (q : ℝ≥0∞)⁻¹

/--
Model predicate for the planned recursive splitter: it packages the future
independence and root-product hypotheses needed for the binomial fallback tail.
-/
def RecursiveFallbackProbabilityModel {Ω : Type*}
    (process : PMF Ω) (fallbackEvent : Set Ω)
    (attempts degree : Nat) : Prop :=
  ∃ badRankEvent : Nat → Set Ω,
    fallbackEvent ⊆ ⋃ j, badRankEvent j ∧
      (∀ j, j ∉ Finset.range (degree - 1) →
        eventProbability process (badRankEvent j) = 0) ∧
        (∀ j, j ∈ Finset.range (degree - 1) →
          eventProbability process (badRankEvent j) ≤
            ((2 : ℝ≥0∞)⁻¹) ^ attempts * (Nat.choose attempts j : ℝ≥0∞))

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
Target theorem for the full recursive splitter: under the independence and
root-product hypotheses represented by the future recursion model, fallback is
bounded by the binomial tail.
-/
theorem recursiveFallback_probability_le_binomialTail {Ω : Type*}
    (process : PMF Ω) (fallbackEvent : Set Ω)
    (attempts degree : Nat)
    (hmodel : RecursiveFallbackProbabilityModel process fallbackEvent attempts degree) :
    eventProbability process fallbackEvent ≤ binomialFallbackTail attempts degree := by
  rcases hmodel with ⟨badRankEvent, hcover, hzero, hbound⟩
  let half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹
  calc
    eventProbability process fallbackEvent
        ≤ eventProbability process (⋃ j, badRankEvent j) := by
          simpa [eventProbability] using process.toOuterMeasure.mono hcover
    _ ≤ ∑' j, eventProbability process (badRankEvent j) := by
          simpa [eventProbability] using
            (MeasureTheory.measure_iUnion_le (μ := process.toOuterMeasure) badRankEvent)
    _ ≤ ∑' j : Nat,
          if j ∈ Finset.range (degree - 1) then
            half ^ attempts * (Nat.choose attempts j : ℝ≥0∞)
          else
            0 := by
          apply ENNReal.tsum_le_tsum
          intro j
          by_cases hj : j ∈ Finset.range (degree - 1)
          · simpa [half, hj] using hbound j hj
          · simp [hj, hzero j hj]
    _ = binomialFallbackTail attempts degree := by
          unfold binomialFallbackTail
          rw [tsum_eq_sum (s := Finset.range (degree - 1))]
          · trans (Finset.range (degree - 1)).sum
                (fun j ↦ half ^ attempts * (Nat.choose attempts j : ℝ≥0∞))
            · apply Finset.sum_congr rfl
              intro j hj
              simp [hj]
            · simp [half, Finset.mul_sum]
          · intro j hj
            simp [hj]

end FiniteField

end Roots

end CPolynomial

end CompPoly
