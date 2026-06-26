/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.OddTrial
import Mathlib.FieldTheory.Finite.Basic

/-!
# Probability Surface for Characteristic-Two Trace Splitting

Probability analysis of the characteristic-two trace split branch under
idealized uniform probes: trace power sums take only the values zero and one,
each trace fiber has exactly half the field, so a uniform probe separates two
distinct roots into different trace fibers with probability at least `1 / 2`
and one trace split attempt succeeds with probability at least `1 / 2`.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/--
Probability-facing model for the characteristic-two trace splitter: the trace
context has base prime two and its cardinality matches both the uniform
enumeration size and the field cardinality.
-/
structure EvenTraceUniformFieldModel (F : Type*) (q : Nat)
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : UniformFieldEnumeration F q) : Prop where
  p_eq : traceCtx.p = 2
  q_eq : traceCtx.q = q
  card_eq : Fintype.card F = q

/-- Trace power sums square to themselves over a binary field. -/
private theorem tracePowerSum_mul_self {F : Type*} [Field F] [Fintype F]
    {k : Nat} (hcard : Fintype.card F = 2 ^ k) (hchar : ringChar F = 2) (x : F) :
    tracePowerSum 2 k x * tracePowerSum 2 k x = tracePowerSum 2 k x := by
  haveI : CharP F 2 := hchar ▸ ringChar.charP F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [tracePowerSum_eq_sum_range]
  have hsq : (∑ i ∈ Finset.range k, x ^ 2 ^ i) * (∑ i ∈ Finset.range k, x ^ 2 ^ i) =
      ∑ i ∈ Finset.range k, x ^ 2 ^ (i + 1) := by
    rw [← _root_.pow_two, sum_pow_char]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [← pow_mul, pow_succ, Nat.mul_comm (2 ^ i) 2, pow_mul]
  rw [hsq]
  have hfrob : x ^ 2 ^ k = x := by
    have h := FiniteField.pow_card x
    rwa [hcard] at h
  have h1 : (∑ i ∈ Finset.range k, x ^ 2 ^ (i + 1)) + x ^ 2 ^ 0 =
      (∑ i ∈ Finset.range k, x ^ 2 ^ i) + x ^ 2 ^ k := by
    rw [← Finset.sum_range_succ' (fun i ↦ x ^ 2 ^ i) k, Finset.sum_range_succ]
  rw [pow_zero, pow_one, hfrob] at h1
  exact add_right_cancel h1

/-- Trace power sums over a binary field take only the values zero and one. -/
theorem tracePowerSum_eq_zero_or_one {F : Type*} [Field F] [Fintype F]
    {k : Nat} (hcard : Fintype.card F = 2 ^ k) (hchar : ringChar F = 2) (x : F) :
    tracePowerSum 2 k x = 0 ∨ tracePowerSum 2 k x = 1 := by
  have hself := tracePowerSum_mul_self hcard hchar x
  have hsplit : tracePowerSum 2 k x * (tracePowerSum 2 k x - 1) = 0 := by
    rw [_root_.mul_sub, hself, MulOneClass.mul_one, sub_self]
  rcases mul_eq_zero.mp hsplit with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The polynomial whose roots form a trace fiber. -/
private noncomputable def traceFiberPoly {F : Type*} [Field F] (k : Nat) (c : F) :
    Polynomial F :=
  (∑ i ∈ Finset.range k, (Polynomial.X : Polynomial F) ^ 2 ^ i) - Polynomial.C c

private theorem eval_traceFiberPoly {F : Type*} [Field F] (k : Nat) (c y : F) :
    (traceFiberPoly k c).eval y = tracePowerSum 2 k y - c := by
  unfold traceFiberPoly
  rw [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_C,
    tracePowerSum_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Polynomial.eval_pow, Polynomial.eval_X]

private theorem traceFiberPoly_natDegree {F : Type*} [Field F]
    {k : Nat} (hk : 1 ≤ k) (c : F) :
    (traceFiberPoly k c).natDegree = 2 ^ (k - 1) := by
  unfold traceFiberPoly
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have hre : (∑ i ∈ Finset.range k', (Polynomial.X : Polynomial F) ^ 2 ^ i) +
      (Polynomial.X : Polynomial F) ^ 2 ^ k' - Polynomial.C c =
      (Polynomial.X : Polynomial F) ^ 2 ^ k' +
        ((∑ i ∈ Finset.range k', (Polynomial.X : Polynomial F) ^ 2 ^ i) -
          Polynomial.C c) := by
    ring
  have hpos : 0 < 2 ^ k' := Nat.two_pow_pos k'
  have hsmall : ((∑ i ∈ Finset.range k', (Polynomial.X : Polynomial F) ^ 2 ^ i) -
      Polynomial.C c).natDegree < 2 ^ k' := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
    apply max_lt
    · refine lt_of_le_of_lt
        (Polynomial.natDegree_sum_le_of_forall_le (n := 2 ^ k' - 1) _ _
          fun i hi ↦ ?_) ?_
      · show ((Polynomial.X : Polynomial F) ^ 2 ^ i).natDegree ≤ 2 ^ k' - 1
        rw [Polynomial.natDegree_X_pow]
        have hlt : 2 ^ i < 2 ^ k' :=
          Nat.pow_lt_pow_right (by omega) (Finset.mem_range.mp hi)
        omega
      · omega
    · rw [Polynomial.natDegree_C]
      exact hpos
  rw [hre, Polynomial.natDegree_add_eq_left_of_natDegree_lt
    (by rw [Polynomial.natDegree_X_pow]; exact hsmall), Polynomial.natDegree_X_pow]
  simp

/-- Every trace fiber contains at most half the field. -/
private theorem card_tracePowerSum_fiber_le {F : Type*} [Field F] [Fintype F]
    {k : Nat} (hk : 1 ≤ k) (c : F) :
    (Finset.univ.filter fun y : F ↦ tracePowerSum 2 k y = c).card ≤ 2 ^ (k - 1) := by
  have hpos : 0 < 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
  have hne : traceFiberPoly (F := F) k c ≠ 0 := by
    intro h0
    have hdeg := traceFiberPoly_natDegree (F := F) hk c
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  calc (Finset.univ.filter fun y : F ↦ tracePowerSum 2 k y = c).card
      ≤ (traceFiberPoly (F := F) k c).roots.toFinset.card := by
        apply Finset.card_le_card
        intro y hy
        rw [Multiset.mem_toFinset, Polynomial.mem_roots']
        refine ⟨hne, ?_⟩
        show (traceFiberPoly (F := F) k c).eval y = 0
        rw [eval_traceFiberPoly, (Finset.mem_filter.mp hy).2, sub_self]
    _ ≤ Multiset.card (traceFiberPoly (F := F) k c).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (traceFiberPoly (F := F) k c).natDegree := Polynomial.card_roots' _
    _ = 2 ^ (k - 1) := traceFiberPoly_natDegree hk c

/--
Two independent uniform field values land in different trace fibers with
probability at least `1 / 2`.
-/
theorem tracePowerSum_pair_separated_probability_ge_half {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q k : Nat} (enumeration : UniformFieldEnumeration F q)
    (hcard : Fintype.card F = q) (hq : q = 2 ^ k) (hk : 1 ≤ k) :
    (2 : ℝ≥0∞)⁻¹ ≤
      eventProbability
        ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind
          fun x ↦ (uniformFieldElementPMF enumeration.toFieldEnumeration).map
            fun y ↦ (x, y))
        {xy : F × F | tracePowerSum 2 k xy.1 ≠ tracePowerSum 2 k xy.2} := by
  apply uniformPair_separated_probability_ge_half_of_fiber_card_le enumeration
    (fun x ↦ tracePowerSum 2 k x) hcard (m := 2 ^ (k - 1))
  · intro x
    refine ⟨Finset.univ.filter fun y : F ↦ tracePowerSum 2 k y = tracePowerSum 2 k x,
      fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩, ?_⟩
    exact card_tracePowerSum_fiber_le hk (tracePowerSum 2 k x)
  · have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ, Nat.mul_comm]
    omega

/-- One characteristic-two trace split trial under a uniform probe distribution. -/
noncomputable def evenTraceTrialPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempt : Nat) :
    PMF (TrialResult F) :=
  (uniformProbePMF enumeration coefficientCount).map fun h ↦
    match cantorZassenhausEvenTraceAttemptWith M D traceCtx q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g attempt with
    | some children => TrialResult.split children
    | none => TrialResult.failed

/--
Uniform probe polynomials make one characteristic-two trace split attempt
succeed with probability at least `1 / 2`: probe values at two distinct roots
are an independent uniform pair, the pair lands in different trace fibers with
probability at least `1 / 2`, and trace-separated probes force the executable
attempt to succeed.
-/
theorem evenTraceTrial_success_probability_ge_half_of_two_le {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (coefficientCount attempt : Nat)
    (hcount : 2 ≤ coefficientCount)
    (hfield : EvenTraceUniformFieldModel F q traceCtx enumeration)
    (hroots : HasTwoDistinctRoots g)
    (hg : g ≠ 0) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (evenTraceTrialPMF M D traceCtx enumeration.toFieldEnumeration q
          coefficientCount g attempt) := by
  obtain ⟨a, b, hab, hra, hrb⟩ := hroots
  have hq : q = 2 ^ traceCtx.k := by
    rw [← hfield.q_eq, traceCtx.q_eq, hfield.p_eq]
  have hq2 : 2 ≤ q := by
    have hlt := Fintype.one_lt_card (α := F)
    have hcard := hfield.card_eq
    omega
  have hk : 1 ≤ traceCtx.k := by
    rcases Nat.eq_zero_or_pos traceCtx.k with hk0 | hk1
    · rw [hk0, pow_zero] at hq
      omega
    · exact hk1
  have hcard2 : Fintype.card F = 2 ^ traceCtx.k := by
    rw [hfield.card_eq, hq]
  have hchar : ringChar F = 2 := by
    apply FiniteField.even_card_iff_char_two.mpr
    rw [hcard2]
    have hdvd : (2 : Nat) ∣ 2 ^ traceCtx.k := dvd_pow_self 2 (by omega)
    omega
  have hzero_one := fun x : F ↦ tracePowerSum_eq_zero_or_one hcard2 hchar x
  have hpush_eq := uniformProbePMF_map_eval_pair enumeration coefficientCount hab hcount
  rw [trialSuccessProbability, eventProbability, evenTraceTrialPMF,
    PMF.toOuterMeasure_map_apply]
  have hsubset : {h : CPolynomial F |
      tracePowerSum 2 traceCtx.k (CPolynomial.eval a h) ≠
        tracePowerSum 2 traceCtx.k (CPolynomial.eval b h)} ⊆
      (fun h : CPolynomial F ↦
        match cantorZassenhausEvenTraceAttemptWith M D traceCtx q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g attempt with
        | some children => TrialResult.split children
        | none => TrialResult.failed) ⁻¹' {trial | trial.IsSuccess} := by
    intro h hsep
    rw [Set.mem_setOf_eq] at hsep
    have hsucc : ∃ children,
        cantorZassenhausEvenTraceAttemptWith M D traceCtx q
          ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F)
          g attempt = some children := by
      rcases hzero_one (CPolynomial.eval a h) with hA | hA <;>
        rcases hzero_one (CPolynomial.eval b h) with hB | hB
      · exact absurd (hA.trans hB.symm) hsep
      · exact cantorZassenhausEvenTraceAttemptWith_success_of_trace_separated
          M D traceCtx q attempt hg hra hrb
          (by rw [hfield.p_eq]; exact hA)
          (by rw [hfield.p_eq, hB]; exact one_ne_zero)
      · exact cantorZassenhausEvenTraceAttemptWith_success_of_trace_separated
          M D traceCtx q attempt hg hrb hra
          (by rw [hfield.p_eq]; exact hB)
          (by rw [hfield.p_eq, hA]; exact one_ne_zero)
      · exact absurd (hA.trans hB.symm) hsep
    obtain ⟨children, hchildren⟩ := hsucc
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hchildren]
    exact trivial
  have hpre : ((fun h : CPolynomial F ↦
      (CPolynomial.eval a h, CPolynomial.eval b h)) ⁻¹'
        {xy : F × F | tracePowerSum 2 traceCtx.k xy.1 ≠
          tracePowerSum 2 traceCtx.k xy.2}) =
      {h : CPolynomial F |
        tracePowerSum 2 traceCtx.k (CPolynomial.eval a h) ≠
          tracePowerSum 2 traceCtx.k (CPolynomial.eval b h)} := rfl
  have hge : (2 : ℝ≥0∞)⁻¹ ≤
      (uniformProbePMF enumeration.toFieldEnumeration
        coefficientCount).toOuterMeasure
        {h : CPolynomial F |
          tracePowerSum 2 traceCtx.k (CPolynomial.eval a h) ≠
            tracePowerSum 2 traceCtx.k (CPolynomial.eval b h)} := by
    rw [← hpre, ← PMF.toOuterMeasure_map_apply, hpush_eq]
    exact tracePowerSum_pair_separated_probability_ge_half enumeration
      hfield.card_eq hq hk
  exact le_trans hge ((uniformProbePMF enumeration.toFieldEnumeration
    coefficientCount).toOuterMeasure.mono hsubset)

/--
Uniform probe polynomials make one characteristic-two trace split attempt
succeed with probability at least `1 / 2`.
-/
theorem evenTraceTrial_success_probability_ge_half {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempt : Nat)
    (hfield : EvenTraceUniformFieldModel F q traceCtx enumeration)
    (hroots : HasTwoDistinctRoots g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (evenTraceTrialPMF M D traceCtx enumeration.toFieldEnumeration q
          (CPolynomial.natDegree g) g attempt) := by
  have hg : g ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    have hnat : CPolynomial.natDegree (0 : CPolynomial F) = 0 := rfl
    omega
  exact evenTraceTrial_success_probability_ge_half_of_two_le M D traceCtx enumeration g
    (CPolynomial.natDegree g) attempt hdegree hfield hroots hg

/-- Independent repeated trace split trials for one unresolved factor. -/
noncomputable def repeatedEvenTraceTrialsPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) :
    Nat → Nat → PMF (List (TrialResult F))
  | 0, _offset => pure []
  | attempts + 1, offset => do
      let trial ← evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g offset
      let trials ← repeatedEvenTraceTrialsPMF M D traceCtx enumeration q coefficientCount g
        attempts (offset + 1)
      pure (trial :: trials)

/-- Probability that the trace branch reaches fallback after all attempts fail. -/
noncomputable def fallbackAfterEvenTraceAttemptsProbability {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat) :
    ℝ≥0∞ :=
  eventProbability
    (repeatedEvenTraceTrialsPMF M D traceCtx enumeration q coefficientCount g
      attempts offset)
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

private theorem fallbackAfterEvenTraceAttemptsProbability_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat) :
    fallbackAfterEvenTraceAttemptsProbability M D traceCtx enumeration q coefficientCount g
        (attempts + 1) offset =
      eventProbability
          (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g offset)
          {trial | ¬ trial.IsSuccess} *
        fallbackAfterEvenTraceAttemptsProbability M D traceCtx enumeration q coefficientCount
          g attempts (offset + 1) := by
  change (PMF.bind (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g offset)
      (fun trial ↦ PMF.map (List.cons trial)
        (repeatedEvenTraceTrialsPMF M D traceCtx enumeration q coefficientCount g attempts
          (offset + 1)))).toOuterMeasure
        {trials | TrialResult.allFailed trials} =
    (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g offset).toOuterMeasure
      {trial | ¬ trial.IsSuccess} *
      (repeatedEvenTraceTrialsPMF M D traceCtx enumeration q coefficientCount g attempts
        (offset + 1)).toOuterMeasure
        {trials | TrialResult.allFailed trials}
  rw [PMF.toOuterMeasure_bind_apply]
  trans (∑' trial, (if ¬ trial.IsSuccess then
        (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g offset) trial
      else 0) *
        (repeatedEvenTraceTrialsPMF M D traceCtx enumeration q coefficientCount g attempts
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
If every trace trial succeeds with probability at least `1 / 2`, the
probability of using fallback after `attempts` trials is at most `2^-attempts`.
-/
theorem fallbackAfterEvenTraceAttempts_probability_le_geometric {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat)
    (hstep : ∀ i, i < attempts →
      (2 : ℝ≥0∞)⁻¹ ≤
        trialSuccessProbability
          (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g (offset + i))) :
    fallbackAfterEvenTraceAttemptsProbability M D traceCtx enumeration q coefficientCount g
        attempts offset ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  induction attempts generalizing offset with
  | zero =>
      rw [fallbackAfterEvenTraceAttemptsProbability, eventProbability,
        repeatedEvenTraceTrialsPMF]
      exact le_trans
        ((pure ([] : List (TrialResult F)) : PMF (List (TrialResult F))).toOuterMeasure.mono
          (Set.subset_univ _))
        (by simp [PMF.toOuterMeasure_apply])
  | succ attempts ih =>
      rw [fallbackAfterEvenTraceAttemptsProbability_succ]
      let half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹
      have hfail : eventProbability
          (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g offset)
          {trial | ¬ trial.IsSuccess} ≤ half := by
        exact trialFailureProbability_le_half_of_success _ (hstep 0 (by omega))
      have hrest :
          fallbackAfterEvenTraceAttemptsProbability M D traceCtx enumeration q
              coefficientCount g attempts (offset + 1) ≤
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
For a squarefree root product over a binary field, the uniform probe source
reaches enumeration fallback after `attempts` trace trials with probability at
most `2^-attempts`.
-/
theorem fallbackAfterEvenTraceAttempts_probability_le_geometric_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts offset : Nat)
    (hfield : EvenTraceUniformFieldModel F q traceCtx enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    fallbackAfterEvenTraceAttemptsProbability M D traceCtx
        enumeration.toFieldEnumeration q (CPolynomial.natDegree g) g attempts offset ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  apply fallbackAfterEvenTraceAttempts_probability_le_geometric
  intro i _hi
  exact evenTraceTrial_success_probability_ge_half M D traceCtx enumeration g (offset + i)
    hfield (hrootProduct.hasTwoDistinctRoots hdegree) hdegree

set_option maxHeartbeats 1600000 in
/--
Bridge to the executable trace retry loop: the deterministic
`tryEvenTraceSplitAttemptsWith`, driven by a probe table whose entries are
sampled independently and uniformly, exhausts all attempts with probability at
most `2 ^ -attempts`.
-/
theorem tryEvenTraceSplitAttemptsWith_uniformTable_none_le_geometric {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat) (g : CPolynomial F)
    (hstep : (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g 0)) :
    ∀ attempts : Nat,
      eventProbability (uniformProbeTablePMF enumeration coefficientCount attempts)
        {table : List (CPolynomial F) |
          tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
            attempts 0 = none} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  have hfailset : ((fun h : CPolynomial F ↦
      (match cantorZassenhausEvenTraceAttemptWith M D traceCtx q
          ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 with
        | some children => TrialResult.split children
        | none => TrialResult.failed)) ⁻¹'
        {trial : TrialResult F | ¬ trial.IsSuccess}) =
      {h : CPolynomial F | cantorZassenhausEvenTraceAttemptWith M D traceCtx q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none} := by
    ext h
    cases h0 : cantorZassenhausEvenTraceAttemptWith M D traceCtx q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 <;>
      simp [h0, TrialResult.IsSuccess]
  have hfail : (uniformProbePMF enumeration coefficientCount).toOuterMeasure
      {h : CPolynomial F | cantorZassenhausEvenTraceAttemptWith M D traceCtx q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none} ≤
      (2 : ℝ≥0∞)⁻¹ := by
    rw [← hfailset, ← PMF.toOuterMeasure_map_apply]
    have hhalf := trialFailureProbability_le_half_of_success
      (evenTraceTrialPMF M D traceCtx enumeration q coefficientCount g 0) hstep
    rw [eventProbability, evenTraceTrialPMF] at hhalf
    exact hhalf
  intro attempts
  induction attempts with
  | zero =>
      rw [eventProbability, uniformProbeTablePMF, PMF.toOuterMeasure_pure_apply,
        if_pos (by
          rw [Set.mem_setOf_eq]
          unfold tryEvenTraceSplitAttemptsWith
          rfl)]
      simp
  | succ attempts ih =>
      rw [eventProbability, uniformProbeTablePMF, PMF.toOuterMeasure_bind_apply]
      have hsection : ∀ (h : CPolynomial F) (rest : List (CPolynomial F)),
          (tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily (h :: rest)) g
            (attempts + 1) 0 = none) ↔
          (cantorZassenhausEvenTraceAttemptWith M D traceCtx q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none ∧
            tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily rest) g
              attempts 0 = none) := by
        intro h rest
        unfold tryEvenTraceSplitAttemptsWith
        rw [cantorZassenhausEvenTraceAttemptWith_probe_congr M D traceCtx q (g := g)
          (p2 := ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F))
          (a2 := 0) (by simp [tableProbeFamily])]
        rw [tryEvenTraceSplitAttemptsWith_probe_congr M D traceCtx q
          (p1 := tableProbeFamily (h :: rest)) (p2 := tableProbeFamily rest) (g := g)
          attempts (0 + 1) 0 (by
            intro i _hi
            simp [tableProbeFamily, Nat.add_comm])]
        cases h0 : cantorZassenhausEvenTraceAttemptWith M D traceCtx q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 with
        | some c => simp
        | none =>
            rw [← tryEvenTraceSplitAttemptsWith.eq_def]
            simp
      have hweight : ∀ h : CPolynomial F,
          ((uniformProbeTablePMF enumeration coefficientCount attempts).map
            (List.cons h)).toOuterMeasure
            {table : List (CPolynomial F) |
              tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
                (attempts + 1) 0 = none} =
          if cantorZassenhausEvenTraceAttemptWith M D traceCtx q
              ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none then
            (uniformProbeTablePMF enumeration coefficientCount attempts).toOuterMeasure
              {table : List (CPolynomial F) |
                tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
                  attempts 0 = none}
          else 0 := by
        intro h
        rw [PMF.toOuterMeasure_map_apply]
        by_cases h0 : cantorZassenhausEvenTraceAttemptWith M D traceCtx q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none
        · rw [if_pos h0]
          congr 1
          ext rest
          rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, hsection h rest]
          simp [h0]
        · rw [if_neg h0]
          have hempty : (List.cons h ⁻¹'
              {table : List (CPolynomial F) |
                tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
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
                  tryEvenTraceSplitAttemptsWith M D traceCtx q (tableProbeFamily table) g
                    (attempts + 1) 0 = none})
          ≤ ∑' h : CPolynomial F,
              (if cantorZassenhausEvenTraceAttemptWith M D traceCtx q
                  ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none
                then uniformProbePMF enumeration coefficientCount h else 0) *
                ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
            apply ENNReal.tsum_le_tsum
            intro h
            rw [hweight h]
            by_cases h0 : cantorZassenhausEvenTraceAttemptWith M D traceCtx q
                ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g 0 = none
            · rw [if_pos h0, if_pos h0]
              exact mul_le_mul' le_rfl (by
                have := ih
                rwa [eventProbability] at this)
            · rw [if_neg h0, if_neg h0]
              simp
        _ = (uniformProbePMF enumeration coefficientCount).toOuterMeasure
              {h : CPolynomial F | cantorZassenhausEvenTraceAttemptWith M D traceCtx q
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

end FiniteField

end Roots

end CPolynomial

end CompPoly
