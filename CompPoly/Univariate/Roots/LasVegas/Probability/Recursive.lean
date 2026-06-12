/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.EvenTrace
import CompPoly.Univariate.Roots.LasVegas.Probability.OddTrial

/-!
# Recursive Fallback Analysis for Las Vegas Splitting

The abstract binomial-tail bound for recursive fallback, together with the
multi-factor splitting process that witnesses it: the process tracks the full
stack of unresolved factors, gives every splittable factor its own batch of
independent uniform probes, and records which factors fell back to enumeration.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

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

theorem toOuterMeasure_apply_le_one {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  calc (∑' a, s.indicator (⇑p) a)
      ≤ ∑' a, p a := ENNReal.tsum_le_tsum fun a ↦ Set.indicator_le_self s (⇑p) a
    _ = 1 := p.tsum_coe

/-- First successful split among independent trials, or `none` after exhaustion. -/
noncomputable def firstSuccessPMF {F : Type*} [Zero F]
    (trial : Nat → PMF (TrialResult F)) :
    Nat → Nat → PMF (Option (Array (CPolynomial F)))
  | 0, _offset => PMF.pure none
  | attempts + 1, offset =>
      (trial offset).bind fun
        | TrialResult.split children => PMF.pure (some children)
        | TrialResult.failed => firstSuccessPMF trial attempts (offset + 1)

/-- Trials that succeed at rate one half are all survived with probability
at most `2 ^ -attempts`. -/
theorem firstSuccessPMF_apply_none_le_geometric {F : Type*} [Zero F]
    (trial : Nat → PMF (TrialResult F)) :
    ∀ attempts offset,
      (∀ i, i < attempts →
        (2 : ℝ≥0∞)⁻¹ ≤ trialSuccessProbability (trial (offset + i))) →
      (firstSuccessPMF trial attempts offset) none ≤ ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset _hstep
      rw [firstSuccessPMF]
      simp
  | succ attempts ih =>
      intro offset hstep
      rw [firstSuccessPMF, PMF.bind_apply]
      trans ((trial offset) TrialResult.failed *
        (firstSuccessPMF trial attempts (offset + 1)) none)
      · refine le_of_eq (tsum_eq_single TrialResult.failed fun t ht ↦ ?_)
        cases t with
        | split children => simp
        | failed => exact absurd rfl ht
      · have hfail : (trial offset) TrialResult.failed ≤ (2 : ℝ≥0∞)⁻¹ := by
          rw [← trialFailureProbability_eq_failed_mass]
          exact trialFailureProbability_le_half_of_success _ (hstep 0 (by omega))
        have hrest := ih (offset + 1) (by
          intro i hi
          have h := hstep (i + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
        refine le_trans (mul_le_mul' hfail hrest) (le_of_eq ?_)
        rw [pow_succ, _root_.mul_comm]

/-- A successful batch outcome lies in the support of some individual trial. -/
theorem firstSuccessPMF_support_some {F : Type*} [Zero F]
    (trial : Nat → PMF (TrialResult F)) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      some children ∈ (firstSuccessPMF trial attempts offset).support →
      ∃ attempt, TrialResult.split children ∈ (trial attempt).support := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children hmem
      rw [firstSuccessPMF] at hmem
      have heq := (PMF.mem_support_pure_iff _ _).mp hmem
      exact absurd heq (by simp)
  | succ attempts ih =>
      intro offset children hmem
      rw [firstSuccessPMF, PMF.mem_support_bind_iff] at hmem
      obtain ⟨t, ht, hmem2⟩ := hmem
      cases t with
      | split c =>
          have hc : some children = some c := (PMF.mem_support_pure_iff _ _).mp hmem2
          have hceq : children = c := by
            injection hc with hc'
          rw [← hceq] at ht
          exact ⟨offset, ht⟩
      | failed => exact ih (offset + 1) hmem2

/--
Facts a split trial guarantees about successful children: at least two of them,
each a nonzero nonconstant divisor of the parent, with total split work
strictly below the parent's.
-/
def IsSplitStep {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (g : CPolynomial F) (children : Array (CPolynomial F)) : Prop :=
  2 ≤ children.size ∧
    (∀ child ∈ children.toList,
      child ≠ 0 ∧ child.toPoly ∣ g.toPoly ∧ 1 ≤ child.toPoly.natDegree) ∧
    stackWork children.toList ≤ splitWork g - 1

/-- Number of splits a stack of unresolved factors can still require. -/
noncomputable def stackSplitBudget {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    List (CPolynomial F) → Nat
  | [] => 0
  | g :: stack => (g.toPoly.natDegree - 1) + stackSplitBudget stack

theorem stackSplitBudget_append {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (xs ys : List (CPolynomial F)) :
    stackSplitBudget (xs ++ ys) = stackSplitBudget xs + stackSplitBudget ys := by
  induction xs with
  | nil => simp [stackSplitBudget]
  | cons g xs ih =>
      simp only [List.cons_append, stackSplitBudget, ih]
      omega

theorem stackWork_eq_two_mul_budget_add_length {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (l : List (CPolynomial F))
    (hpos : ∀ g ∈ l, 1 ≤ g.toPoly.natDegree) :
    stackWork l = 2 * stackSplitBudget l + l.length := by
  induction l with
  | nil => simp [stackWork, stackSplitBudget]
  | cons g l ih =>
      have hg := hpos g (by simp)
      have hl := ih fun x hx ↦ hpos x (by simp [hx])
      simp only [stackWork, stackSplitBudget, splitWork, List.length_cons]
      omega

/--
Multi-factor Las Vegas splitting process for an abstract per-factor trial
family.

The stack of unresolved factors is processed sequentially. Every factor of
degree at least two receives its own batch of `attempts` independent trials;
the resulting trace records, in processing order, whether each such factor
fell back to enumeration (`true`) or split into children that are pushed back
onto the stack (`false`). This is the idealized-probe model of
`lasVegasSplitLoopWith`, which retries each unresolved factor up to the
configured cutoff before enumerating it.
-/
noncomputable def recursiveSplitProcessPMF {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (trial : CPolynomial F → Nat → PMF (TrialResult F)) (attempts : Nat) :
    Nat → List (CPolynomial F) → PMF (List Bool)
  | 0, _stack => PMF.pure []
  | _fuel + 1, [] => PMF.pure []
  | fuel + 1, g :: stack =>
      if CPolynomial.natDegree g < 2 then
        recursiveSplitProcessPMF trial attempts fuel stack
      else
        (firstSuccessPMF (trial g) attempts 0).bind fun
          | none =>
              (recursiveSplitProcessPMF trial attempts fuel stack).map (List.cons true)
          | some children =>
              (recursiveSplitProcessPMF trial attempts fuel
                (children.toList ++ stack)).map (List.cons false)

/-- Process traces never exceed the split budget of the initial stack. -/
theorem recursiveSplitProcessPMF_support_length {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (trial : CPolynomial F → Nat → PMF (TrialResult F)) (attempts : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (attempt : Nat) (children : Array (CPolynomial F)),
        TrialResult.split children ∈ (trial g attempt).support →
        IsSplitStep g children) :
    ∀ fuel (stack : List (CPolynomial F)) {tr2 : List Bool},
      tr2 ∈ (recursiveSplitProcessPMF trial attempts fuel stack).support →
      tr2.length ≤ stackSplitBudget stack := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack tr2 hmem
      rw [recursiveSplitProcessPMF] at hmem
      have heq := (PMF.mem_support_pure_iff _ _).mp hmem
      subst heq
      simp
  | succ fuel ih =>
      intro stack tr2 hmem
      cases stack with
      | nil =>
          rw [recursiveSplitProcessPMF] at hmem
          have heq := (PMF.mem_support_pure_iff _ _).mp hmem
          subst heq
          simp
      | cons g stack =>
          rw [recursiveSplitProcessPMF] at hmem
          by_cases hdeg : CPolynomial.natDegree g < 2
          · rw [if_pos hdeg] at hmem
            refine le_trans (ih stack hmem) ?_
            simp only [stackSplitBudget]
            omega
          · rw [if_neg hdeg] at hmem
            rw [PMF.mem_support_bind_iff] at hmem
            obtain ⟨o, ho, hmem2⟩ := hmem
            have hdeg2 : 2 ≤ g.toPoly.natDegree := by
              have h := Nat.le_of_not_lt hdeg
              rwa [CPolynomial.natDegree_toPoly] at h
            cases o with
            | none =>
                rw [PMF.mem_support_map_iff] at hmem2
                obtain ⟨tr, htr, heq⟩ := hmem2
                subst heq
                have hlen := ih stack htr
                simp only [stackSplitBudget, List.length_cons]
                omega
            | some children =>
                rw [PMF.mem_support_map_iff] at hmem2
                obtain ⟨tr, htr, heq⟩ := hmem2
                subst heq
                have hlen := ih (children.toList ++ stack) htr
                rw [stackSplitBudget_append] at hlen
                have hg : g ≠ 0 := by
                  intro h0
                  apply hdeg
                  rw [h0]
                  have hzero : CPolynomial.natDegree (0 : CPolynomial F) = 0 := rfl
                  omega
                obtain ⟨att, hmemt⟩ := firstSuccessPMF_support_some (trial g) attempts 0 ho
                obtain ⟨hsize2, hchild, hwork⟩ := hsplit g hg att children hmemt
                have hsw := stackWork_eq_two_mul_budget_add_length children.toList
                  fun c hc ↦ (hchild c hc).2.2
                have hlen2 : children.toList.length = children.size := by simp
                simp only [splitWork] at hwork
                simp only [stackSplitBudget, List.length_cons]
                omega

/--
Each processed factor falls back with probability at most `2 ^ -attempts`:
the `j`-th entry of the process trace is `true` with at most that probability.
-/
theorem recursiveSplitProcessPMF_rank_le_geometric {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (trial : CPolynomial F → Nat → PMF (TrialResult F)) {q : Nat} (attempts : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (attempt : Nat) (children : Array (CPolynomial F)),
        TrialResult.split children ∈ (trial g attempt).support →
        IsSplitStep g children)
    (hhalf : ∀ (g : CPolynomial F), lasVegasSplitterInput q g →
      2 ≤ CPolynomial.natDegree g → ∀ attempt : Nat,
        (2 : ℝ≥0∞)⁻¹ ≤ trialSuccessProbability (trial g attempt)) :
    ∀ fuel (stack : List (CPolynomial F)) (j : Nat),
      (∀ g ∈ stack, lasVegasSplitterInput q g) →
      eventProbability
        (recursiveSplitProcessPMF trial attempts fuel stack)
        {tr2 : List Bool | tr2[j]? = some true} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack j _hstack
      rw [recursiveSplitProcessPMF, eventProbability, PMF.toOuterMeasure_pure_apply,
        if_neg (by simp)]
      exact zero_le'
  | succ fuel ih =>
      intro stack j hstack
      cases stack with
      | nil =>
          rw [recursiveSplitProcessPMF, eventProbability, PMF.toOuterMeasure_pure_apply,
            if_neg (by simp)]
          exact zero_le'
      | cons g stack =>
          rw [recursiveSplitProcessPMF]
          by_cases hdeg : CPolynomial.natDegree g < 2
          · rw [if_pos hdeg]
            exact ih stack j fun x hx ↦ hstack x (by simp [hx])
          · rw [if_neg hdeg]
            rw [eventProbability, PMF.toOuterMeasure_bind_apply]
            have hvalid := hstack g (by simp)
            have hdeg2 : 2 ≤ CPolynomial.natDegree g := Nat.le_of_not_lt hdeg
            have hnone : (firstSuccessPMF (trial g) attempts 0) none ≤
                ((2 : ℝ≥0∞)⁻¹) ^ attempts :=
              firstSuccessPMF_apply_none_le_geometric (trial g) attempts 0 fun i _hi ↦
                hhalf g hvalid hdeg2 (0 + i)
            cases j with
            | zero =>
                trans ((firstSuccessPMF (trial g) attempts 0) none *
                  ((recursiveSplitProcessPMF trial attempts fuel stack).map
                    (List.cons true)).toOuterMeasure
                    {tr2 : List Bool | tr2[0]? = some true})
                · refine le_of_eq (tsum_eq_single none fun o ho ↦ ?_)
                  cases o with
                  | none => exact absurd rfl ho
                  | some children =>
                      have hzero : ((recursiveSplitProcessPMF trial attempts fuel
                          (children.toList ++ stack)).map (List.cons false)).toOuterMeasure
                          {tr2 : List Bool | tr2[0]? = some true} = 0 := by
                        rw [PMF.toOuterMeasure_map_apply]
                        have hpre : (List.cons false ⁻¹'
                            {tr2 : List Bool | tr2[0]? = some true}) = ∅ := by
                          ext tr
                          simp
                        rw [hpre]
                        simp
                      rw [hzero, MulZeroClass.mul_zero]
                · refine le_trans (mul_le_mul' le_rfl (toOuterMeasure_apply_le_one _ _)) ?_
                  rw [MulOneClass.mul_one]
                  exact hnone
            | succ j' =>
                trans (∑' o : Option (Array (CPolynomial F)),
                  (firstSuccessPMF (trial g) attempts 0) o * ((2 : ℝ≥0∞)⁻¹) ^ attempts)
                · apply ENNReal.tsum_le_tsum
                  intro o
                  by_cases hzero : (firstSuccessPMF (trial g) attempts 0) o = 0
                  · simp [hzero]
                  · apply mul_le_mul' le_rfl
                    cases o with
                    | none =>
                        rw [PMF.toOuterMeasure_map_apply]
                        have hpre : (List.cons true ⁻¹'
                            {tr2 : List Bool | tr2[j' + 1]? = some true}) =
                            {tr2 : List Bool | tr2[j']? = some true} := by
                          ext tr
                          simp
                        rw [hpre]
                        exact ih stack j' fun x hx ↦ hstack x (by simp [hx])
                    | some children =>
                        rw [PMF.toOuterMeasure_map_apply]
                        have hpre : (List.cons false ⁻¹'
                            {tr2 : List Bool | tr2[j' + 1]? = some true}) =
                            {tr2 : List Bool | tr2[j']? = some true} := by
                          ext tr
                          simp
                        rw [hpre]
                        obtain ⟨att, hmemt⟩ := firstSuccessPMF_support_some (trial g)
                          attempts 0 ((PMF.mem_support_iff _ _).mpr hzero)
                        obtain ⟨_hsize2, hchild, _hwork⟩ := hsplit g hvalid.1 att
                          children hmemt
                        apply ih (children.toList ++ stack) j'
                        intro x hx
                        rw [List.mem_append] at hx
                        rcases hx with hx | hx
                        · exact ⟨(hchild x hx).1, (hchild x hx).2.1.trans hvalid.2⟩
                        · exact hstack x (by simp [hx])
                · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, _root_.one_mul]

/-- Trace entries beyond the split budget of the stack never appear. -/
theorem recursiveSplitProcessPMF_rank_eq_zero_of_budget_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (trial : CPolynomial F → Nat → PMF (TrialResult F)) (attempts : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (attempt : Nat) (children : Array (CPolynomial F)),
        TrialResult.split children ∈ (trial g attempt).support →
        IsSplitStep g children)
    (fuel : Nat) (stack : List (CPolynomial F)) {j : Nat}
    (hj : stackSplitBudget stack ≤ j) :
    eventProbability
      (recursiveSplitProcessPMF trial attempts fuel stack)
      {tr2 : List Bool | tr2[j]? = some true} = 0 := by
  rw [eventProbability, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro tr2 hsupp hmem
  have hlen := recursiveSplitProcessPMF_support_length trial attempts hsplit
    fuel stack hsupp
  rw [Set.mem_setOf_eq, List.getElem?_eq_none (l := tr2) (by omega)] at hmem
  simp at hmem

/--
The multi-factor splitting process satisfies the recursive fallback model:
the `j`-th rank event is "the `j`-th processed splittable factor fell back",
there are at most `degree - 1` such factors, and each falls back with
probability at most `2 ^ -attempts ≤ choose attempts j * 2 ^ -attempts`.
-/
theorem recursiveSplitProcessPMF_recursiveFallbackProbabilityModel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (trial : CPolynomial F → Nat → PMF (TrialResult F)) {q : Nat}
    (g : CPolynomial F) (attempts fuel : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (attempt : Nat) (children : Array (CPolynomial F)),
        TrialResult.split children ∈ (trial g attempt).support →
        IsSplitStep g children)
    (hhalf : ∀ (g : CPolynomial F), lasVegasSplitterInput q g →
      2 ≤ CPolynomial.natDegree g → ∀ attempt : Nat,
        (2 : ℝ≥0∞)⁻¹ ≤ trialSuccessProbability (trial g attempt))
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    RecursiveFallbackProbabilityModel
      (recursiveSplitProcessPMF trial attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2}
      attempts (CPolynomial.natDegree g) := by
  refine ⟨fun j ↦ {tr2 : List Bool | tr2[j]? = some true}, ?_, ?_, ?_⟩
  · intro tr2 htr2
    rw [Set.mem_setOf_eq] at htr2
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htr2
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    apply recursiveSplitProcessPMF_rank_eq_zero_of_budget_le trial attempts hsplit
    have hbudget : stackSplitBudget [g] = g.toPoly.natDegree - 1 := by
      simp [stackSplitBudget]
    have hdeg := (CPolynomial.natDegree_toPoly g).symm
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    have hrank := recursiveSplitProcessPMF_rank_le_geometric trial attempts hsplit hhalf
      fuel [g] j (by
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
Generic recursive fallback bound: any per-factor trial family that succeeds at
rate one half on splitter-valid factors keeps the full recursion's fallback
probability below the binomial tail.
-/
theorem recursiveSplitProcessPMF_fallback_probability_le_binomialTail {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (trial : CPolynomial F → Nat → PMF (TrialResult F)) {q : Nat}
    (g : CPolynomial F) (attempts fuel : Nat)
    (hsplit : ∀ (g : CPolynomial F), g ≠ 0 →
      ∀ (attempt : Nat) (children : Array (CPolynomial F)),
        TrialResult.split children ∈ (trial g attempt).support →
        IsSplitStep g children)
    (hhalf : ∀ (g : CPolynomial F), lasVegasSplitterInput q g →
      2 ≤ CPolynomial.natDegree g → ∀ attempt : Nat,
        (2 : ℝ≥0∞)⁻¹ ≤ trialSuccessProbability (trial g attempt))
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (recursiveSplitProcessPMF trial attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) :=
  recursiveFallback_probability_le_binomialTail _ _ _ _
    (recursiveSplitProcessPMF_recursiveFallbackProbabilityModel trial g attempts fuel
      hsplit hhalf hvalid hattempts)

/-- Successful odd split attempts are split steps. -/
theorem cantorZassenhausOddAttemptWith_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} (hg : g ≠ 0)
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children) :
    IsSplitStep g children := by
  refine ⟨cantorZassenhausOddAttemptWith_size_ge_two M D q _ htry, ?_, ?_⟩
  · intro child hchild
    have hproper := cantorZassenhausOddAttemptWith_child_proper M D q _ htry hchild
    have hpos := cantorZassenhausOddAttemptWith_child_normSplitWork_pos M D q _
      htry hg hchild
    have hns : normSplitWork child = splitWork child := normSplitWork_eq_splitWork child
    rw [hns] at hpos
    simp only [splitWork] at hpos
    exact ⟨child_ne_zero_of_proper hproper,
      cantorZassenhausOddAttemptWith_child_dvd_input M D q _ htry hchild, by omega⟩
  · have hwork := cantorZassenhausOddAttemptWith_stackWork_le M D q _ htry hg
    rwa [splitWork_monicNormalize_eq] at hwork

/-- Successful retry-loop results are split steps. -/
theorem tryOddSplitAttemptsWith_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} (hg : g ≠ 0)
    {attempts offset : Nat} {children : Array (CPolynomial F)}
    (htry : tryOddSplitAttemptsWith M D q probes g attempts offset = some children) :
    IsSplitStep g children := by
  obtain ⟨attempt, hatt⟩ :=
    tryOddSplitAttemptsWith_eq_some_exists_attempt M D q probes attempts offset htry
  exact cantorZassenhausOddAttemptWith_isSplitStep M D q probes hg hatt

/-- Successful odd split trials are split steps. -/
theorem oddSplitTrialPMF_support_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q : Nat) {g : CPolynomial F} (hg : g ≠ 0)
    {attempt : Nat} {children : Array (CPolynomial F)}
    (hmem : TrialResult.split children ∈
      (oddSplitTrialPMF M D enumeration q (CPolynomial.natDegree g) g attempt).support) :
    IsSplitStep g children := by
  rw [oddSplitTrialPMF, PMF.mem_support_map_iff] at hmem
  obtain ⟨probe, _hprobe, heq⟩ := hmem
  cases htry : cantorZassenhausOddAttemptWith M D q
      ({ probe := fun _q _factor _attempt ↦ probe } : ProbeFamily F) g attempt with
  | none =>
      simp only [htry] at heq
      exact absurd heq (by simp)
  | some c =>
      simp only [htry] at heq
      have hceq : c = children := by
        injection heq with h
      exact hceq ▸ cantorZassenhausOddAttemptWith_isSplitStep M D q _ hg htry

/-- Successful trace split attempts are split steps. -/
theorem cantorZassenhausEvenTraceAttemptWith_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} (hg : g ≠ 0)
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt =
      some children) :
    IsSplitStep g children := by
  refine ⟨cantorZassenhausEvenTraceAttemptWith_size_ge_two M D traceCtx q _ htry, ?_, ?_⟩
  · intro child hchild
    have hproper := cantorZassenhausEvenTraceAttemptWith_child_proper M D traceCtx q _
      htry hchild
    have hpos := cantorZassenhausEvenTraceAttemptWith_child_normSplitWork_pos
      M D traceCtx q _ htry hg hchild
    have hns : normSplitWork child = splitWork child := normSplitWork_eq_splitWork child
    rw [hns] at hpos
    simp only [splitWork] at hpos
    exact ⟨child_ne_zero_of_proper hproper,
      cantorZassenhausEvenTraceAttemptWith_child_dvd_input M D traceCtx q _
        htry hchild, by omega⟩
  · have hwork := cantorZassenhausEvenTraceAttemptWith_stackWork_le M D traceCtx q _
      htry hg
    rwa [splitWork_monicNormalize_eq] at hwork

/-- Successful trace retry-loop results are split steps. -/
theorem tryEvenTraceSplitAttemptsWith_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} (hg : g ≠ 0)
    {attempts offset : Nat} {children : Array (CPolynomial F)}
    (htry : tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset =
      some children) :
    IsSplitStep g children := by
  obtain ⟨attempt, hatt⟩ :=
    tryEvenTraceSplitAttemptsWith_eq_some_exists_attempt M D traceCtx q probes
      attempts offset htry
  exact cantorZassenhausEvenTraceAttemptWith_isSplitStep M D traceCtx q probes hg hatt

/-- Successful trace split trials are split steps. -/
theorem evenTraceTrialPMF_support_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q : Nat) {g : CPolynomial F} (hg : g ≠ 0)
    {attempt : Nat} {children : Array (CPolynomial F)}
    (hmem : TrialResult.split children ∈
      (evenTraceTrialPMF M D traceCtx enumeration q (CPolynomial.natDegree g)
        g attempt).support) :
    IsSplitStep g children := by
  rw [evenTraceTrialPMF, PMF.mem_support_map_iff] at hmem
  obtain ⟨probe, _hprobe, heq⟩ := hmem
  cases htry : cantorZassenhausEvenTraceAttemptWith M D traceCtx q
      ({ probe := fun _q _factor _attempt ↦ probe } : ProbeFamily F) g attempt with
  | none =>
      simp only [htry] at heq
      exact absurd heq (by simp)
  | some c =>
      simp only [htry] at heq
      have hceq : c = children := by
        injection heq with h
      exact hceq ▸ cantorZassenhausEvenTraceAttemptWith_isSplitStep M D traceCtx q _
        hg htry

/-- Multi-factor odd Cantor-Zassenhaus splitting under uniform probes. -/
noncomputable def recursiveOddSplitProcessPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q attempts : Nat) :
    Nat → List (CPolynomial F) → PMF (List Bool) :=
  recursiveSplitProcessPMF
    (fun g attempt ↦ oddSplitTrialPMF M D enumeration q (CPolynomial.natDegree g) g attempt)
    attempts

/-- The odd multi-factor process satisfies the recursive fallback model. -/
theorem recursiveOddSplitProcessPMF_recursiveFallbackProbabilityModel {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts fuel : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    RecursiveFallbackProbabilityModel
      (recursiveOddSplitProcessPMF M D enumeration.toFieldEnumeration q attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2}
      attempts (CPolynomial.natDegree g) :=
  recursiveSplitProcessPMF_recursiveFallbackProbabilityModel _ g attempts fuel
    (fun _g hg _att _children hmem ↦
      oddSplitTrialPMF_support_isSplitStep M D enumeration.toFieldEnumeration q hg hmem)
    (fun g hvalid hdeg attempt ↦
      oddSplitTrial_success_probability_ge_half M D enumeration g attempt hfield
        (rootProductProbabilityInput_of_lasVegasSplitterInput hvalid hfield.card_eq) hdeg)
    hvalid hattempts

/--
Full recursive fallback bound for the odd branch: starting from a root product
of degree `d`, the probability that any factor anywhere in the recursion falls
back to exhaustive enumeration is at most the binomial tail
`2 ^ -attempts * ∑_{j ≤ d - 2} C(attempts, j)`.
-/
theorem recursiveOddSplitProcessPMF_fallback_probability_le_binomialTail {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts fuel : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (recursiveOddSplitProcessPMF M D enumeration.toFieldEnumeration q attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) :=
  recursiveFallback_probability_le_binomialTail _ _ _ _
    (recursiveOddSplitProcessPMF_recursiveFallbackProbabilityModel M D enumeration g
      attempts fuel hfield hvalid hattempts)

/-- Multi-factor characteristic-two trace splitting under uniform probes. -/
noncomputable def recursiveEvenTraceSplitProcessPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (enumeration : FieldEnumeration F) (q attempts : Nat) :
    Nat → List (CPolynomial F) → PMF (List Bool) :=
  recursiveSplitProcessPMF
    (fun g attempt ↦ evenTraceTrialPMF M D traceCtx enumeration q
      (CPolynomial.natDegree g) g attempt)
    attempts

/-- The trace multi-factor process satisfies the recursive fallback model. -/
theorem recursiveEvenTraceSplitProcessPMF_recursiveFallbackProbabilityModel {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts fuel : Nat)
    (hfield : EvenTraceUniformFieldModel F q traceCtx enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    RecursiveFallbackProbabilityModel
      (recursiveEvenTraceSplitProcessPMF M D traceCtx enumeration.toFieldEnumeration q
        attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2}
      attempts (CPolynomial.natDegree g) :=
  recursiveSplitProcessPMF_recursiveFallbackProbabilityModel _ g attempts fuel
    (fun _g hg _att _children hmem ↦
      evenTraceTrialPMF_support_isSplitStep M D traceCtx enumeration.toFieldEnumeration q
        hg hmem)
    (fun g hvalid hdeg attempt ↦
      evenTraceTrial_success_probability_ge_half M D traceCtx enumeration g attempt hfield
        ((rootProductProbabilityInput_of_lasVegasSplitterInput hvalid
          hfield.card_eq).hasTwoDistinctRoots hdeg) hdeg)
    hvalid hattempts

/--
Full recursive fallback bound for the characteristic-two trace branch.
-/
theorem recursiveEvenTraceSplitProcessPMF_fallback_probability_le_binomialTail {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts fuel : Nat)
    (hfield : EvenTraceUniformFieldModel F q traceCtx enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (recursiveEvenTraceSplitProcessPMF M D traceCtx enumeration.toFieldEnumeration q
        attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) :=
  recursiveFallback_probability_le_binomialTail _ _ _ _
    (recursiveEvenTraceSplitProcessPMF_recursiveFallbackProbabilityModel M D traceCtx
      enumeration g attempts fuel hfield hvalid hattempts)

/--
Per-factor trial of the full Las Vegas backend: the odd Cantor-Zassenhaus
branch for odd `q`, the characteristic-two trace branch when trace metadata is
supplied, mirroring the branch selection of `lasVegasSplitLoopWith`.
-/
noncomputable def lasVegasSplitTrialPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    (enumeration : FieldEnumeration F) (q : Nat)
    (g : CPolynomial F) (attempt : Nat) : PMF (TrialResult F) :=
  match traceCtx? with
  | some traceCtx =>
      if q % 2 = 1 then
        oddSplitTrialPMF M D enumeration q (CPolynomial.natDegree g) g attempt
      else
        evenTraceTrialPMF M D traceCtx enumeration q (CPolynomial.natDegree g) g attempt
  | none => oddSplitTrialPMF M D enumeration q (CPolynomial.natDegree g) g attempt

/--
Probability-facing model for the full Las Vegas backend: either the field has
odd cardinality, or it is a binary field presented with matching trace
metadata.
-/
inductive LasVegasUniformFieldModel (F : Type*) (q : Nat)
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (traceCtx? : Option (SmallPrimeTraceContext F))
    (enumeration : UniformFieldEnumeration F q) : Prop
  | odd (hodd : q % 2 = 1) (hfield : OddUniformFieldModel F q enumeration)
  | evenTrace (traceCtx : SmallPrimeTraceContext F)
      (hctx : traceCtx? = some traceCtx) (heven : q % 2 = 0)
      (hfield : EvenTraceUniformFieldModel F q traceCtx enumeration)

theorem LasVegasUniformFieldModel.card_eq {F : Type*} {q : Nat}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {traceCtx? : Option (SmallPrimeTraceContext F)}
    {enumeration : UniformFieldEnumeration F q}
    (hmodel : LasVegasUniformFieldModel F q traceCtx? enumeration) :
    Fintype.card F = q := by
  cases hmodel with
  | odd _ hfield => exact hfield.card_eq
  | evenTrace _ _ _ hfield => exact hfield.card_eq

/-- Successful backend trials are split steps. -/
theorem lasVegasSplitTrialPMF_support_isSplitStep {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    (enumeration : FieldEnumeration F) (q : Nat) {g : CPolynomial F} (hg : g ≠ 0)
    {attempt : Nat} {children : Array (CPolynomial F)}
    (hmem : TrialResult.split children ∈
      (lasVegasSplitTrialPMF M D traceCtx? enumeration q g attempt).support) :
    IsSplitStep g children := by
  unfold lasVegasSplitTrialPMF at hmem
  cases traceCtx? with
  | none => exact oddSplitTrialPMF_support_isSplitStep M D enumeration q hg hmem
  | some traceCtx =>
      dsimp only at hmem
      by_cases hodd : q % 2 = 1
      · rw [if_pos hodd] at hmem
        exact oddSplitTrialPMF_support_isSplitStep M D enumeration q hg hmem
      · rw [if_neg hodd] at hmem
        exact evenTraceTrialPMF_support_isSplitStep M D traceCtx enumeration q hg hmem

/-- Backend trials on splitter-valid factors succeed at rate one half. -/
theorem lasVegasSplitTrialPMF_success_probability_ge_half {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (hmodel : LasVegasUniformFieldModel F q traceCtx? enumeration)
    (g : CPolynomial F) (hvalid : lasVegasSplitterInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) (attempt : Nat) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (lasVegasSplitTrialPMF M D traceCtx? enumeration.toFieldEnumeration q g attempt) := by
  have hinput : RootProductProbabilityInput q g :=
    rootProductProbabilityInput_of_lasVegasSplitterInput hvalid hmodel.card_eq
  cases hmodel with
  | odd hodd hfield =>
      have heq : lasVegasSplitTrialPMF M D traceCtx? enumeration.toFieldEnumeration q
          g attempt =
          oddSplitTrialPMF M D enumeration.toFieldEnumeration q
            (CPolynomial.natDegree g) g attempt := by
        unfold lasVegasSplitTrialPMF
        cases traceCtx? <;> simp [hodd]
      rw [heq]
      exact oddSplitTrial_success_probability_ge_half M D enumeration g attempt hfield
        hinput hdegree
  | evenTrace traceCtx hctx heven hfield =>
      have heq : lasVegasSplitTrialPMF M D traceCtx? enumeration.toFieldEnumeration q
          g attempt =
          evenTraceTrialPMF M D traceCtx enumeration.toFieldEnumeration q
            (CPolynomial.natDegree g) g attempt := by
        unfold lasVegasSplitTrialPMF
        rw [hctx]
        dsimp only
        rw [if_neg (by omega : ¬q % 2 = 1)]
      rw [heq]
      exact evenTraceTrial_success_probability_ge_half M D traceCtx enumeration g attempt
        hfield (hinput.hasTwoDistinctRoots hdegree) hdegree

/--
The full Las Vegas backend recursion under idealized uniform probes,
dispatching between the odd and trace branches by field characteristic.
-/
noncomputable def lasVegasRecursiveSplitProcessPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    (enumeration : FieldEnumeration F) (q attempts : Nat) :
    Nat → List (CPolynomial F) → PMF (List Bool) :=
  recursiveSplitProcessPMF (lasVegasSplitTrialPMF M D traceCtx? enumeration q) attempts

/--
Backend-level recursive fallback bound: over any finite field — odd, or binary
with matching trace metadata — the full Las Vegas recursion on a splitter-valid
input of degree `d` reaches exhaustive enumeration anywhere with probability at
most the binomial tail `2 ^ -attempts * ∑_{j ≤ d - 2} C(attempts, j)`.
-/
theorem lasVegasRecursiveSplitProcessPMF_fallback_probability_le_binomialTail {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx? : Option (SmallPrimeTraceContext F))
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts fuel : Nat)
    (hmodel : LasVegasUniformFieldModel F q traceCtx? enumeration)
    (hvalid : lasVegasSplitterInput q g)
    (hattempts : CPolynomial.natDegree g - 2 ≤ attempts) :
    eventProbability
      (lasVegasRecursiveSplitProcessPMF M D traceCtx? enumeration.toFieldEnumeration q
        attempts fuel [g])
      {tr2 : List Bool | true ∈ tr2} ≤
    binomialFallbackTail attempts (CPolynomial.natDegree g) :=
  recursiveSplitProcessPMF_fallback_probability_le_binomialTail _ g attempts fuel
    (fun _g hg _att _children hmem ↦
      lasVegasSplitTrialPMF_support_isSplitStep M D traceCtx?
        enumeration.toFieldEnumeration q hg hmem)
    (fun g hvalid hdeg attempt ↦
      lasVegasSplitTrialPMF_success_probability_ge_half M D traceCtx? enumeration hmodel
        g hvalid hdeg attempt)
    hvalid hattempts

/--
Headline backend theorem: for any nonzero polynomial over a finite field — odd,
or binary with matching trace metadata — the Las Vegas backend run on its
finite-field root product reaches exhaustive enumeration anywhere in the
recursion with probability at most the binomial tail in the attempt cutoff.
-/
theorem finiteFieldRootProductWith_lasVegas_fallback_probability_le_binomialTail
    {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (enumeration : UniformFieldEnumeration F ctx.q)
    {p : CPolynomial F} (attempts fuel : Nat)
    (hmodel : LasVegasUniformFieldModel F ctx.q traceCtx? enumeration)
    (hp : p ≠ 0)
    (hattempts :
      CPolynomial.natDegree (finiteFieldRootProductWith M D ctx p) - 2 ≤ attempts) :
    eventProbability
      (lasVegasRecursiveSplitProcessPMF M D traceCtx? enumeration.toFieldEnumeration
        ctx.q attempts fuel [finiteFieldRootProductWith M D ctx p])
      {tr2 : List Bool | true ∈ tr2} ≤
    binomialFallbackTail attempts
      (CPolynomial.natDegree (finiteFieldRootProductWith M D ctx p)) :=
  lasVegasRecursiveSplitProcessPMF_fallback_probability_le_binomialTail M D traceCtx?
    enumeration _ attempts fuel hmodel
    (finiteFieldRootProductWith_lasVegasSplitterInput M D ctx hp) hattempts

end FiniteField

end Roots

end CPolynomial

end CompPoly
