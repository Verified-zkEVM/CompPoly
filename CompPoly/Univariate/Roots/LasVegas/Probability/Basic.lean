/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability Basics for Las Vegas Root Splitting

Shared probability-side vocabulary for the Las Vegas splitter: event
probabilities, uniform enumeration models, split-trial results, and small PMF
lemmas about trial success and failure mass.

This module is intentionally separate from the executable splitter modules:
runtime root search remains pure and deterministic for a fixed `ProbeFamily`,
while the probability modules model idealized uniform probes. Runtime and
correctness modules must not import this file or any other probability module.
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

/--
Probability-facing odd-field model: the uniform enumeration size `q` is the
cardinality of the finite field, and that cardinality is odd.

This intentionally stays separate from the runtime splitter contract
`lasVegasSplitterInput`, which must not accumulate probability hypotheses.
-/
structure OddUniformFieldModel (F : Type*) (q : Nat) [Fintype F]
    (enumeration : UniformFieldEnumeration F q) : Prop where
  q_odd : q % 2 = 1
  card_eq : Fintype.card F = q

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

/-- Trial failure probability is the PMF mass of the failed outcome. -/
theorem trialFailureProbability_eq_failed_mass {F : Type*} [Zero F]
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

/-- Success probability and failed mass of a trial distribution sum to one. -/
theorem trialSuccessProbability_add_failed_mass {F : Type*} [Zero F]
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

/-- A trial that succeeds with probability at least `1 / 2` fails with at most `1 / 2`. -/
theorem trialFailureProbability_le_half_of_success {F : Type*} [Zero F]
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

end FiniteField

end Roots

end CPolynomial

end CompPoly
