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
  sorry

/-- Every field element has probability `1 / q` under a uniform field enumeration. -/
theorem uniformFieldElementPMF_apply {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) (a : F) :
    uniformFieldElementPMF enumeration.toFieldEnumeration a = (q : ℝ≥0∞)⁻¹ := by
  sorry

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
  sorry

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
  sorry

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
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (oddSplitTrialPMF M D enumeration.toFieldEnumeration q
          (CPolynomial.natDegree g) g attempt) := by
  sorry

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
  sorry

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
Target theorem for the full recursive splitter: under the independence and
root-product hypotheses represented by the future recursion model, fallback is
bounded by the binomial tail.
-/
theorem recursiveFallback_probability_le_binomialTail {Ω : Type*}
    (process : PMF Ω) (fallbackEvent : Set Ω)
    (attempts degree : Nat)
    (hmodel : True) :
    eventProbability process fallbackEvent ≤ binomialFallbackTail attempts degree := by
  sorry

end FiniteField

end Roots

end CPolynomial

end CompPoly
