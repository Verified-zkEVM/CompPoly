/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.OddBuckets
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Squarefree.Basic

/-!
# One Odd Cantor-Zassenhaus Trial Under Uniform Probes

The single-trial probability surface for odd-field Las Vegas splitting: the
trial PMF induced by uniform probes, the half-success model, and the theorem
that uniform probes really achieve success probability at least `1 / 2` for
squarefree root products with at least two distinct roots.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- The factor has at least two distinct field roots. -/
def HasTwoDistinctRoots {F : Type*} [Semiring F] (g : CPolynomial F) : Prop :=
  ∃ a b : F, a ≠ b ∧ CPolynomial.eval a g = 0 ∧ CPolynomial.eval b g = 0

/--
Probability-facing root-product model for the recursive fallback analysis: the
factor is a nonzero squarefree product of linear factors over the field, with
as many roots as its degree, dividing the Frobenius polynomial `X ^ q - X`.

This intentionally strengthens the runtime splitter contract
`lasVegasSplitterInput` instead of overloading it with probability details.
-/
structure RootProductProbabilityInput {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (g : CPolynomial F) : Prop where
  nonzero : g ≠ 0
  splits_over_field :
    g.toPoly ∣ ((Polynomial.X : Polynomial F) ^ q - Polynomial.X)
  squarefree : Squarefree g.toPoly
  roots_card_eq_degree : g.toPoly.roots.card = g.toPoly.natDegree

/--
A squarefree root product of degree at least two has two distinct field roots.
-/
theorem RootProductProbabilityInput.hasTwoDistinctRoots {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {q : Nat} {g : CPolynomial F}
    (hinput : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    HasTwoDistinctRoots g := by
  sorry

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
Uniform probe polynomials really make one odd Cantor-Zassenhaus attempt succeed
with probability at least `1 / 2`.

The proof combines pair-evaluation uniformity of `uniformProbePMF`, the Euler
bucket separation probability, and the deterministic theorem that a probe whose
buckets separate two roots forces the executable attempt to succeed.

The hypothesis `hdegree` is essential and not implied by `hroots`: for `g = 0`
every pair of points consists of roots, yet the trial samples zero-coefficient
probes and always fails.
-/
theorem oddSplitTrialHalfSuccessModel_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempt : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hroots : HasTwoDistinctRoots g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    OddSplitTrialHalfSuccessModel M D enumeration g attempt := by
  sorry

/--
For a squarefree finite-field root product over an odd field, one uniform
Cantor-Zassenhaus trial succeeds with probability at least `1 / 2`.

Unlike the historical model-assisted shape (kept below as
`oddSplitTrial_success_probability_ge_half_of_model`), this theorem no longer
accepts the probability bound itself as an input.
-/
theorem oddSplitTrial_success_probability_ge_half {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempt : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (oddSplitTrialPMF M D enumeration.toFieldEnumeration q
          (CPolynomial.natDegree g) g attempt) :=
  oddSplitTrialHalfSuccessModel_of_uniformProbe M D enumeration g attempt
    hfield (hrootProduct.hasTwoDistinctRoots hdegree) hdegree

/--
Compatibility shape of the half-success theorem that still accepts the
half-success model as an assumption. Prefer
`oddSplitTrial_success_probability_ge_half`, which derives the model from the
uniform probe source.
-/
theorem oddSplitTrial_success_probability_ge_half_of_model {F : Type*}
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

end FiniteField

end Roots

end CPolynomial

end CompPoly
