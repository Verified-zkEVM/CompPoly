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
  have hcard2 : 2 ≤ g.toPoly.roots.card := by
    rw [hinput.roots_card_eq_degree, ← CPolynomial.natDegree_toPoly]
    exact hdegree
  have hnodup : g.toPoly.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [Polynomial.count_roots]
    by_contra hgt
    have hsq : (Polynomial.X - Polynomial.C z) * (Polynomial.X - Polynomial.C z) ∣
        g.toPoly := by
      have hpow : (Polynomial.X - Polynomial.C z) ^ 2 ∣ g.toPoly :=
        (pow_dvd_pow _ (by omega)).trans (Polynomial.pow_rootMultiplicity_dvd g.toPoly z)
      rwa [_root_.pow_two] at hpow
    exact Polynomial.not_isUnit_X_sub_C z (hinput.squarefree _ hsq)
  have hfin : 1 < g.toPoly.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnodup]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hfin
  have hroot : ∀ z ∈ g.toPoly.roots.toFinset, CPolynomial.eval z g = 0 := by
    intro z hz
    rw [CPolynomial.eval_toPoly]
    exact (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hz)).2
  exact ⟨a, b, hab, hroot a ha, hroot b hb⟩

/--
Over a field of cardinality `q`, the runtime splitter contract already implies
the full probability-facing root-product model: every divisor of the Frobenius
polynomial `X ^ q - X` is squarefree and splits with as many roots as its
degree.
-/
theorem rootProductProbabilityInput_of_lasVegasSplitterInput {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F] {q : Nat} {g : CPolynomial F}
    (hvalid : lasVegasSplitterInput q g) (hcard : Fintype.card F = q) :
    RootProductProbabilityInput q g := by
  obtain ⟨hne, hdvd⟩ := hvalid
  have hq2 : 2 ≤ q := by
    have hlt := Fintype.one_lt_card (α := F)
    omega
  have hXne : ((Polynomial.X : Polynomial F) ^ q - Polynomial.X) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero F (by omega)
  have hXdeg : ((Polynomial.X : Polynomial F) ^ q - Polynomial.X).natDegree = q :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F (by omega)
  have hXroots : ((Polynomial.X : Polynomial F) ^ q - Polynomial.X).roots =
      (Finset.univ : Finset F).val := by
    rw [← hcard]
    exact FiniteField.roots_X_pow_card_sub_X (K := F)
  have hXsplits : ((Polynomial.X : Polynomial F) ^ q - Polynomial.X).Splits := by
    rw [Polynomial.splits_iff_card_roots, hXroots, hXdeg]
    simpa using hcard
  have hXsf : Squarefree ((Polynomial.X : Polynomial F) ^ q - Polynomial.X) := by
    apply Polynomial.Separable.squarefree
    rw [← Polynomial.nodup_roots_iff_of_splits hXne hXsplits, hXroots]
    exact (Finset.univ : Finset F).nodup
  refine ⟨hne, hdvd, hXsf.squarefree_of_dvd hdvd, ?_⟩
  exact Polynomial.splits_iff_card_roots.mp (hXsplits.of_dvd hXne hdvd)

/--
Finite-field root products satisfy the probability-facing root-product model.
This is the adapter from the concrete `finiteFieldRootProductWith` construction
to the hypotheses of the half-success and recursive fallback theorems.
-/
theorem finiteFieldRootProductWith_rootProductProbabilityInput {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    RootProductProbabilityInput ctx.q (finiteFieldRootProductWith M D ctx p) := by
  apply rootProductProbabilityInput_of_lasVegasSplitterInput
    (finiteFieldRootProductWith_lasVegasSplitterInput M D ctx hp)
  rw [← Nat.card_eq_fintype_card]
  exact ctx.card_eq

/-- Default-backend root products satisfy the probability-facing model. -/
theorem finiteFieldRootProduct_rootProductProbabilityInput {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    RootProductProbabilityInput ctx.q (finiteFieldRootProduct ctx p) :=
  finiteFieldRootProductWith_rootProductProbabilityInput
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx hp

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
theorem oddSplitTrial_success_probability_ge_half_of_two_le {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (coefficientCount attempt : Nat)
    (hcount : 2 ≤ coefficientCount)
    (hfield : OddUniformFieldModel F q enumeration)
    (hroots : HasTwoDistinctRoots g)
    (hg : g ≠ 0) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (oddSplitTrialPMF M D enumeration.toFieldEnumeration q coefficientCount
          g attempt) := by
  obtain ⟨a, b, hab, hra, hrb⟩ := hroots
  have hpush_eq := uniformProbePMF_map_eval_pair enumeration coefficientCount hab hcount
  -- Bucket-separated probes force the executable attempt to succeed.
  rw [trialSuccessProbability, eventProbability, oddSplitTrialPMF,
    PMF.toOuterMeasure_map_apply]
  have hsubset : {h : CPolynomial F |
      oddCZBucket q (CPolynomial.eval a h) ≠ oddCZBucket q (CPolynomial.eval b h)} ⊆
      (fun h : CPolynomial F ↦
        match cantorZassenhausOddAttemptWith M D q
            ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g attempt with
        | some children => TrialResult.split children
        | none => TrialResult.failed) ⁻¹' {trial | trial.IsSuccess} := by
    intro h hsep
    obtain ⟨children, hchildren⟩ :=
      cantorZassenhausOddAttemptWith_success_of_bucket_separated M D q attempt hg
        hra hrb hsep
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hchildren]
    exact trivial
  have hpre : ((fun h : CPolynomial F ↦
      (CPolynomial.eval a h, CPolynomial.eval b h)) ⁻¹'
        {xy : F × F | oddCZBucket q xy.1 ≠ oddCZBucket q xy.2}) =
      {h : CPolynomial F |
        oddCZBucket q (CPolynomial.eval a h) ≠ oddCZBucket q (CPolynomial.eval b h)} := rfl
  have hge : (2 : ℝ≥0∞)⁻¹ ≤
      (uniformProbePMF enumeration.toFieldEnumeration
        coefficientCount).toOuterMeasure
        {h : CPolynomial F |
          oddCZBucket q (CPolynomial.eval a h) ≠ oddCZBucket q (CPolynomial.eval b h)} := by
    rw [← hpre, ← PMF.toOuterMeasure_map_apply, hpush_eq]
    exact oddCZBucket_pair_separated_probability_ge_half enumeration
      hfield.q_odd hfield.card_eq
  exact le_trans hge ((uniformProbePMF enumeration.toFieldEnumeration
    coefficientCount).toOuterMeasure.mono hsubset)

/--
Random affine probes with both coefficients drawn uniformly and independently
already achieve the half-success bound: the evaluation pair at two distinct
roots covers all of `F × F`, so no higher-degree probes are needed.
-/
theorem oddSplitTrial_success_probability_ge_half_linear {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempt : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hroots : HasTwoDistinctRoots g)
    (hg : g ≠ 0) :
    (2 : ℝ≥0∞)⁻¹ ≤
      trialSuccessProbability
        (oddSplitTrialPMF M D enumeration.toFieldEnumeration q 2 g attempt) :=
  oddSplitTrial_success_probability_ge_half_of_two_le M D enumeration g 2 attempt
    le_rfl hfield hroots hg

/--
Uniform probe polynomials really make one odd Cantor-Zassenhaus attempt succeed
with probability at least `1 / 2`.

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
  have hg : g ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    have hnat : CPolynomial.natDegree (0 : CPolynomial F) = 0 := rfl
    omega
  unfold OddSplitTrialHalfSuccessModel
  exact oddSplitTrial_success_probability_ge_half_of_two_le M D enumeration g
    (CPolynomial.natDegree g) attempt hdegree hfield hroots hg

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
