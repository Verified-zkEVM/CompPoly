/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.Basic

/-!
# Uniform Probe Distributions for Las Vegas Root Splitting

Idealized uniform sources for the Las Vegas probability story: uniform field
elements induced by a lazy enumeration, independent uniform coefficient arrays,
and the uniform probe-polynomial distribution they induce.

The deep target of this module is pair-evaluation uniformity: a uniform probe
with at least two sampled coefficients evaluates at two distinct field points
to a uniform pair on `F × F`.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

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

/--
Pair-evaluation uniformity: a uniform probe with at least two sampled
coefficients evaluates at two distinct points to a uniform pair on `F × F`.

For a fixed coefficient tail, the map
`(c₀, c₁) ↦ (c₀ + c₁ * a + tail(a), c₀ + c₁ * b + tail(b))` is a bijection of
`F × F` because `a ≠ b`, so exactly one of the `q ^ 2` equally likely
`(c₀, c₁)` choices hits the target pair `(x, y)`.
-/
theorem uniformProbePMF_eval_pair_apply {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q)
    (coefficientCount : Nat) {a b : F} (x y : F)
    (hab : a ≠ b) (hcount : 2 ≤ coefficientCount) :
    eventProbability
        (uniformProbePMF enumeration.toFieldEnumeration coefficientCount)
        {h | CPolynomial.eval a h = x ∧ CPolynomial.eval b h = y} =
      (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
  sorry

end FiniteField

end Roots

end CPolynomial

end CompPoly
