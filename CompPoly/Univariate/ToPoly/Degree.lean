/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Julian Sutherland
-/
module

import all CompPoly.Univariate.ToPoly.Impl
public import CompPoly.Univariate.ToPoly.Impl

/-!
# `toPoly` Degree Lemmas

Degree lemmas for the computable-univariate to `Polynomial` conversion.
-/

public section

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*} [Semiring R] [BEq R]

section LinearEquiv

variable [LawfulBEq R]

@[simp, grind =, norm_cast]
lemma toPoly_smul (r : R) (p : CPolynomial R) :
    (r • p).toPoly = r • p.toPoly := by
  ext i; rw [Polynomial.coeff_smul, ← coeff_toPoly, ← coeff_toPoly, coeff_smul, smul_eq_mul]

noncomputable def toPolyLinearEquiv : CPolynomial R ≃ₗ[R] R[X] where
  toFun := toPoly
  invFun := fun p => ⟨p.toImpl, isCanonical_toImpl p⟩
  map_add' := toPoly_add
  map_smul' := toPoly_smul
  left_inv := fun p => Subtype.ext (toImpl_toPoly_of_canonical p)
  right_inv := toPoly_mk_toImpl

/-- The forward map of `toPolyLinearEquiv` is `toPoly`. -/
@[simp]
theorem toPolyLinearEquiv_apply (p : CPolynomial R) : toPolyLinearEquiv p = p.toPoly := by
  rfl

theorem degree_le_iff_coeff_zero (p : CPolynomial R) (n : WithBot ℕ) :
    p.degree ≤ n ↔ ∀ k : ℕ, n < k → p.coeff k = 0 := by
    rw [degree_toPoly, Polynomial.degree_le_iff_coeff_zero]
    simp only [coeff_toPoly]

theorem degree_lt_iff_coeff_zero (p : CPolynomial R) (n : ℕ) :
    p.degree < n ↔ ∀ k : ℕ, n ≤ k → p.coeff k = 0 := by
    rw [degree_toPoly, Polynomial.degree_lt_iff_coeff_zero]
    simp only [coeff_toPoly]

omit [BEq R] [LawfulBEq R] in
theorem degreeLE_mono (m n : WithBot ℕ) (h_lessThan : m ≤ n) :
    degreeLE (R := R) m ≤ degreeLE (R := R) n :=
  fun _ hf => mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) h_lessThan)

omit [BEq R] [LawfulBEq R] in
theorem degreeLT_mono {m n : ℕ} (h : m ≤ n) :
    degreeLT (R := R) m ≤ degreeLT (R := R) n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 h)

omit [BEq R] [LawfulBEq R] in
theorem degreeLT_succ_eq_degreeLE {n : ℕ} :
    degreeLT (R := R) (n + 1) = degreeLE (R := R) ↑n := by
  ext p
  rw [mem_degreeLT, mem_degreeLE]
  cases hd : p.degree with
  | bot =>
      simp
  | coe a =>
      change ((a : WithBot ℕ) < (n + 1 : ℕ)) ↔ ((a : WithBot ℕ) ≤ (n : ℕ))
      exact WithBot.coe_lt_coe.trans (Nat.lt_succ_iff.trans WithBot.coe_le_coe.symm)

section degreeLTEquiv

lemma monomial_mem_degreeLT [DecidableEq R] {n : ℕ} (i : Fin n) (c : R) :
    monomial (R := R) (i : ℕ) c ∈ degreeLT (R := R) n := by
  rw [mem_degreeLT_iff_size_le]
  by_cases hc : c = 0
  · simp [monomial, Raw.monomial, hc]
  · simp [monomial, Raw.monomial, hc, Nat.succ_le_of_lt i.isLt]

lemma degreeLTEquiv_invFun_mem [DecidableEq R] (n : ℕ) (f : Fin n → R) :
    Finset.univ.sum (fun i : Fin n => monomial (R := R) (i : ℕ) (f i)) ∈ degreeLT (R := R) n := by
  refine Finset.induction_on Finset.univ ?_ ?_
  · exact zero_mem_degreeLT (R := R) n
  · intro i s hi hs
    rw [Finset.sum_insert hi]
    exact add_mem_degreeLT (monomial_mem_degreeLT (R := R) i (f i)) hs

lemma degreeLTEquiv_left_inv [DecidableEq R] (n : ℕ)
    (p : ↥(degreeLT (R := R) n)) :
    (⟨
      Finset.univ.sum (fun i : Fin n => monomial (R := R) (↑i) (coeff p.1 i)),
      degreeLTEquiv_invFun_mem (R := R) n (fun i => coeff p.1 i)
    ⟩ : ↥(degreeLT (R := R) n)) = p := by
  apply Subtype.ext
  rw [eq_iff_coeff]
  intro i
  rw [show coeff (∑ j : Fin n, monomial (R := R) (↑j) (coeff p.1 j)) i =
    ∑ j : Fin n, coeff (monomial (R := R) (↑j) (coeff p.1 j)) i from
      by simpa only [lcoeff_apply] using map_sum (lcoeff (R := R) i) _ _]
  simp only [coeff_monomial]
  by_cases hi : i < n
  · rw [Finset.sum_eq_single_of_mem ⟨i, hi⟩ (Finset.mem_univ _)
      (fun j _ hji => ite_eq_right fun h => hji (Fin.ext h.symm))]
    simp
  · rw [show coeff p.1 i = 0 from
      (degree_lt_iff_coeff_zero p.1 n).mp (mem_degreeLT.mp p.2) i (by omega)]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right (by have := j.isLt; omega)

lemma degreeLTEquiv_right_inv [DecidableEq R] (n : ℕ)
    (f : Fin n → R) :
    (fun i : Fin n => coeff
      (Finset.univ.sum (fun j : Fin n => monomial (R := R) (↑j) (f j))) i) = f := by
  funext i
  rw [show coeff (∑ j : Fin n, monomial (R := R) (↑j) (f j)) ↑i =
    ∑ j : Fin n, coeff (monomial (R := R) (↑j) (f j)) ↑i from
      by simpa only [lcoeff_apply] using map_sum (lcoeff (R := R) ↑i) _ _]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
    (fun j _ hji => ite_eq_right fun h => hji (Fin.ext (by omega)))]
  simp

def degreeLTEquiv [DecidableEq R] (n : ℕ) :
    ↥(degreeLT (R := R) n) ≃ₗ[R] (Fin n → R) where
  toFun := degreeLTCoeffs (R := R) n
  invFun := fun f => ⟨Finset.univ.sum (fun i : Fin n => monomial (R := R) (↑i) (f i)),
    degreeLTEquiv_invFun_mem (R := R) n f⟩
  left_inv := by
    intro p
    simpa only [degreeLTCoeffs_apply] using degreeLTEquiv_left_inv (R := R) n p
  right_inv := by
    intro f
    funext i
    rw [degreeLTCoeffs_apply]
    exact congrFun (degreeLTEquiv_right_inv (R := R) n f) i
  map_add' := by
    intro p q
    exact (degreeLTCoeffs (R := R) n).map_add p q
  map_smul' := by
    intro r p
    exact (degreeLTCoeffs (R := R) n).map_smul r p

abbrev degreeLTLinearEquiv [DecidableEq R] (n : ℕ) :
    ↥(degreeLT (R := R) n) ≃ₗ[R] (Fin n → R) :=
  degreeLTEquiv (R := R) n

theorem degreeLTEquiv_toPoly [DecidableEq R] {n : ℕ} {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) (i : Fin n) :
      degreeLTEquiv (R := R) n ⟨p, hp⟩ i =
          Polynomial.degreeLTEquiv R n ⟨p.toPoly, degreeLT_toPoly.mp hp⟩ i := by
  simp [degreeLTEquiv, degreeLTCoeffs_apply, Polynomial.degreeLTEquiv, ← coeff_toPoly]

theorem degreeLTEquiv_eq_zero_iff_eq_zero [DecidableEq R] {n : ℕ} {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) :
    degreeLTEquiv (R := R) n ⟨p, hp⟩ = 0 ↔ p = 0 := by
  constructor
  · intro h
    have h_subtype : (⟨p, hp⟩ : ↥(degreeLT (R := R) n)) = 0 :=
      (degreeLTEquiv (R := R) n).injective (by simpa using h)
    exact congrArg Subtype.val h_subtype
  · rintro rfl
    have h_subtype : (⟨(0 : CPolynomial R), hp⟩ : ↥(degreeLT (R := R) n)) = 0 := by
      apply Subtype.ext
      rfl
    rw [h_subtype]
    exact map_zero (degreeLTEquiv (R := R) n)

theorem eval_eq_sum_degreeLTEquiv [DecidableEq R] {n : ℕ} {p : CPolynomial R}
    (hp : p ∈ degreeLT (R := R) n) (x : R) :
    eval x p =
      Finset.univ.sum (fun i : Fin n => degreeLTEquiv (R := R) n ⟨p, hp⟩ i * x ^ (i : ℕ)) := by
  rw [eval_toPoly, Polynomial.eval_eq_sum_degreeLTEquiv (degreeLT_toPoly.mp hp)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [degreeLTEquiv_toPoly (R := R) hp i]

end degreeLTEquiv

end LinearEquiv

section OfFinCoeff

variable [LawfulBEq R] [DecidableEq R]

/-- The polynomial built from `N` coefficients has `toPoly` of degree below `N`. -/
theorem degree_toPoly_ofFinCoeff_lt (N : ℕ) (c : ℕ → R) :
    (ofFinCoeff N c).toPoly.degree < (N : WithBot ℕ) := by
  rw [← degree_toPoly, degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_ofFinCoeff]
  exact ite_eq_right (by omega)

end OfFinCoeff

/-! ### Degree arithmetic

`CPolynomial` versions of Mathlib's degree, `natDegree` and `leadingCoeff` lemmas, each
transferred through the `toPoly` coercion. The `@[simp]` attributes follow Mathlib's. -/

section DegreeArith

variable [LawfulBEq R]

theorem degree_C_le (r : R) : (C r).degree ≤ 0 := by
  rw [degree_toPoly, C_toPoly]; exact Polynomial.degree_C_le

theorem degree_C {r : R} (hr : r ≠ 0) : (C r).degree = 0 := by
  rw [degree_toPoly, C_toPoly]; exact Polynomial.degree_C hr

@[simp]
theorem leadingCoeff_C (r : R) : (C r).leadingCoeff = r := by
  rw [leadingCoeff_toPoly, C_toPoly]; exact Polynomial.leadingCoeff_C r

@[simp]
theorem degree_X [Nontrivial R] : (X : CPolynomial R).degree = 1 := by
  rw [degree_toPoly, X_toPoly]; exact Polynomial.degree_X

@[simp]
theorem natDegree_X [Nontrivial R] : (X : CPolynomial R).natDegree = 1 := by
  rw [natDegree_toPoly, X_toPoly]; exact Polynomial.natDegree_X

@[simp]
theorem leadingCoeff_X [Nontrivial R] : (X : CPolynomial R).leadingCoeff = 1 := by
  rw [leadingCoeff_toPoly, X_toPoly]; exact Polynomial.leadingCoeff_X

@[simp]
theorem degree_one [Nontrivial R] : (1 : CPolynomial R).degree = 0 := by
  rw [degree_toPoly, toPoly_one]; exact Polynomial.degree_one

@[simp]
theorem natDegree_one [Nontrivial R] : (1 : CPolynomial R).natDegree = 0 := by
  rw [natDegree_toPoly, toPoly_one]; exact Polynomial.natDegree_one

@[simp]
theorem leadingCoeff_one [Nontrivial R] : (1 : CPolynomial R).leadingCoeff = 1 := by
  rw [leadingCoeff_toPoly, toPoly_one]; exact Polynomial.leadingCoeff_one

theorem degree_add_le (p q : CPolynomial R) : (p + q).degree ≤ max p.degree q.degree := by
  exact_mod_cast Polynomial.degree_add_le (p : Polynomial R) q

theorem degree_add_eq_left_of_degree_lt {p q : CPolynomial R} (h : q.degree < p.degree) :
    (p + q).degree = p.degree := by
  exact_mod_cast Polynomial.degree_add_eq_left_of_degree_lt (p := (p : Polynomial R)) (q := q)
    (by exact_mod_cast h)

theorem degree_add_eq_right_of_degree_lt {p q : CPolynomial R} (h : p.degree < q.degree) :
    (p + q).degree = q.degree := by
  exact_mod_cast Polynomial.degree_add_eq_right_of_degree_lt (p := (p : Polynomial R)) (q := q)
    (by exact_mod_cast h)

theorem degree_mul_le (p q : CPolynomial R) : (p * q).degree ≤ p.degree + q.degree := by
  exact_mod_cast Polynomial.degree_mul_le (p : Polynomial R) q

theorem natDegree_mul_le (p q : CPolynomial R) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  exact_mod_cast Polynomial.natDegree_mul_le (p := (p : Polynomial R)) (q := q)

theorem degree_pow_le [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).degree ≤ n • p.degree := by
  exact_mod_cast Polynomial.degree_pow_le (p : Polynomial R) n

theorem natDegree_pow_le [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).natDegree ≤ n * p.natDegree := by
  exact_mod_cast Polynomial.natDegree_pow_le (p := (p : Polynomial R)) (n := n)

theorem natDegree_pow_le_of_le [Nontrivial R] {p : CPolynomial R} {m : ℕ} (n : ℕ)
    (h : p.natDegree ≤ m) : (p ^ n).natDegree ≤ n * m :=
  (natDegree_pow_le p n).trans (Nat.mul_le_mul_left n h)

end DegreeArith

section DegreeArithRing

variable {S : Type*} [Ring S] [BEq S] [LawfulBEq S]

@[simp]
theorem degree_neg (p : CPolynomial S) : (-p).degree = p.degree := by
  exact_mod_cast Polynomial.degree_neg (p : Polynomial S)

@[simp]
theorem natDegree_neg (p : CPolynomial S) : (-p).natDegree = p.natDegree := by
  exact_mod_cast Polynomial.natDegree_neg (p : Polynomial S)

@[simp]
theorem leadingCoeff_neg (p : CPolynomial S) : (-p).leadingCoeff = -p.leadingCoeff := by
  exact_mod_cast Polynomial.leadingCoeff_neg (p : Polynomial S)

theorem degree_sub_le (p q : CPolynomial S) : (p - q).degree ≤ max p.degree q.degree := by
  exact_mod_cast Polynomial.degree_sub_le (p : Polynomial S) q

theorem natDegree_sub_le (p q : CPolynomial S) :
    (p - q).natDegree ≤ max p.natDegree q.natDegree := by
  exact_mod_cast Polynomial.natDegree_sub_le (p : Polynomial S) q

@[simp]
theorem degree_X_sub_C [Nontrivial S] (a : S) : (X - C a).degree = 1 := by
  rw [degree_toPoly, toPoly_sub, X_toPoly, C_toPoly]; exact Polynomial.degree_X_sub_C a

@[simp]
theorem natDegree_X_sub_C [Nontrivial S] (a : S) : (X - C a).natDegree = 1 := by
  rw [natDegree_toPoly, toPoly_sub, X_toPoly, C_toPoly]; exact Polynomial.natDegree_X_sub_C a

end DegreeArithRing

section DegreeArithNoZeroDivisors

variable [LawfulBEq R] [NoZeroDivisors R]

@[simp]
theorem degree_mul (p q : CPolynomial R) : (p * q).degree = p.degree + q.degree := by
  exact_mod_cast Polynomial.degree_mul (p := (p : Polynomial R)) (q := q)

theorem natDegree_mul {p q : CPolynomial R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  exact_mod_cast Polynomial.natDegree_mul ((toPoly_eq_zero_iff p).not.mpr hp)
    ((toPoly_eq_zero_iff q).not.mpr hq)

@[simp]
theorem leadingCoeff_mul (p q : CPolynomial R) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  exact_mod_cast Polynomial.leadingCoeff_mul (p : Polynomial R) q

@[simp]
theorem degree_pow [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).degree = n • p.degree := by
  exact_mod_cast Polynomial.degree_pow (p : Polynomial R) n

@[simp]
theorem natDegree_pow [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).natDegree = n * p.natDegree := by
  exact_mod_cast Polynomial.natDegree_pow (p : Polynomial R) n

@[simp]
theorem leadingCoeff_pow [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).leadingCoeff = p.leadingCoeff ^ n := by
  exact_mod_cast Polynomial.leadingCoeff_pow (p : Polynomial R) n

end DegreeArithNoZeroDivisors

end CPolynomial

end CompPoly
