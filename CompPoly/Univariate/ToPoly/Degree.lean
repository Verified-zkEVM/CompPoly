/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import CompPoly.Univariate.ToPoly.Impl

/-!
# `toPoly` Degree Lemmas

Degree lemmas for the computable-univariate to `Polynomial` conversion.
-/

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*} [Semiring R] [BEq R]

section LinearEquiv

variable [LawfulBEq R]

lemma toPoly_smul (r : R) (p : CPolynomial R) :
    (r • p).toPoly = r • p.toPoly := by
  ext i; rw [Polynomial.coeff_smul, ← coeff_toPoly, ← coeff_toPoly, coeff_smul, smul_eq_mul]

noncomputable def toPolyLinearEquiv : CPolynomial R ≃ₗ[R] R[X] where
  toFun := toPoly
  invFun := fun p => ⟨p.toImpl, isCanonical_toImpl p⟩
  map_add' := toPoly_add
  map_smul' := toPoly_smul
  left_inv := fun p => Subtype.ext (toImpl_toPoly_of_canonical p)
  right_inv := fun _ => toPoly_toImpl
theorem degree_le_iff_coeff_zero (p : CPolynomial R) (n : WithBot ℕ) :
    p.degree ≤ n ↔ ∀ k : ℕ, n < k → p.coeff k = 0 := by
    rw [degree_toPoly, Polynomial.degree_le_iff_coeff_zero]
    simp only [coeff_toPoly]

theorem degree_lt_iff_coeff_zero (p : CPolynomial R) (n : ℕ) :
    p.degree < n ↔ ∀ k : ℕ, n ≤ k → p.coeff k = 0 := by
    rw [degree_toPoly, Polynomial.degree_lt_iff_coeff_zero]
    simp only [coeff_toPoly]

omit [BEq R] [LawfulBEq R] in
theorem mem_degreeLE {n : WithBot ℕ} {p : (CPolynomial R)} :
    p ∈ degreeLE (R := R) n ↔ degree p ≤ n := by
  rfl

omit [BEq R] [LawfulBEq R] in
theorem degreeLE_mono (m n : WithBot ℕ) (h_lessThan : m ≤ n) :
    degreeLE (R := R) m ≤ degreeLE (R := R) n :=
  fun _ hf => mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) h_lessThan)

omit [BEq R] [LawfulBEq R] in
theorem mem_degreeLT {n : ℕ} {p : CPolynomial R} : p ∈ degreeLT (R := R) n ↔ degree p < n := by
  rfl

omit [BEq R] [LawfulBEq R] in
theorem degreeLT_mono {m n : ℕ} (h : m ≤ n) :
    degreeLT (R := R) m ≤ degreeLT (R := R) n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 h)

omit [BEq R] [LawfulBEq R] in
theorem degreeLT_succ_eq_degreeLE {n : ℕ} :
    degreeLT (R := R) (n + 1) = degreeLE (R := R) ↑n := by
  ext p
  change p.val.degreeBound < (n + 1 : ℕ) ↔ p.val.degreeBound ≤ (n : WithBot ℕ)
  cases hd : p.val.degreeBound with
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
      map_sum (lcoeff (R := R) i) _ _]
  simp only [coeff_monomial]
  by_cases hi : i < n
  · rw [Finset.sum_eq_single_of_mem ⟨i, hi⟩ (Finset.mem_univ _)
      (fun j _ hji => if_neg fun h => hji (Fin.ext h.symm))]
    simp
  · rw [show coeff p.1 i = 0 from
      (degree_lt_iff_coeff_zero p.1 n).mp (mem_degreeLT.mp p.2) i (by omega)]
    exact Finset.sum_eq_zero fun j _ => if_neg (by have := j.isLt; omega)

lemma degreeLTEquiv_right_inv [DecidableEq R] (n : ℕ)
    (f : Fin n → R) :
    (fun i : Fin n => coeff
      (Finset.univ.sum (fun j : Fin n => monomial (R := R) (↑j) (f j))) i) = f := by
  funext i
  rw [show coeff (∑ j : Fin n, monomial (R := R) (↑j) (f j)) ↑i =
    ∑ j : Fin n, coeff (monomial (R := R) (↑j) (f j)) ↑i from
      map_sum (lcoeff (R := R) ↑i) _ _]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
    (fun j _ hji => if_neg fun h => hji (Fin.ext (by omega)))]
  simp

def degreeLTEquiv [DecidableEq R] (n : ℕ) :
    ↥(degreeLT (R := R) n) ≃ₗ[R] (Fin n → R) where
  toFun := degreeLTCoeffs (R := R) n
  invFun := fun f => ⟨Finset.univ.sum (fun i : Fin n => monomial (R := R) (↑i) (f i)),
    degreeLTEquiv_invFun_mem (R := R) n f⟩
  left_inv := degreeLTEquiv_left_inv (R := R) n
  right_inv := degreeLTEquiv_right_inv (R := R) n
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
  simp [degreeLTEquiv, degreeLTCoeffs, Polynomial.degreeLTEquiv, ← coeff_toPoly]

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

end CPolynomial

end CompPoly
