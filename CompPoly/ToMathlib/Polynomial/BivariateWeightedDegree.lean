/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.ToMathlib.Polynomial.BivariateDegree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Mathlib-Facing Bivariate Weighted-Degree Helpers

This file extends `Polynomial.Bivariate` with weighted-degree algebra that is generic
and reusable across downstream protocol developments.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- The monomial `X^i Y^j` as a bivariate polynomial. -/
def monomial (i j : ℕ) : F[X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i 1)

/-- The weighted degree of a sum is at most the maximum of the weighted degrees. -/
lemma natWeightedDegree_add_le (p q : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  refine Finset.sup_le fun m hm ↦ ?_
  by_cases h : m ∈ p.support <;> by_cases h' : m ∈ q.support <;>
    simp_all only [Polynomial.mem_support_iff, coeff_add, ne_eq, le_sup_iff]
  ·
    have h_deg : (p.coeff m + q.coeff m).natDegree ≤
        max ((p.coeff m).natDegree) ((q.coeff m).natDegree) :=
      natDegree_add_le (p.coeff m) (q.coeff m)
    cases max_cases (natDegree (p.coeff m)) (natDegree (q.coeff m)) <;>
      simp_all only [sup_of_le_left, sup_eq_left, and_self, natWeightedDegree]
    ·
      exact Or.inl <|
        le_trans
          (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
          (Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m) <| by aesop)
    ·
      exact Or.inr <|
        le_trans
          (add_le_add (mul_le_mul_of_nonneg_left h_deg <| Nat.zero_le _) le_rfl)
          (Finset.le_sup (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop)
  all_goals simp_all only [not_not, add_zero, zero_add, not_false_eq_true]
  ·
    exact Or.inl <|
      Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m) <| by aesop
  ·
    exact Or.inr <|
      Finset.le_sup (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop
  ·
    simp at hm

/-- The weighted degree of a sum is bounded by the supremum of the weighted degrees. -/
lemma natWeightedDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → F[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [natWeightedDegree]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact le_trans (natWeightedDegree_add_le _ _ _ _) (max_le_max le_rfl ih)

/-- The weighted degree of a scalar multiple is at most the weighted degree of the polynomial. -/
lemma natWeightedDegree_smul_le (a : F) (p : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (a • p) u v ≤ natWeightedDegree p u v := by
  simp only [natWeightedDegree, coeff_smul, Finset.sup_le_iff, Polynomial.mem_support_iff, ne_eq]
  intro b _
  exact le_trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (natDegree_smul_le a (p.coeff b)) u.zero_le)
      (mul_le_mul_of_nonneg_left le_rfl v.zero_le))
    (Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m)
      (show b ∈ p.support from by aesop))

/-- The degree of `Q(X, P(X))` is bounded by the weighted degree of `Q`,
provided `deg(P) ≤ k - 1`. -/
lemma degree_eval_le_weightedDegree (Q : F[X][Y]) (P : F[X]) (k : ℕ) (hP : P.natDegree ≤ k - 1) :
    (Q.eval P).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
  intro i hi
  by_cases hi' : Q.coeff i = 0
  · simp [hi', natWeightedDegree]
  ·
    have hpow : (P ^ i).natDegree ≤ (k - 1) * i := by
      simpa [Nat.mul_comm] using
        (Polynomial.natDegree_pow_le_of_le (p := P) (m := k - 1) i hP)
    refine le_trans ?_
      (Finset.le_sup (f := fun m ↦ 1 * (Q.coeff m).natDegree + (k - 1) * m)
        (show i ∈ Q.support from Polynomial.mem_support_iff.mpr hi'))
    exact le_trans Polynomial.natDegree_mul_le <|
      by simpa [one_mul] using Nat.add_le_add_left hpow (Q.coeff i).natDegree

end Semiring

section NontrivialSemiring

variable [Semiring F] [Nontrivial F]

/-- The weighted degree of `X^i Y^j` is `u * i + v * j`. -/
lemma natWeightedDegree_monomial (i j u v : ℕ) :
    natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
  classical
  simp only [natWeightedDegree, monomial]
  refine le_antisymm ?_ ?_ <;> norm_num
  ·
    intros b hb
    simp [coeff_monomial] at hb
    simp [← hb]
  ·
    refine le_trans ?_ (Finset.le_sup
      (f := fun m ↦ u * (Polynomial.monomial j (Polynomial.monomial i 1) |>.coeff m |>.natDegree)
        + v * m) (b := j) ?_)
    all_goals norm_num [coeff_monomial]

end NontrivialSemiring

end
end Polynomial.Bivariate
