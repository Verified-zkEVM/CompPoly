/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Multilinear.Basic
public import Mathlib.Combinatorics.Nullstellensatz

/-!
  # Multilinear extensions on the Boolean hypercube

  A hypercube table evaluates to its entries at the Boolean vertices, and a polynomial of degree
  at most one in each variable is determined by its values on the hypercube.

  The reference is Thaler, "Proofs, Arguments, and Zero-Knowledge", Lemma 3.6.
-/

@[expose] public section

open MvPolynomial Finset

variable {R : Type*} {n : ℕ}

namespace CompPoly

namespace CMlPolynomialEval

variable [CommRing R]

/-- The Boolean vertex with index `i`, in little-endian order: coordinate `j` is bit `j` of `i`. -/
def vertex (i : Fin (2 ^ n)) : Vector R n :=
  Vector.ofFn fun j => if (BitVec.ofFin i).getLsb j then 1 else 0

/-- Two indices below `2 ^ n` are equal when their first `n` bits agree. -/
private lemma eq_of_bits {i k : Fin (2 ^ n)}
    (h : ∀ j : Fin n, (i : ℕ).testBit j = (k : ℕ).testBit j) : i = k := by
  refine Fin.ext (Nat.eq_of_testBit_eq fun j => ?_)
  by_cases hj : j < n
  · exact h ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right two_pos (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le k.isLt (Nat.pow_le_pow_right two_pos (by omega)))]

/-- At a Boolean vertex the Lagrange basis is the indicator of that vertex. -/
theorem lagrangeBasis_vertex [Nontrivial R] (i k : Fin (2 ^ n)) :
    (lagrangeBasis (vertex (R := R) i))[(k : ℕ)] = if i = k then 1 else 0 := by
  rw [← Fin.getElem_fin, lagrangeBasis_getElem]
  have hfac : ∀ j : Fin n, (if (BitVec.ofFin k).getLsb j then (vertex (R := R) i)[j]
      else 1 - (vertex (R := R) i)[j]) =
      if (i : ℕ).testBit j = (k : ℕ).testBit j then (1 : R) else 0 := fun j => by
    simp only [vertex, Vector.getElem_ofFn, BitVec.getLsb_eq_getElem, Fin.getElem_fin,
      BitVec.getElem_ofFin]
    by_cases hi : (i : ℕ).testBit j <;> by_cases hk : (k : ℕ).testBit j <;> simp [hi, hk]
  simp only [hfac, prod_ite_zero, prod_const_one]
  congr 1
  exact propext ⟨fun h => eq_of_bits fun j => h j (mem_univ j), fun h j _ => by rw [h]⟩

/-- A hypercube table evaluates to its entry `i` at the vertex `i`. -/
theorem eval_vertex [Nontrivial R] (p : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    eval p (vertex i) = p[i] := by
  rw [eval, Vector.dotProduct_eq_root_dotProduct, _root_.dotProduct,
    sum_eq_single i (fun k _ hk => by
      simp only [Vector.get_eq_getElem, lagrangeBasis_vertex, Ne.symm hk, ite_false, mul_zero])
      (by simp)]
  simp only [Vector.get_eq_getElem, lagrangeBasis_vertex, ite_true, mul_one, Fin.getElem_fin]

/-- Hypercube tables with the same values at every vertex are equal. -/
theorem ext_of_eval_vertex [Nontrivial R] {p q : CMlPolynomialEval R n}
    (h : ∀ i : Fin (2 ^ n), eval p (vertex i) = eval q (vertex i)) : p = q :=
  Vector.ext fun k hk => by simpa [eval_vertex] using h ⟨k, hk⟩

end CMlPolynomialEval

end CompPoly

namespace MvPolynomial

variable [CommRing R] [IsDomain R] {σ : Type*} [Finite σ]

/-- Lemma 3.6 of Thaler: two polynomials of degree at most one in each variable that agree on the
Boolean hypercube are equal. -/
theorem eq_of_degreeOf_le_one_of_eval_zeroOne {p q : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (h : ∀ x : σ → R, (∀ i, x i = 0 ∨ x i = 1) → eval x p = eval x q) : p = q := by
  classical
  refine sub_eq_zero.mp (eq_zero_of_eval_zero_at_prod_finset _ (fun _ => {0, 1}) (fun i => ?_)
    fun x hx => ?_)
  · rw [card_pair zero_ne_one]
    exact lt_of_le_of_lt ((degreeOf_sub_le _ _ _).trans (max_le (hp i) (hq i))) one_lt_two
  · rw [eval_sub, h x fun i => by simpa using hx i, sub_self]

end MvPolynomial
