/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Combinatorics.Nullstellensatz

/-!
# Polynomials of degree at most one per variable

Such a polynomial is fixed by its values on the Boolean hypercube $\{0, 1\}^\sigma$.

This is a corollary of the combinatorial Nullstellensatz.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {R σ : Type*} [CommRing R] [IsDomain R] [Finite σ]

/-- Two polynomials of degree at most one per variable that agree on the hypercube are equal.

This is Lemma 3.6 of Thaler, "Proofs, Arguments, and Zero-Knowledge".
-/
theorem eq_of_degreeOf_le_one_of_eval_zeroOne {p q : MvPolynomial σ R}
    (hp : ∀ i, p.degreeOf i ≤ 1) (hq : ∀ i, q.degreeOf i ≤ 1)
    (h : ∀ x : σ → R, (∀ i, x i = 0 ∨ x i = 1) → eval x p = eval x q) : p = q := by
  classical
  refine sub_eq_zero.mp (eq_zero_of_eval_zero_at_prod_finset _ (fun _ => {0, 1}) (fun i => ?_)
    fun x hx => ?_)
  · rw [card_pair zero_ne_one]
    exact lt_of_le_of_lt ((degreeOf_sub_le _ _ _).trans (max_le (hp i) (hq i))) one_lt_two
  · rw [eval_sub, h x fun i => by simpa only [mem_insert, mem_singleton] using hx i, sub_self]

end MvPolynomial
