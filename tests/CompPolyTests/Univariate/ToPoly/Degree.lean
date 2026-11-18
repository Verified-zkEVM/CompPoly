/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public meta import CompPoly.Univariate.ToPoly.Degree
public meta import Mathlib.Algebra.Field.ZMod
public import CompPoly.Univariate.ToPoly.Degree
public import Mathlib.Algebra.Field.ZMod

/-!
# Enumeration of bounded-degree polynomials

The `#guard` checks evaluate the enumeration `instFintypeDegreeLT` over `ZMod 5` in compiled code
during elaboration. The `example` declarations are kernel-checked theorems. One states the count
through `card_degreeLT`. The others connect finite searches to statements about Mathlib
polynomials through the quantifier lemmas.
-/

public meta section

namespace CompPolyTests.UnivariateDegreeLT

open CompPoly CompPoly.CPolynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F : Type := ZMod 5

/-! ## Executable enumeration

The `#guard` lines evaluate the enumeration in compiled code. The one `example` in this section is
a kernel-checked theorem. -/

-- There are `5 ^ n` polynomials of degree below `n`.
#guard Fintype.card ↥(degreeLT (R := F) 2) = 25
#guard Fintype.card ↥(degreeLT (R := F) 3) = 125

-- Kernel-checked: `card_degreeLT` gives the same count as a theorem.
example : Fintype.card ↥(degreeLT (R := F) 3) = 125 := by
  rw [card_degreeLT, ZMod.card]
  norm_num

-- Degree below zero admits exactly one polynomial, the zero polynomial.
#guard Fintype.card ↥(degreeLT (R := F) 0) = 1
#guard ∀ p : ↥(degreeLT (R := F) 0), p.val = 0

-- The enumeration lists distinct polynomials, each within the degree bound.
#guard ((Finset.univ : Finset ↥(degreeLT (R := F) 2)).image (·.val)).card = 25
#guard ∀ p : ↥(degreeLT (R := F) 2), p.val.degree < 2

-- A search finds the known polynomial `(X - 1) * (X - 2)`.
#guard ∃ p : ↥(degreeLT (R := F) 3), p.val = (X - C 1) * (X - C 2)

-- The polynomials of degree below 3 that vanish at 1 and 2 are the five multiples of
-- `(X - 1) * (X - 2)`.
#guard (Finset.univ.filter fun p : ↥(degreeLT (R := F) 3) ↦
  p.val.eval 1 = 0 ∧ p.val.eval 2 = 0).card = 5

/-! ## Quantifier lemmas

Each `#guard` below evaluates a finite search over `↥(degreeLT n)` in compiled code. The kernel
does not evaluate the search. The `example` after each `#guard` is a kernel-checked theorem: the
search returns `true` exactly when the stated property of Mathlib polynomials holds. -/

-- Compiled check: every polynomial of degree below 2 with roots 1 and 2 is zero. The kernel-checked
-- example states that this search returns `true` exactly when the same holds for every Mathlib
-- polynomial over `ZMod 5` of degree below 2.
#guard ∀ p : ↥(degreeLT (R := F) 2), p.val.eval 1 = 0 → p.val.eval 2 = 0 → p.val = 0

example : decide (∀ p : ↥(degreeLT (R := F) 2),
      p.val.eval 1 = 0 → p.val.eval 2 = 0 → p.val = 0) = true ↔
    ∀ p : Polynomial F, p.degree < 2 → p.eval 1 = 0 → p.eval 2 = 0 → p = 0 := by
  rw [decide_eq_true_iff]
  simpa only [← eval_toPoly, toPoly_eq_zero_iff, Nat.cast_ofNat] using
    forall_degreeLT_toPoly_iff (R := F) 2 fun q ↦ q.eval 1 = 0 → q.eval 2 = 0 → q = 0

-- Compiled check: some polynomial of degree at most 2 has roots 1 and 2 and the coefficient 1 at
-- `X ^ 2`. The kernel-checked example states that this search returns `true` exactly when such a
-- Mathlib polynomial over `ZMod 5` exists.
#guard ∃ p : ↥(degreeLT (R := F) 3),
  p.val.degree ≤ 2 ∧ p.val.eval 1 = 0 ∧ p.val.eval 2 = 0 ∧ p.val.coeff 2 = 1

example : decide (∃ p : ↥(degreeLT (R := F) 3),
      p.val.degree ≤ 2 ∧ p.val.eval 1 = 0 ∧ p.val.eval 2 = 0 ∧ p.val.coeff 2 = 1) = true ↔
    ∃ p : Polynomial F, p.degree ≤ 2 ∧ p.eval 1 = 0 ∧ p.eval 2 = 0 ∧ p.coeff 2 = 1 := by
  rw [decide_eq_true_iff, ← exists_degreeLT_toPoly_iff_of_degree_lt 3
    (fun q ↦ q.degree ≤ 2 ∧ q.eval 1 = 0 ∧ q.eval 2 = 0 ∧ q.coeff 2 = 1)
    fun q hq ↦ lt_of_le_of_lt hq.1 (by decide)]
  simp only [← degree_toPoly, ← eval_toPoly, coeff_toPoly]

-- Compiled check: if two polynomials of degree below 2 vanish at 1, then their sum vanishes at 1.
-- The kernel-checked example states that this search returns `true` exactly when the same holds
-- for every pair of Mathlib polynomials over `ZMod 5` of degree below 2.
#guard ∀ f g : ↥(degreeLT (R := F) 2),
  f.val.eval 1 = 0 → g.val.eval 1 = 0 → (f.val + g.val).eval 1 = 0

example : decide (∀ f g : ↥(degreeLT (R := F) 2),
      f.val.eval 1 = 0 → g.val.eval 1 = 0 → (f.val + g.val).eval 1 = 0) = true ↔
    ∀ f g : Polynomial F, f.degree < 2 → g.degree < 2 →
      f.eval 1 = 0 → g.eval 1 = 0 → (f + g).eval 1 = 0 := by
  rw [decide_eq_true_iff]
  simpa only [← toPoly_add, ← eval_toPoly, Nat.cast_ofNat] using
    forall₂_degreeLT_toPoly_iff (R := F) 2 2
      fun f g ↦ f.eval 1 = 0 → g.eval 1 = 0 → (f + g).eval 1 = 0

end CompPolyTests.UnivariateDegreeLT
