/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Canonical

/-!
  # Equivalence with Mathlib Polynomials

  This file establishes the equivalence between `CPolynomial R` and mathlib's `Polynomial R`.
  The main results (thus far) are:
  - `toPoly`: converts `CPolynomial R` to `Polynomial R`
  - `ofPoly` (aliased from `Polynomial.toImpl`): converts `Polynomial R` to `CPolynomial R`
  - `toPoly_toImpl`: the round-trip from `Polynomial` is the identity
  - `toImpl_toPoly_of_canonical`: the round-trip from canonical `CPolynomial` is the identity

  This shows that `CPolynomialC R` is isomorphic to `Polynomial R`.

  HIGH LEVEL TODOs:
  - equivalence theorems for univariate polynomials to the mathlib definition
    - OR since multivariate polynomials are already defined, should we just prove a special case ..?
  - equivalence between canonical and raw polynomials
  - Prove CPolynomial R isomorphic to CMvPolynomial Unit R?
  - inspiration from MvPolyEquiv.lean
-/

open Polynomial

/-- Convert a mathlib `Polynomial` to a `CPolynomial` by extracting coefficients up to the degree. -/
def Polynomial.toImpl {R : Type*} [Semiring R] (p : R[X]) : CompPoly.CPolynomial R :=
  match p.degree with
  | ⊥ => #[]
  | some d  => .ofFn (fun i : Fin (d + 1) => p.coeff i)

namespace CompPoly

namespace CPolynomial
variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

section ToPoly

/-- Convert a `CPolynomial` to a (mathlib) `Polynomial`. -/
noncomputable def toPoly (p : CPolynomial R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Alternative definition of `toPoly` using `Finsupp`; currently unused. -/
noncomputable def toPoly' (p : CPolynomial R) : Polynomial R :=
  Polynomial.ofFinsupp (Finsupp.onFinset (Finset.range p.size) p.coeff (by
    intro n hn
    rw [Finset.mem_range]
    by_contra! h
    have h' : p.coeff n = 0 := by simp [h]
    contradiction
  ))

noncomputable def CPolynomialC.toPoly (p : CPolynomialC R) : Polynomial R := p.val.toPoly

alias ofPoly := Polynomial.toImpl

/-- Evaluation is preserved by `toPoly`. -/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomial Q) : p.toPoly.eval x = p.eval x := by
  unfold toPoly eval eval₂
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp

/-- The coefficients of `p.toPoly` match those of `p`. -/
lemma coeff_toPoly {p : CPolynomial Q} {n : ℕ} : p.toPoly.coeff n = p.coeff n := by
  unfold toPoly eval₂

  let f := fun (acc: Q[X]) ((a,i): Q × ℕ) ↦ acc + Polynomial.C a * Polynomial.X ^ i
  change (Array.foldl f 0 p.zipIdx).coeff n = p.coeff n

  -- we slightly weaken the goal, to use `Array.foldl_induction`
  let motive (size: ℕ) (acc: Q[X]) := acc.coeff n = if (n < size) then p.coeff n else 0

  have zipIdx_size : p.zipIdx.size = p.size := by simp [Array.zipIdx]

  suffices h : motive p.zipIdx.size (Array.foldl f 0 p.zipIdx) by
    rw [h, ite_eq_left_iff, zipIdx_size]
    intro hn
    replace hn : n ≥ p.size := by linarith
    rw [coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn, Option.getD_none]

  apply Array.foldl_induction motive
  · change motive 0 0
    simp [motive]

  change ∀ (i : Fin p.zipIdx.size) acc, motive i acc → motive (i + 1) (f acc p.zipIdx[i])
  unfold motive f
  intros i acc h
  have i_lt_p : i < p.size := by linarith [i.is_lt]
  have : p.zipIdx[i] = (p[i], ↑i) := by simp [Array.getElem_zipIdx]
  rw [this, coeff_add, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, h]
  rcases (Nat.lt_trichotomy i n) with hlt | rfl | hgt
  · have h1 : ¬ (n < i) := by linarith
    have h2 : ¬ (n = i) := by linarith
    have h3 : ¬ (n < i + 1) := by linarith
    simp [h1, h2, h3]
  · simp [i_lt_p]
  · have h1 : ¬ (n = i) := by linarith
    have h2 : n < i + 1 := by linarith
    simp [hgt, h1, h2]

/-- Case analysis for `toImpl`: either the polynomial is zero or has a specific form. -/
lemma toImpl_elim (p : Q[X]) :
    (p = 0 ∧ p.toImpl = #[])
  ∨ (p ≠ 0 ∧ p.toImpl = .ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) := by
  unfold toImpl
  by_cases hbot : p.degree = ⊥
  · left
    use degree_eq_bot.mp hbot
    rw [hbot]
  right
  use degree_ne_bot.mp hbot
  have hnat : p.degree = p.natDegree := degree_eq_natDegree (degree_ne_bot.mp hbot)
  simp [hnat]

/-- `toImpl` is a right-inverse of `toPoly`: the round-trip from `Polynomial` is the identity.

  This shows `toPoly` is surjective and `toImpl` is injective. -/
theorem toPoly_toImpl {p : Q[X]} : p.toImpl.toPoly = p := by
  ext n
  rw [coeff_toPoly]
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨_, h⟩
  · simp [h]
  rw [h]
  by_cases h : n < p.natDegree + 1
  · simp [h]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, reduceDIte, Option.getD_none]
  replace h := Nat.lt_of_succ_le (not_lt.mp h)
  symm
  exact coeff_eq_zero_of_natDegree_lt h

/-- `toPoly` preserves addition. -/
theorem toPoly_add {p q : CPolynomial Q} : (add_raw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, add_coeff?]

/-- Trimming doesn't change the `toPoly` image. -/
lemma toPoly_trim [LawfulBEq R] {p : CPolynomial R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]

/-- Non-zero polynomials map to non-empty arrays. -/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]

/-- The last coefficient of `toImpl p` is the leading coefficient of `p`. -/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]

/-- `toImpl` produces canonical polynomials (no trailing zeros). -/
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · rw [h, Trim.canonical_empty]
  rw [Trim.canonical_iff]
  unfold Array.getLast
  intro
  rw [getLast_toImpl h_nz]
  exact Polynomial.leadingCoeff_ne_zero.mpr h_nz

/-- On canonical polynomials, `toImpl` is a left-inverse of `toPoly`.

  This shows `toPoly` is a bijection from `CPolynomialC R` to `Polynomial R`. -/
lemma toImpl_toPoly_of_canonical [LawfulBEq R] (p : CPolynomialC R) : p.toPoly.toImpl = p := by
  -- we will change something slightly more general: `toPoly` is injective on canonical polynomials
  suffices h_inj : ∀ q : CPolynomialC R, p.toPoly = q.toPoly → p = q by
    have : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
    exact h_inj ⟨ p.toPoly.toImpl, trim_toImpl p.toPoly ⟩ this |> congrArg Subtype.val |>.symm
  intro q hpq
  apply CPolynomialC.ext
  apply Trim.canonical_ext p.property q.property
  intro i
  rw [← coeff_toPoly, ← coeff_toPoly]
  exact hpq |> congrArg (fun p => p.coeff i)

/-- The round-trip from `CPolynomial` to `Polynomial` and back yields the canonical form. -/
theorem toImpl_toPoly [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p.trim := by
  rw [← toPoly_trim]
  exact toImpl_toPoly_of_canonical ⟨ p.trim, Trim.trim_twice p⟩

/-- Evaluation is preserved by `toImpl`. -/
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- Evaluation is unchanged by trimming. -/
lemma eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial R) : p.trim.eval x = p.eval x := by
  rw [← toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end ToPoly

end CPolynomial

end CompPoly
