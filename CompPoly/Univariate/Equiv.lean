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

-- HIGH LEVEL TODOs
-- * equivalence theorems for univariate polynomials to the mathlib definition
--   * OR since multivariate polynomials are already defined, should we just prove a special case ..?
-- * equivalence between canonical and raw polynomials
-- * Prove CPolynomial R isomorphic to CMvPolynomial Unit R?
-- * inspiration from MvPolyEquiv.lean

open Polynomial

/-- Convert a `Polynomial` to a `CPolynomial`. -/
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

/-- a more low-level and direct definition of `toPoly`; currently unused. -/
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

/-- evaluation stays the same after converting to mathlib -/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomial Q) : p.toPoly.eval x = p.eval x := by
  unfold toPoly eval eval₂
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp

/-- characterize `p.toPoly` by showing that its coefficients are exactly the coefficients of `p` -/
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

/-- helper lemma, to argue about `toImpl` by cases -/
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

/-- `toImpl` is a right-inverse of `toPoly`.
  that is, the round-trip starting from a mathlib polynomial gets us back to where we were.
  in particular, `toPoly` is surjective and `toImpl` is injective. -/
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

/-- `CPolynomial` addition is mapped to `Polynomial` addition -/
theorem toPoly_add {p q : CPolynomial Q} : (add_raw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, add_coeff?]

/-- trimming doesn't change the `toPoly` image -/
lemma toPoly_trim [LawfulBEq R] {p : CPolynomial R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]

/-- helper lemma to be able to state the next lemma -/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]

/-- helper lemma: the last entry of the `CPolynomial` obtained by `toImpl` is just the `leadingCoeff` -/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]

/-- `toImpl` maps to canonical `CPolynomial`s -/
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · rw [h, Trim.canonical_empty]
  rw [Trim.canonical_iff]
  unfold Array.getLast
  intro
  rw [getLast_toImpl h_nz]
  exact Polynomial.leadingCoeff_ne_zero.mpr h_nz

/-- on canonical `CPolynomial`s, `toImpl` is also a left-inverse of `toPoly`.
  in particular, `toPoly` is a bijection from `CPolynomialC` to `Polynomial`. -/
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

/-- the roundtrip to and from mathlib maps a `CPolynomial` to its trimmed/canonical representative -/
theorem toImpl_toPoly [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p.trim := by
  rw [← toPoly_trim]
  exact toImpl_toPoly_of_canonical ⟨ p.trim, Trim.trim_twice p⟩

/-- evaluation stays the same after converting a mathlib `Polynomial` to a `CPolynomial` -/
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- corollary: evaluation stays the same after trimming -/
lemma eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial R) : p.trim.eval x = p.eval x := by
  rw [← toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end ToPoly

end CPolynomial

end CompPoly
