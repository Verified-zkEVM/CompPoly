/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Raw
import CompPoly.Univariate.Basic

/-!
  # Equivalence with Mathlib Polynomials

  This file establishes the equivalence between `CPolynomialRaw R` and mathlib's `Polynomial R`.
  The main results (thus far) are:
  - `toPoly`: converts `CPolynomialRaw R` to `Polynomial R`
  - `ofPoly` (aliased from `Polynomial.toImpl`): converts `Polynomial R` to `CPolynomialRaw R`
  - `toPoly_toImpl`: the round-trip from `Polynomial` is the identity
  - `toImpl_toPoly_of_canonical`: the round-trip from canonical `CPolynomialRaw` is the identity

  This shows that `CPolynomial R` is isomorphic to `Polynomial R`.
-/

open Polynomial

/-- Convert a mathlib `Polynomial` to a `CPolynomialRaw` by extracting coefficients
up to the degree. -/
def Polynomial.toImpl {R : Type*} [Semiring R] (p : R[X]) : CompPoly.CPolynomialRaw R :=
  match p.degree with
  | ⊥ => #[]
  | some d  => .ofFn (fun i : Fin (d + 1) => p.coeff i)

namespace CompPoly

namespace CPolynomialRaw

variable {R : Type*} [Ring R] [BEq R]

variable {Q : Type*} [Ring Q]

section ToPoly

/-- Convert a `CPolynomialRaw` to a (mathlib) `Polynomial`. -/
noncomputable def toPoly (p : CPolynomialRaw R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Alternative definition of `toPoly` using `Finsupp`; currently unused. -/
noncomputable def toPoly' (p : CPolynomialRaw R) : Polynomial R :=
  Polynomial.ofFinsupp (Finsupp.onFinset (Finset.range p.size) p.coeff (by
    intro n hn
    rw [Finset.mem_range]
    by_contra! h
    have h' : p.coeff n = 0 := by simp [h]
    contradiction
  ))

/-- Convert a canonical polynomial to a (mathlib) `Polynomial`. -/
noncomputable def CPolynomial.toPoly (p : CPolynomial R) : Polynomial R := p.val.toPoly

alias ofPoly := Polynomial.toImpl

/-- Evaluation is preserved by `toPoly`. -/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomialRaw Q) : p.toPoly.eval x = p.eval x := by
  unfold toPoly eval eval₂
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp

/-- The coefficients of `p.toPoly` match those of `p`. -/
lemma coeff_toPoly {p : CPolynomialRaw Q} {n : ℕ} : p.toPoly.coeff n = p.coeff n := by
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

/-- Trimming doesn't change the `toPoly` image. -/
@[grind =]
lemma toPoly_trim [LawfulBEq R] {p : CPolynomialRaw R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]

/-- `toPoly` preserves addition. -/
@[grind =]
theorem toPoly_addRaw {p q : CPolynomialRaw Q} : (addRaw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, add_coeff?]

@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomialRaw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  change (p.add q).toPoly = p.toPoly + q.toPoly; unfold add
  rw [toPoly_trim, toPoly_addRaw]

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
@[simp, grind =]
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · rw [h, Trim.canonical_empty]
  rw [Trim.canonical_iff]
  unfold Array.getLast
  intro
  rw [getLast_toImpl h_nz]
  exact Polynomial.leadingCoeff_ne_zero.mpr h_nz

/-- On canonical polynomials, `toImpl` is a left-inverse of `toPoly`.

  This shows `toPoly` is a bijection from `CPolynomial R` to `Polynomial R`. -/
@[grind =]
lemma toImpl_toPoly_of_canonical [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p := by
  -- we will change something slightly more general: `toPoly` is injective on canonical polynomials
  suffices h_inj : ∀ q : CPolynomial R, p.toPoly = q.toPoly → p = q by
    have : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
    exact h_inj ⟨ p.toPoly.toImpl, trim_toImpl p.toPoly ⟩ this |> congrArg Subtype.val |>.symm
  intro q hpq
  apply CPolynomial.ext
  apply Trim.canonical_ext p.property q.property
  intro i
  rw [← coeff_toPoly, ← coeff_toPoly]
  exact hpq |> congrArg (fun p => p.coeff i)

/-- The round-trip from `CPolynomialRaw` to `Polynomial` and back yields the canonical form. -/
@[simp, grind =]
theorem toImpl_toPoly [LawfulBEq R] (p : CPolynomialRaw R) : p.toPoly.toImpl = p.trim := by
  rw [← toPoly_trim]
  exact toImpl_toPoly_of_canonical ⟨ p.trim, Trim.trim_twice p⟩

/-- Evaluation is preserved by `toImpl`. -/
@[simp, grind =]
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- Evaluation is unchanged by trimming. -/
@[simp, grind =]
lemma eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomialRaw R) :
    p.trim.eval x = p.eval x := by
  rw [← toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end ToPoly

section RingEquiv

/-- Ring equivalence between canonical computable polynomials and Mathlib polynomials.

  This establishes that `CPolynomial R` and `Polynomial R` are isomorphic as rings.
  The equivalence is given by `toPoly` (evaluation-based conversion) and `toImpl`
  (coefficient extraction).

  **Prerequisites**: This can only be constructed after:
  1. `CPolynomial` has a `Semiring`/`CommSemiring` instance (see `Canonical.lean`)
  2. We prove that `toPoly` preserves multiplication (see `toPoly_mul` below)
  3. We prove that `toPoly` preserves addition for trimmed polynomials

  TODO: Construct this ring equivalence once prerequisites are met.
-/
@[grind =]
lemma toPoly_mul_coeff [LawfulBEq R] (p q : CPolynomialRaw R) (i : ℕ) :
    (p * q).toPoly.coeff i = (p.toPoly * q.toPoly).coeff i := by
  rw [coeff_toPoly, mul_coeff, Polynomial.coeff_mul]; simp
  -- equality of indices
  have h_antidiagonal :
      Finset.HasAntidiagonal.antidiagonal i =
      Finset.image (fun x => (x, i - x)) (Finset.range (i + 1)) := by
    exact Finset.Nat.antidiagonal_eq_image i
  simp [h_antidiagonal ]
  -- equality of terms
  have h_coeff : ∀ x, p.toPoly.coeff x = p[x]?.getD 0 ∧ q.toPoly.coeff x = q[x]?.getD 0 := by
    intro x
    repeat rw [coeff_toPoly]
    constructor <;> simp
  grind

@[grind =]
lemma toPoly_mul_coeffC [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p.val * q.val).toPoly.coeff i = (p.val.toPoly * q.val.toPoly).coeff i := by grind

/-- Converting the product of two canonical polynomials to a mathlib `Polynomial` is the same as
  the product of their conversions: `(p * q).toPoly = p.toPoly * q.toPoly`. -/
@[grind =]
lemma toPoly_mul [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  convert Polynomial.ext (toPoly_mul_coeff p.val q.val)

/-- Converting the sum of two raw polynomials to a mathlib `Polynomial` is the same as the sum of
  their conversions: `(p + q).toPoly = p.toPoly + q.toPoly`. -/
@[grind =]
lemma toPoly_addC [CommSemiring R] [LawfulBEq R] (p q : CPolynomialRaw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by rw [toPoly_add]

/-
Evaluating the constant polynomial `C r` yields `f r`.
-/
@[simp, grind =]
lemma eval₂_C {R : Type*} [Ring R] [BEq R] {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (r : R) :
    (C r).eval₂ f x = f r := by
  unfold CPolynomialRaw.eval₂ C
  ring_nf
  simp [Array.zipIdx]

/-
Converting the constant polynomial `C r` to a `Polynomial` yields `Polynomial.C r`.
-/
@[simp, grind =]
lemma toPoly_C {R : Type*} [Ring R] [BEq R] (r : R) :
    (C r).toPoly = Polynomial.C r := by
  unfold toPoly
  exact eval₂_C Polynomial.C Polynomial.X r

/--
`toPoly` preserves the multiplicative identity
-/
@[simp, grind =]
lemma toPoly_one [CommSemiring R] [LawfulBEq R] :
    (1 : CPolynomialRaw R).toPoly = 1 := by
  have : (1 : CPolynomialRaw R).toPoly = (C 1).toPoly := by rfl
  apply this.trans; clear this
  apply toPoly_C

/-- The ring equivalence sends the canonical variable `X` to `Polynomial.X`. -/
@[simp, grind =]
lemma toPoly_X [LawfulBEq R] :
    (X : CPolynomialRaw R).toPoly = Polynomial.X := by
  unfold CPolynomialRaw.X
  simp [toPoly, eval₂]

/--
`toPoly` preserves the additive identity
-/
@[simp, grind =]
lemma toPoly_zero [CommSemiring R] [LawfulBEq R] :
    (0 : CPolynomialRaw R).toPoly = 0 := by simp [toPoly, eval₂]

/-- Ring equivalence between canonical computable polynomials and mathlib's `Polynomial R`.

  `CPolynomial R` (polynomials with no trailing zeros) is isomorphic as a ring to `Polynomial R`.
  The forward map is `CPolynomial.toPoly`; the inverse sends `p : Polynomial R` to
  `⟨p.toImpl, trim_toImpl p⟩` (the canonical polynomial whose underlying array is `p.toImpl`). -/
noncomputable def ringEquiv [LawfulBEq R] :
  CPolynomial R ≃+* Polynomial R where
  toFun := CPolynomial.toPoly
  invFun := fun p => ⟨p.toImpl, trim_toImpl p⟩
  left_inv := by
    unfold Function.LeftInverse; intro x
    apply Subtype.ext; apply toImpl_toPoly_of_canonical
  right_inv := by
    unfold Function.RightInverse CPolynomial.toPoly
    apply toPoly_toImpl
  map_mul' := by intros p q; rw [toPoly_mul p q]
  map_add' := by intros p q; apply toPoly_add


end RingEquiv

end CPolynomialRaw

end CompPoly
