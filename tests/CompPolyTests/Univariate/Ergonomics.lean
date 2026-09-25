/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Bivariate.ToPoly
public import CompPoly.Multilinear.Basic
public import CompPoly.Univariate.Deriv
public import CompPoly.Univariate.ToPoly

/-!
  # Proof-Ergonomics Regression Tests

  Routine univariate, bivariate and multilinear goals that the default `simp` and `grind` sets
  must close with no arguments. A failure here means a lemma has left, or has not joined, the
  simp or grind set described in `docs/wiki/representations-and-bridges.md`.
-/

@[expose] public section

namespace CompPoly.CPolynomial.ErgonomicsTests

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-! ### Pushing `toPoly` through an expression -/

example (p q : CPolynomial R) (a : R) :
    (p * q + C a).toPoly = p.toPoly * q.toPoly + Polynomial.C a := by simp

example (p q : CPolynomial R) (a : R) :
    (p * q + C a).toPoly = p.toPoly * q.toPoly + Polynomial.C a := by grind

example (p : CPolynomial R) (n : ℕ) :
    (X * p ^ n - 1).toPoly = Polynomial.X * p.toPoly ^ n - 1 := by simp

/-! ### Evaluation -/

example (p q : CPolynomial R) (x : R) :
    (p * q + 1).eval x = p.eval x * q.eval x + 1 := by simp

example (p q : CPolynomial R) (x : R) :
    (p * q + 1).eval x = p.eval x * q.eval x + 1 := by grind

example (x : R) : (X ^ 2 - C 3 : CPolynomial R).eval x = x ^ 2 - 3 := by simp

example {ι : Type*} (s : Finset ι) (f : ι → CPolynomial R) (x : R) :
    (∑ i ∈ s, X * f i).eval x = ∑ i ∈ s, x * (f i).eval x := by simp

/-! ### Equalities by transfer to Mathlib -/

example (p q : CPolynomial R) :
    derivative (p * q) = derivative p * q + p * derivative q :=
  toPoly_inj.mp (by simp [Polynomial.derivative_mul])

example (p : CPolynomial R) : C (1 : R) * p = p := toPoly_inj.mp (by simp)

example (p : CPolynomial R) : (p.toPoly = 0) ↔ p = 0 := by simp

/-! ### Transfer from Mathlib through the `toPoly` coercion -/

section Cast

variable {S : Type*} [CommRing S] [IsDomain S] [BEq S] [LawfulBEq S]

-- Degree of a product, from `Polynomial.natDegree_mul`, with both side conditions cast.
example (p q : CPolynomial S) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  exact_mod_cast Polynomial.natDegree_mul (p := (p : Polynomial S)) (q := q)
    (by exact_mod_cast hp) (by exact_mod_cast hq)

example (p q : CPolynomial S) : (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  exact_mod_cast Polynomial.leadingCoeff_mul (p : Polynomial S) q

example (p q : CPolynomial S) : (p + q).degree ≤ max p.degree q.degree := by
  exact_mod_cast Polynomial.degree_add_le (p : Polynomial S) q

example (p : CPolynomial S) (n : ℕ) : (p ^ n).natDegree = n * p.natDegree := by
  exact_mod_cast Polynomial.natDegree_pow (p : Polynomial S) n

-- A statement about `X` or `C` needs one more step: unfold the query into Mathlib's and
-- `push_cast` it, since `C_toPoly` cannot be a `norm_cast` lemma.
example (p : CPolynomial S) (n : ℕ) : (X * p).coeff (n + 1) = p.coeff n := by
  rw [← toPoly_coeff]
  push_cast
  exact_mod_cast Polynomial.coeff_X_mul (p := (p : Polynomial S)) (n := n)

-- A root of `p` gives divisibility in Mathlib's terms.
example (p : CPolynomial S) (a : S) (h : p.eval a = 0) :
    Polynomial.X - Polynomial.C a ∣ (p : Polynomial S) :=
  Polynomial.dvd_iff_isRoot.mpr (by rw [Polynomial.IsRoot.def]; exact_mod_cast h)

end Cast

/-! ### Degree arithmetic without leaving `CPolynomial` -/

section Degree

variable {S : Type*} [CommRing S] [IsDomain S] [BEq S] [LawfulBEq S]

-- The simp set computes the degree of a product of linear factors.
example (a b : S) : ((X - C a) * (X - C b)).degree = 2 := by
  simp [one_add_one_eq_two]

example (a : S) (n : ℕ) : ((X - C a) ^ n).natDegree = n := by simp

example (p : CPolynomial S) : (-p * X).leadingCoeff = -p.leadingCoeff := by simp

-- The bounds are named lemmas, as in Mathlib.
example (p q : CPolynomial R) :
    (p * q - p).natDegree ≤ max (p.natDegree + q.natDegree) p.natDegree :=
  (natDegree_sub_le _ _).trans (max_le_max_right _ (natDegree_mul_le p q))

example (p : CPolynomial R) (n : ℕ) (h : p.natDegree ≤ 3) : (p ^ n).natDegree ≤ n * 3 :=
  natDegree_pow_le_of_le n h

example (p : CPolynomial R) (i : ℕ) (h : p.natDegree < i) : p.coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt h

end Degree

/-! ### Bivariate transport -/

example (p q : CBivariate R) (a : R) :
    CBivariate.toPoly (p * q + CBivariate.CC a) =
      CBivariate.toPoly p * CBivariate.toPoly q + Polynomial.C (Polynomial.C a) := by simp

example [DecidableEq R] : CBivariate.toPoly (CBivariate.X * CBivariate.Y : CBivariate R) =
    Polynomial.C Polynomial.X * Polynomial.X := by simp

/-! ### Multilinear evaluation -/

example {n : ℕ} (p q : CMlPolynomial R n) (a : R) (x : Vector R n) :
    CMlPolynomial.eval (a • p + q) x = a * CMlPolynomial.eval p x + CMlPolynomial.eval q x := by
  simp

example {n : ℕ} (p q : CMlPolynomialEval R n) (x : Vector R n) :
    CMlPolynomialEval.eval (p + 0 + q) x =
      CMlPolynomialEval.eval p x + CMlPolynomialEval.eval q x := by simp

end CompPoly.CPolynomial.ErgonomicsTests
