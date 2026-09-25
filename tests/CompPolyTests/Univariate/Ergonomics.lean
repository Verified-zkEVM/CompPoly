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
