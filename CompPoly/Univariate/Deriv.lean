/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly.Impl
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Formal Derivative and Taylor Shift of Computable Univariate Polynomials

Defines the formal derivative `CPolynomial.derivative` and the Taylor shift
`CPolynomial.taylor`, with proofs of their core properties.
-/

namespace CompPoly

namespace CPolynomial

/-- The formal derivative of a computable polynomial.
    Coefficient `n` of the result is `coeff p (n+1) * (n+1)`. -/
def derivative [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CPolynomial R :=
  let arr : Array R :=
    (p.val.extract 1 p.val.size).mapIdx
      fun i c => c * (Nat.cast (i + 1) : R)
  ⟨(Raw.mk arr).trim, Raw.Trim.isCanonical_trim _⟩

/-- Coefficient formula for the derivative. -/
theorem coeff_derivative [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (↑(n + 1) : R) := by
  simp only [derivative, coeff, Raw.Trim.coeff_eq_coeff, Raw.coeff, Raw.mk]
  by_cases hn : n + 1 < Array.size p.val
  · unfold Array.getD
    simp only [Array.size_mapIdx, Array.size_extract, Nat.min_self,
          hn, dite_true]
    split
    · simp [Array.getElem_mapIdx, Array.getElem_extract, Nat.add_comm 1 n]
    · omega
  · unfold Array.getD
    simp only [Array.size_mapIdx, Array.size_extract, Nat.min_self,
          hn, dite_false]
    split
    · omega
    · simp


/-- The derivative of the zero polynomial is zero. -/
theorem derivative_zero [Semiring R] [BEq R] [LawfulBEq R] :
    derivative (0 : CPolynomial R) = 0 := by
  rw [eq_zero_iff_coeff_zero]
  intro i
  rw [coeff_derivative, CPolynomial.coeff_zero]
  simp

/-- The derivative of a constant is zero. -/
theorem derivative_C [Semiring R] [BEq R] [LawfulBEq R] (r : R) :
    derivative (C r) = 0 := by
  rw [eq_zero_iff_coeff_zero]
  intro i
  rw [coeff_derivative, CPolynomial.coeff_C]
  simp

/-- The derivative of a monomial. -/
theorem derivative_monomial [Semiring R] [BEq R] [LawfulBEq R]
    [DecidableEq R] (n : ℕ) (r : R) :
    derivative (monomial n r) =
      monomial (n - 1) (r * (↑n : R)) := by
  rw [eq_iff_coeff]
  intro i
  rw [coeff_derivative, coeff_monomial, coeff_monomial]
  split_ifs <;> simp_all
  · omega
  · have : n = 0 := by omega
    simp [this]

/-- The derivative distributes over addition. -/
theorem derivative_add [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (p q : CPolynomial R) :
    derivative (p + q) = derivative p + derivative q := by
  rw [eq_iff_coeff]
  intro i
  simp only [coeff_derivative, coeff_add]
  exact right_distrib _ _ _

/-- The computable derivative matches Mathlib's `Polynomial.derivative` under `toPoly`. -/
theorem derivative_toPoly [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (derivative p).toPoly = Polynomial.derivative (R := R) p.toPoly := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_derivative, CPolynomial.toPoly,
    Raw.coeff_toPoly, CPolynomial.coeff_derivative]
  push_cast; ring_nf

/-- The derivative satisfies the Leibniz product rule. -/
theorem derivative_mul [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (p q : CPolynomial R) :
    derivative (p * q) = derivative p * q + p * derivative q := by
  apply ringEquiv.injective
  change (derivative (p * q)).toPoly = (derivative p * q + p * derivative q).toPoly
  rw [derivative_toPoly, toPoly_mul, toPoly_add, toPoly_mul, toPoly_mul,
    derivative_toPoly, derivative_toPoly, Polynomial.derivative_mul]

/-- The Taylor shift `taylor a p = p(X + a)`. -/
def taylor [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) : CPolynomial R :=
  (support p).sum fun m => C (p.coeff m) * (X + C a) ^ m

/-- The computable Taylor shift matches `Polynomial.taylor` under `toPoly`. -/
theorem taylor_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) :
    (taylor a p).toPoly = Polynomial.taylor a p.toPoly := by
  unfold taylor
  rw [toPoly_sum, Polynomial.taylor_apply, Polynomial.comp, Polynomial.eval₂_eq_sum,
    Polynomial.sum, ← support_toPoly]
  apply Finset.sum_congr rfl
  intro m _
  rw [toPoly_mul, toPoly_pow, toPoly_add, C_toPoly, X_toPoly, C_toPoly, coeff_toPoly]

/-- The Taylor shift of zero is zero. -/
theorem taylor_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) : taylor a (0 : CPolynomial R) = 0 := by
  unfold taylor
  rw [(support_empty_iff 0).mpr rfl, Finset.sum_empty]

/-- The constant coefficient of the Taylor shift is evaluation at the shift point. -/
theorem taylor_coeff_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) : coeff (taylor a p) 0 = eval a p := by
  rw [coeff_toPoly, taylor_toPoly, Polynomial.taylor_coeff_zero, eval_toPoly]

end CPolynomial

end CompPoly
