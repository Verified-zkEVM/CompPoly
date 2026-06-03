/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Formal Derivatives for Computable Univariate Polynomials
-/

namespace CompPoly

namespace CPolynomial

/-- Formal derivative of a canonical univariate polynomial. -/
def derivative {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CPolynomial R :=
  ofArray
    ((List.range (p.val.size - 1)).map fun i ↦
      ((i + 1 : Nat) : R) * p.coeff (i + 1)).toArray

/-- The executable formal derivative agrees with Mathlib's polynomial derivative. -/
theorem derivative_toPoly {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) :
    (CPolynomial.derivative p).toPoly = Polynomial.derivative p.toPoly := by
  apply Polynomial.ext
  intro n
  rw [← CPolynomial.coeff_toPoly]
  unfold CPolynomial.derivative
  rw [show
      (CPolynomial.ofArray
          ((List.range (p.val.size - 1)).map fun i ↦
            ((i + 1 : Nat) : R) * p.coeff (i + 1)).toArray).coeff n =
        ((List.range (p.val.size - 1)).map fun i ↦
          ((i + 1 : Nat) : R) * p.coeff (i + 1)).toArray.getD n 0 by
    unfold CPolynomial.coeff CPolynomial.ofArray
    rw [CPolynomial.Raw.Trim.coeff_eq_coeff]]
  rw [Polynomial.coeff_derivative]
  by_cases hn : n < p.val.size - 1
  · have hArray : n < (List.map (fun i ↦ ((i + 1 : Nat) : R) * p.coeff (i + 1))
        (List.range (p.val.size - 1))).toArray.size := by
      simp [hn]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hArray]
    simp
    have hcoeff : p.val[n + 1]?.getD 0 = p.toPoly.coeff (n + 1) := by
      simpa [CPolynomial.coeff, CPolynomial.Raw.coeff] using
        CPolynomial.coeff_toPoly p (n + 1)
    rw [hcoeff]
    simpa [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_commute (n + 1) (p.toPoly.coeff (n + 1))).eq
  · have hlen : (List.map (fun i ↦ ((i + 1 : Nat) : R) * p.coeff (i + 1))
        (List.range (p.val.size - 1))).toArray.size ≤ n := by
      simp [Nat.le_of_not_gt hn]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hlen]
    simp
    rw [← CPolynomial.coeff_toPoly p (n + 1)]
    unfold CPolynomial.coeff CPolynomial.Raw.coeff
    rw [Array.getD_eq_getD_getElem?]
    have hnsize : p.val.size ≤ n + 1 := by omega
    rw [Array.getElem?_eq_none hnsize]
    simp

end CPolynomial

end CompPoly
