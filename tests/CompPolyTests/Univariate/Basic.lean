/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.Basic

/-!
  # Univariate Basic Tests

  First-pass sanity checks for key API behavior in `CompPoly.Univariate.Basic`.
-/

namespace CompPoly
namespace CPolynomial

-- TODO: expand this file with more operation-level regression checks.

example (r : ℚ) : (C r).coeff 0 = r := by
  simpa using coeff_C (R := ℚ) r 0

example (r : ℚ) : (C r).coeff 3 = 0 := by
  simpa using coeff_C (R := ℚ) r 3

example : (X : CPolynomial ℚ).coeff 1 = 1 := by
  decide

example (p : CPolynomial ℚ) : (divX p).coeff 2 = p.coeff 3 := by
  simpa using coeff_divX (R := ℚ) p 2

example (p : CPolynomial ℚ) : p + 0 = p := by
  simp

example (p : CPolynomial ℚ) : 0 + p = p := by
  simp

example (p : CPolynomial ℚ) : p * 0 = 0 := by
  simp

example (p : CPolynomial ℚ) : 1 * p = p := by
  simp

end CPolynomial

-- Power regression tests: canonical powers agree with repeated multiplication
section PowerTests

open CPolynomial.Raw

private abbrev p1x : CPolynomial.Raw ℤ := CPolynomial.Raw.mk #[1, 1]

-- Zero polynomial: 0^n = 0 for n ≥ 1
#guard (0 : CPolynomial.Raw ℤ) ^ 0 == C 1
#guard (0 : CPolynomial.Raw ℤ) ^ 1 == (0 : CPolynomial.Raw ℤ)
#guard (0 : CPolynomial.Raw ℤ) ^ 5 == (0 : CPolynomial.Raw ℤ)

-- Constant: (C 3)^n = C (3^n)
#guard (C 3 : CPolynomial.Raw ℤ) ^ 0 == C 1
#guard (C 3 : CPolynomial.Raw ℤ) ^ 1 == C 3
#guard (C 3 : CPolynomial.Raw ℤ) ^ 2 == C 9
#guard (C 3 : CPolynomial.Raw ℤ) ^ 3 == C 27

-- Monomial: X^n
#guard (X : CPolynomial.Raw ℤ) ^ 0 == C 1
#guard (X : CPolynomial.Raw ℤ) ^ 1 == (X : CPolynomial.Raw ℤ)
#guard (X : CPolynomial.Raw ℤ) ^ 3 == CPolynomial.Raw.mk #[(0 : ℤ), 0, 0, 1]

-- Nontrivial: (1 + X)^n = binomial coefficients
#guard p1x ^ 0 == C 1
#guard p1x ^ 1 == p1x
#guard p1x ^ 2 == CPolynomial.Raw.mk #[(1 : ℤ), 2, 1]
#guard p1x ^ 3 == CPolynomial.Raw.mk #[(1 : ℤ), 3, 3, 1]
#guard p1x ^ 4 == CPolynomial.Raw.mk #[(1 : ℤ), 4, 6, 4, 1]

-- Agrees with repeated multiplication
#guard p1x ^ 3 == p1x * (p1x * p1x)
#guard p1x ^ 4 == p1x * (p1x * (p1x * p1x))

end PowerTests

end CompPoly
