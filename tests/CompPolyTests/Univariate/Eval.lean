/-
Copyright (c) 2026 CompPoly, Elias Judin, Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic)
-/
import CompPoly.Univariate.ToPoly.Impl

/-!
  # Univariate Evaluation Regression Tests

  Regression tests for the Horner-style evaluation backend, covering:
  - Zero polynomial
  - Constant polynomials
  - Monomial
  - Trailing-zero polynomials
  - Nontrivial polynomials
  - Agreement with `toPoly` evaluation (Mathlib bridge)
-/

namespace CompPoly

open CPolynomial.Raw

-- ============================================================
-- Raw evaluation: eval₂ with RingHom.id ≡ eval
-- ============================================================

section ZeroPoly

-- eval of the zero polynomial should always be 0
#guard (eval 42 (#[] : CPolynomial.Raw ℤ)) == 0
#guard (eval 0 (#[] : CPolynomial.Raw ℤ)) == 0
#guard (eval (-7) (#[] : CPolynomial.Raw ℤ)) == 0

end ZeroPoly

section ConstPoly

-- eval of a constant polynomial should return that constant
#guard (eval 100 (C 5 : CPolynomial.Raw ℤ)) == 5
#guard (eval 0 (C 5 : CPolynomial.Raw ℤ)) == 5
#guard (eval (-3) (C 0 : CPolynomial.Raw ℤ)) == 0
#guard (eval 7 (C (-2) : CPolynomial.Raw ℤ)) == (-2)

end ConstPoly

section MonomialPoly

-- eval of X at various points
#guard (eval 0 (X : CPolynomial.Raw ℤ)) == 0
#guard (eval 1 (X : CPolynomial.Raw ℤ)) == 1
#guard (eval 5 (X : CPolynomial.Raw ℤ)) == 5
#guard (eval (-3) (X : CPolynomial.Raw ℤ)) == (-3)

-- eval of X^2 = monomial 2 1 = [0, 0, 1]
#guard (eval 3 (monomial 2 1 : CPolynomial.Raw ℤ)) == 9
#guard (eval (-2) (monomial 2 1 : CPolynomial.Raw ℤ)) == 4

end MonomialPoly

section TrailingZeros

-- Polynomial with trailing zeros: [1, 0, 0] represents constant 1
-- Evaluation should still give 1
#guard (eval 42 (mk #[(1 : ℤ), 0, 0])) == 1
#guard (eval 0 (mk #[(1 : ℤ), 0, 0])) == 1

-- [0, 1, 0] represents X (with trailing zero)
#guard (eval 5 (mk #[(0 : ℤ), 1, 0])) == 5
#guard (eval (-3) (mk #[(0 : ℤ), 1, 0])) == (-3)

end TrailingZeros

section NontrivialPoly

-- 1 + X at x=3 should be 4
private abbrev p1x : CPolynomial.Raw ℤ := mk #[1, 1]
#guard (eval 3 p1x) == 4
#guard (eval 0 p1x) == 1
#guard (eval (-1) p1x) == 0

-- 1 + 2X + 3X^2 at x=2 should be 1 + 4 + 12 = 17
private abbrev p123 : CPolynomial.Raw ℤ := mk #[1, 2, 3]
#guard (eval 2 p123) == 17
#guard (eval 0 p123) == 1
#guard (eval 1 p123) == 6
#guard (eval (-1) p123) == 2

-- 5 + 0*X + 3X^2 at x=2 should be 5 + 0 + 12 = 17
private abbrev p503 : CPolynomial.Raw ℤ := mk #[5, 0, 3]
#guard (eval 2 p503) == 17

end NontrivialPoly

section HornerNaiveAgreement

-- Verify Horner eval₂ agrees with naive eval₂ on concrete examples
#guard (eval₂ (RingHom.id ℤ) 3 p1x) == (eval₂Naive (RingHom.id ℤ) 3 p1x)
#guard (eval₂ (RingHom.id ℤ) 2 p123) == (eval₂Naive (RingHom.id ℤ) 2 p123)
#guard (eval₂ (RingHom.id ℤ) (-1) p123) == (eval₂Naive (RingHom.id ℤ) (-1) p123)
#guard (eval₂ (RingHom.id ℤ) 0 (#[] : CPolynomial.Raw ℤ)) ==
       (eval₂Naive (RingHom.id ℤ) 0 (#[] : CPolynomial.Raw ℤ))

end HornerNaiveAgreement

section ToPolyAgreement

-- Verify eval agrees with toPoly evaluation via proved bridge theorems

example : CPolynomial.Raw.eval 3 p1x = p1x.toPoly.eval 3 := by
  rw [CPolynomial.Raw.eval_toPoly_eq_eval]

example : CPolynomial.Raw.eval 2 p123 = p123.toPoly.eval 2 := by
  rw [CPolynomial.Raw.eval_toPoly_eq_eval]

-- eval₂ bridge
example : CPolynomial.Raw.eval₂ (RingHom.id ℤ) 2 p123 =
          p123.toPoly.eval₂ (RingHom.id ℤ) 2 := by
  exact CPolynomial.Raw.eval₂_toPoly (RingHom.id ℤ) 2 p123

end ToPolyAgreement

end CompPoly
