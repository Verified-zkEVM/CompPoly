/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen, Elias Judin
-/
module

public meta import CompPoly.Univariate.Raw.Division
public meta import CompPoly.Univariate.Basic

/-!
  # Univariate Raw Regression Tests

  Lightweight regression checks for `CompPoly.Univariate.Raw`.

  The `divByMonic`/`modByMonic` operations over `ℚ` do not reduce by `decide`
  or `rfl` because `ℚ` normalization is not definitionally computable. These
  regressions are checked at meta-level via `#guard`.
-/

public meta section

open CompPoly CPolynomial.Raw

-- Regression test for issue #115: (X^2 - 1) / (X + 1) = X - 1
#guard
  divByMonic ((X : CPolynomial.Raw ℚ) ^ 2 - C 1) ((X : CPolynomial.Raw ℚ) + C 1)
    == #[-(1 : ℚ), 1]

#guard
  modByMonic ((X : CPolynomial.Raw ℚ) ^ 2 - C 1) ((X : CPolynomial.Raw ℚ) + C 1)
    == #[]

-- Regression test for review-thread case: X^3 = (X^2 + 1) * X + (-X)
#guard
  divByMonic ((X : CPolynomial.Raw ℚ) ^ 3) ((X : CPolynomial.Raw ℚ) ^ 2 + C 1)
    == #[(0 : ℚ), 1]

#guard
  modByMonic ((X : CPolynomial.Raw ℚ) ^ 3) ((X : CPolynomial.Raw ℚ) ^ 2 + C 1)
    == #[(0 : ℚ), -(1 : ℚ)]

/-! Evaluation compiles to Horner's method through `@[csimp]` lemmas (issue #186). These checks
run the compiled `eval`/`eval₂` and compare with hand-computed values and with `evalHorner`. -/

-- 1 + 2X + 3X² at X = 2 is 17
#guard eval (2 : ℤ) (#[1, 2, 3] : CPolynomial.Raw ℤ) == 17
#guard eval₂ (Int.castRingHom ℚ) (1 / 2 : ℚ) (#[1, 2, 3] : CPolynomial.Raw ℤ) == 11 / 4
#guard eval (5 : ℤ) (#[] : CPolynomial.Raw ℤ) == 0
#guard eval (-3 : ℤ) (#[4, 0, 0, 1] : CPolynomial.Raw ℤ) == -23
#guard eval (7 : ℤ) (#[4, 0, 0, 1] : CPolynomial.Raw ℤ) ==
  evalHorner (7 : ℤ) (#[4, 0, 0, 1] : CPolynomial.Raw ℤ)
#guard CPolynomial.eval (2 : ℚ) ((CPolynomial.X : CPolynomial ℚ) ^ 3 - CPolynomial.C 1) == 7
#guard CPolynomial.eval₂ (Int.castRingHom ℚ) (1 / 3 : ℚ)
  ((CPolynomial.X : CPolynomial ℤ) ^ 2 + CPolynomial.C 2) == 19 / 9
