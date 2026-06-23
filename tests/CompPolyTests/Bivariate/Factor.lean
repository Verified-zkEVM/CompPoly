/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Factor

/-!
  # Bivariate Factorisation Tests

  Lightweight regressions for `evalYPoly`, `isLinearYFactor`, and `divByLinearY`
  over `ℚ`: the synthetic-division specification, the remainder/evaluation
  identity, exactness, and the degenerate `0` / constant cases.
-/

namespace CompPoly
namespace CBivariate

-- Synthetic division identity `Q = quot * (Y - f) + rem` holds over `ℚ`.
example (Q : CBivariate ℚ) (f : CPolynomial ℚ) :
    toPoly Q =
      toPoly (divByLinearY Q f).1 * (Polynomial.X - Polynomial.C f.toPoly)
        + Polynomial.C ((divByLinearY Q f).2).toPoly := by
  simpa using divByLinearY_spec (R := ℚ) Q f

-- The remainder of synthetic division is the substitution `Q(X, f(X))`.
example (Q : CBivariate ℚ) (f : CPolynomial ℚ) :
    (divByLinearY Q f).2 = evalYPoly f Q :=
  divByLinearY_rem_eq_eval Q f

-- When `Y - f` divides `Q`, the division is exact.
example (Q : CBivariate ℚ) (f : CPolynomial ℚ) (h : isLinearYFactor Q f = true) :
    (divByLinearY Q f).2 = 0 :=
  divByLinearY_exact Q f h

-- `isLinearYFactor` matches the proposition `Q(X, f(X)) = 0`.
example (Q : CBivariate ℚ) (f : CPolynomial ℚ) :
    isLinearYFactor Q f = true ↔ evalYPoly f Q = 0 :=
  isLinearYFactor_iff Q f

-- Degenerate cases: dividing `0` and a `Y`-constant.
example (f : CPolynomial ℚ) : divByLinearY (0 : CBivariate ℚ) f = (0, 0) :=
  divByLinearY_zero f

example (a f : CPolynomial ℚ) :
    divByLinearY (CPolynomial.C a : CBivariate ℚ) f = (0, a) :=
  divByLinearY_const a f

end CBivariate
end CompPoly
