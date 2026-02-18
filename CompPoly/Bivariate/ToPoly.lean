/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/

import CompPoly.Bivariate.Basic
import CompPoly.Univariate.ToPoly
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Equivalence with Mathlib Bivariate Polynomials

This file establishes the conversion from `CBivariate R` to Mathlib's `R[X][Y]`
(`Polynomial (Polynomial R)`).

The main definition is:
- `toPoly`: converts `CBivariate R` to `R[X][Y]`

Proofs that `toPoly` preserves evaluation, coefficients, degrees, etc. (and that it
forms an isomorphism with an inverse `ofPoly`) will be added as the implementation
is completed. The target interface matches ArkLib's `Polynomial.Bivariate` and
Mathlib's `Polynomial.Bivariate`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace CompPoly

namespace CBivariate

/-- Convert `CBivariate R` to Mathlib's bivariate polynomial `R[X][Y]`.

  Intended implementation: map each Y-coefficient (a `CPolynomial R`) through
  `CPolynomial.toPoly` to obtain `Polynomial R`, then build `Polynomial (Polynomial R)`
  via `eval₂` (analogous to univariate `Raw.toPoly`).
  -/
noncomputable def toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]
    (p : CBivariate R) : R[X][Y] := sorry

/-- Convert Mathlib's `R[X][Y]` to `CBivariate R` (inverse of `toPoly`).

  Intended implementation: extract each Y-coefficient via `p.coeff`, convert to
  `CPolynomial R` via `Polynomial.toImpl`, then build canonical bivariate.
  TODO: implement and prove round-trip lemmas. -/
noncomputable def ofPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]
    (p : R[X][Y]) : CBivariate R := sorry

-- TODO: toPoly_ofPoly, ofPoly_toPoly (round-trips), ring equiv, evalEval/toPoly compatibility

end CBivariate

end CompPoly
