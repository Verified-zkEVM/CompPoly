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

  Maps each Y-coefficient through `CPolynomial.toPoly`, then builds
  `Polynomial (Polynomial R)` as the sum of monomials.
  -/
noncomputable def toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p : CBivariate R) : R[X][Y] :=
  (CPolynomial.support p).sum (fun j =>
    monomial j (CPolynomial.toPoly (p.val.coeff j)))

/-- Convert Mathlib's `R[X][Y]` to `CBivariate R` (inverse of `toPoly`).

  Extracts each Y-coefficient via `p.coeff`, converts to `CPolynomial R` via
  `toImpl` and trimming, then builds the canonical bivariate sum.
  -/
def ofPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (p : R[X][Y]) : CBivariate R :=
  (p.support).sum (fun j =>
    let cj := p.coeff j
    CPolynomial.monomial j ⟨cj.toImpl, CPolynomial.Raw.trim_toImpl cj⟩)

-- TODO: toPoly_ofPoly, ofPoly_toPoly (round-trips), ring equiv, evalEval/toPoly compatibility

end CBivariate

end CompPoly
