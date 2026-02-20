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

/-- Round-trip from Mathlib: converting a polynomial to `CBivariate` and back is the identity. -/
theorem ofPoly_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : R[X][Y]) : toPoly (ofPoly p) = p := sorry

/-- Round-trip from `CBivariate`: converting to Mathlib and back is the identity. -/
theorem toPoly_ofPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : CBivariate R) : ofPoly (toPoly p) = p := sorry

/-- Ring equivalence between `CBivariate R` and Mathlib's `R[X][Y]`. -/
noncomputable def ringEquiv
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    CBivariate R ≃+* R[X][Y] where
  toFun := toPoly
  invFun := ofPoly
  left_inv := toPoly_ofPoly
  right_inv := ofPoly_toPoly
  map_mul' := sorry
  map_add' := sorry

/-- `toPoly` preserves full evaluation: `evalEval x y f = (toPoly f).evalEval x y`. -/
theorem evalEval_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (x y : R) (f : CBivariate R) :
    @CompPoly.CBivariate.evalEval R _ _ _ _ x y f = (toPoly f).evalEval x y := sorry

/-- `toPoly` preserves coefficients: coefficient of `X^i Y^j` matches. -/
theorem coeff_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) (i j : ℕ) :
    ((toPoly f).coeff j).coeff i = @CompPoly.CBivariate.coeff R _ _ _ _ f i j := sorry

/-- `toPoly` preserves Y-degree. -/
theorem natDegreeY_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) : (toPoly f).natDegree = f.natDegreeY := sorry

/-- `toPoly` preserves X-degree (max over Y-coefficients of their degree in X). -/
theorem degreeX_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) :
    (toPoly f).support.sup (fun j => ((toPoly f).coeff j).natDegree) = f.degreeX := sorry

end CBivariate

-- TODO correctness lemmas for operations and API functions

end CompPoly
