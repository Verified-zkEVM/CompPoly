/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/

import CompPoly.Univariate.Basic

/-!
# Computable Bivariate Polynomials

This file defines `Bivariate R`, the computable representation of bivariate polynomials with
coefficients in `R`. The type is `CPolynomial (CPolynomial R)`, i.e. polynomials in `Y` with
coefficients that are polynomials in `X`, matching Mathlib's `R[X][Y]`
(i.e. `Polynomial (Polynomial R)`).

The design is intended to be compatible with:
- Mathlib's `Polynomial.Bivariate` (see `CompPoly/Bivariate/ToPoly.lean`)
- ArkLib's `Polynomial.Bivariate` interface (see ArkLib/Data/Polynomial/Bivariate.lean and
  ArkLib/Data/CodingTheory/PolishchukSpielman/Degrees.lean, BCIKS20.lean, etc.)
-/

namespace CompPoly

/-- Computable bivariate polynomials: `F[X][Y]` as `CPolynomial (CPolynomial R)`.

  Each `p : Bivariate R` is a polynomial in `Y` whose coefficients are univariate polynomials
  in `X`. The outer structure is indexed by powers of `Y`, the inner by powers of `X`.
  -/
def CPolynomial.Bivariate (R : Type*) [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]
    [BEq (CPolynomial R)] := CPolynomial (CPolynomial R)

namespace CPolynomial.Bivariate

-- TODO prove that BEq R => BEq (CPolynomial R)
variable {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R] [BEq (CPolynomial R)]

/-- Extensionality: two bivariate polynomials are equal iff their underlying values are. -/
@[ext] theorem ext {p q : Bivariate R} (h : p.val = q.val) : p = q :=
  CPolynomial.ext h

/-- Coerce to the underlying univariate polynomial (in Y) with polynomial coefficients. -/
instance : Coe (Bivariate R) (CPolynomial (CPolynomial R)) where coe := id

/-- The zero bivariate polynomial is canonical. -/
instance : Inhabited (Bivariate R) := inferInstanceAs (Inhabited (CPolynomial (CPolynomial R)))

-- ---------------------------------------------------------------------------
-- Operation stubs (for ArkLib compatibility; proofs deferred)
-- ---------------------------------------------------------------------------
-- ArkLib's Polynomial.Bivariate uses: coeff, natDegreeY, degreeX, totalDegree,
-- evalX, evalY, leadingCoeffY, swap. These will be implemented and proven
-- equivalent to Mathlib/ArkLib via ToPoly.lean.
-- ---------------------------------------------------------------------------

section Operations

-- TODO simplify these variables so only assumptions on R are needed if possible
variable (R : Type*) [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] [Semiring R]
  [BEq (CPolynomial R)] [LawfulBEq (CPolynomial R)] [DecidableEq (CPolynomial R)]

/-- Constant as a bivariate polynomial. Mathlib: `Polynomial.Bivariate.CC`. -/
def CC (r : R) : Bivariate R := CPolynomial.C (CPolynomial.C r)

/-- The variable X (inner variable). As bivariate: polynomial in Y with single coeff `X` at Y^0. -/
def C_X [Nontrivial R] : Bivariate R := CPolynomial.C CPolynomial.X

/-- The variable Y (outer variable). Monomial `Y^1` with coefficient 1. -/
def Y : Bivariate R := CPolynomial.monomial 1 (CPolynomial.C 1)

/-- Monomial `c * X^n * Y^m`. ArkLib: `Polynomial.Bivariate.monomialXY`. -/
def monomialXY (n m : ℕ) (c : R) : Bivariate R :=
  CPolynomial.monomial m (CPolynomial.monomial n c)

/-- Coefficient of `X^i Y^j` in the bivariate polynomial. Here `i` is the X-exponent (inner)
    and `j` is the Y-exponent (outer). ArkLib: `Polynomial.Bivariate.coeff f i j`. -/
def coeff (f : Bivariate R) (i j : ℕ) : R :=
  (f.val.coeff j).coeff i

/-- The Y-support: indices j such that the coefficient of Y^j is nonzero. -/
def support (f : Bivariate R) : Finset ℕ := CPolynomial.support f

/-- The `Y`-degree (degree when viewed as a polynomial in `Y`).
    ArkLib: `Polynomial.Bivariate.natDegreeY`. -/
def natDegreeY (f : Bivariate R) : ℕ :=
  f.val.natDegree

/-- The `X`-degree: maximum over all Y-coefficients of their degree in X.
    ArkLib: `Polynomial.Bivariate.degreeX`. -/
def degreeX (f : Bivariate R) : ℕ :=
  (CPolynomial.support f).sup (fun n => (f.val.coeff n).natDegree)

/-- Total degree: max over monomials of (deg_X + deg_Y).
    ArkLib: `Polynomial.Bivariate.totalDegree`. -/
def totalDegree (f : Bivariate R) : ℕ :=
  (CPolynomial.support f).sup (fun m => (f.val.coeff m).natDegree + m)

/-- Evaluate in the first variable (X) at `a`, yielding a univariate polynomial in Y.
    ArkLib: `Polynomial.Bivariate.evalX`.
    TODO: implement via mapping each Y-coefficient through `eval a`. -/
def evalX (a : R) (f : Bivariate R) : CPolynomial R := sorry

/-- Evaluate in the second variable (Y) at `a`, yielding a univariate polynomial in X.
    ArkLib: `Polynomial.Bivariate.evalY`. -/
def evalY (a : R) (f : Bivariate R) : CPolynomial R :=
  f.val.eval (CPolynomial.C a)

/-- Full evaluation at `(x, y)`: `p(x, y)`. Equivalently `(evalY y f).eval x`.
    Mathlib: `Polynomial.evalEval`. -/
def evalEval (x y : R) (f : Bivariate R) : R :=
  CPolynomial.eval x (f.val.eval (CPolynomial.C y))

/-- Leading coefficient when viewed as a polynomial in Y.
    ArkLib: `Polynomial.Bivariate.leadingCoeffY`. -/
def leadingCoeffY (f : Bivariate R) : CPolynomial R :=
  f.val.coeff (f.val.natDegree)

/-- Swap the roles of X and Y.
    ArkLib/Mathlib: `Polynomial.Bivariate.swap`. -/
def swap (f : Bivariate R) : Bivariate R := sorry

/-- Leading coefficient when viewed as a polynomial in X.
    The coefficient of X^(degreeX f): a polynomial in Y. Equivalently, `leadingCoeffY (swap f)`.
    TODO: implement as `leadingCoeffY (swap f)` once `swap` has a computable definition. -/
def leadingCoeffX (f : Bivariate R) : CPolynomial R := sorry  -- leadingCoeffY (swap f)

end Operations

end CPolynomial.Bivariate

end CompPoly
