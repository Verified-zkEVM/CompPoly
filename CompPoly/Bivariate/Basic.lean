/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/

import CompPoly.Univariate.Basic

/-!
# Computable Bivariate Polynomials

This file defines `CBivariate R`, the computable representation of bivariate polynomials with
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

  Each `p : CBivariate R` is a polynomial in `Y` whose coefficients are univariate polynomials
  in `X`. The outer structure is indexed by powers of `Y`, the inner by powers of `X`.
  -/
def CBivariate (R : Type*) [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R] :=
    CPolynomial (CPolynomial R)

namespace CBivariate

variable {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]

/-- Extensionality: two bivariate polynomials are equal iff their underlying values are. -/
@[ext] theorem ext {p q : CBivariate R} (h : p.val = q.val) : p = q :=
  CPolynomial.ext h

/-- Coerce to the underlying univariate polynomial (in Y) with polynomial coefficients. -/
instance : Coe (CBivariate R) (CPolynomial (CPolynomial R)) where coe := id

/-- The zero bivariate polynomial is canonical. -/
instance : Inhabited (CBivariate R) := inferInstanceAs (Inhabited (CPolynomial (CPolynomial R)))

/-- Additive structure on CBivariate R -/
instance : AddCommMonoid (CBivariate R) :=
  inferInstanceAs (AddCommMonoid (CPolynomial (CPolynomial R)))

-- ---------------------------------------------------------------------------
-- Operation stubs (for ArkLib compatibility; proofs deferred)
-- ---------------------------------------------------------------------------
-- ArkLib's Polynomial.Bivariate uses: coeff, natDegreeY, degreeX, totalDegree,
-- evalX, evalY, leadingCoeffY, swap. These will be implemented and proven
-- equivalent to Mathlib/ArkLib via ToPoly.lean.
-- ---------------------------------------------------------------------------

section Operations

variable (R : Type*) [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]

/-- Constant as a bivariate polynomial. Mathlib: `Polynomial.Bivariate.CC`. -/
def CC (r : R) : CBivariate R := CPolynomial.C (CPolynomial.C r)

/-- The variable X (inner variable). As bivariate: polynomial in Y with single coeff `X` at Y^0. -/
def X : CBivariate R := CPolynomial.C CPolynomial.X

/-- The variable Y (outer variable). Monomial `Y^1` with coefficient 1. -/
def Y [DecidableEq R] : CBivariate R := CPolynomial.monomial 1 (CPolynomial.C 1)

/-- Monomial `c * X^n * Y^m`. ArkLib: `Polynomial.Bivariate.monomialXY`. -/
def monomialXY [DecidableEq R] (n m : ℕ) (c : R) : CBivariate R :=
  CPolynomial.monomial m (CPolynomial.monomial n c)

/-- Coefficient of `X^i Y^j` in the bivariate polynomial. Here `i` is the X-exponent (inner)
    and `j` is the Y-exponent (outer). ArkLib: `Polynomial.Bivariate.coeff f i j`. -/
def coeff (f : CBivariate R) (i j : ℕ) : R :=
  (f.val.coeff j).coeff i

/-- The Y-support: indices j such that the coefficient of Y^j is nonzero. -/
def supportY (f : CBivariate R) : Finset ℕ := CPolynomial.support f

/-- The X-support: indices i such that the coefficient of X^i is nonzero
    (i.e. some monomial X^i Y^j has nonzero coefficient). -/
def supportX (f : CBivariate R) : Finset ℕ :=
  (CPolynomial.support f).biUnion (fun j => CPolynomial.support (f.val.coeff j))

/-- The `Y`-degree (degree when viewed as a polynomial in `Y`).
    ArkLib: `Polynomial.Bivariate.natDegreeY`. -/
def natDegreeY (f : CBivariate R) : ℕ :=
  f.val.natDegree

/-- The `X`-degree: maximum over all Y-coefficients of their degree in X.
    ArkLib: `Polynomial.Bivariate.degreeX`. -/
def degreeX (f : CBivariate R) : ℕ :=
  (CPolynomial.support f).sup (fun n => (f.val.coeff n).natDegree)

/-- Total degree: max over monomials of (deg_X + deg_Y).
    ArkLib: `Polynomial.Bivariate.totalDegree`. -/
def totalDegree (f : CBivariate R) : ℕ :=
  (CPolynomial.support f).sup (fun m => (f.val.coeff m).natDegree + m)

/-- Evaluate in the first variable (X) at `a`, yielding a univariate polynomial in Y.
    ArkLib: `Polynomial.Bivariate.evalX`. -/
def evalX [DecidableEq R] (a : R) (f : CBivariate R) : CPolynomial R :=
  (CPolynomial.support f).sum (fun j => CPolynomial.monomial j (CPolynomial.eval a (f.val.coeff j)))

/-- Evaluate in the second variable (Y) at `a`, yielding a univariate polynomial in X.
    ArkLib: `Polynomial.Bivariate.evalY`. -/
def evalY (a : R) (f : CBivariate R) : CPolynomial R :=
  f.val.eval (CPolynomial.C a)

/-- Full evaluation at `(x, y)`: `p(x, y)`. Inner variable X at `x`, outer variable Y at `y`.
    Equivalently `(evalY y f).eval x`. Mathlib: `Polynomial.evalEval`. -/
def evalEval (x y : R) (f : CBivariate R) : R :=
  CPolynomial.eval x (f.val.eval (CPolynomial.C y))

/-- Leading coefficient when viewed as a polynomial in Y.
    ArkLib: `Polynomial.Bivariate.leadingCoeffY`. -/
def leadingCoeffY (f : CBivariate R) : CPolynomial R :=
  f.val.coeff (f.val.natDegree)

/-- Swap the roles of X and Y.
    ArkLib/Mathlib: `Polynomial.Bivariate.swap`. -/
def swap [DecidableEq R] (f : CBivariate R) : CBivariate R :=
  (f.supportY).sum (fun j =>
    let coeffJ : CPolynomial R :=
      (CPolynomial.support (f.val.coeff j)).sum (fun i =>
        CPolynomial.monomial i ((f.val.coeff j).coeff i))
    CPolynomial.monomial j coeffJ)

/-- Leading coefficient when viewed as a polynomial in X.
    The coefficient of X^(degreeX f): a polynomial in Y. -/
def leadingCoeffX [DecidableEq R] (f : CBivariate R) : CPolynomial R :=
  (f.swap).leadingCoeffY

end Operations

end CBivariate

end CompPoly
