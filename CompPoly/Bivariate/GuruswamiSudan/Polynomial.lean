/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.FactorMonic
import CompPoly.Bivariate.ToPoly
import CompPoly.Univariate.Deriv

/-!
# Guruswami-Sudan Polynomial Helpers

Reusable univariate and bivariate polynomial operations used by the
Guruswami-Sudan interpolation and root-finding kernels.
-/

namespace CompPoly

namespace CPolynomial

/-- Drop the first `n` powers of `X`, i.e. divide by `X^n` when possible and
truncate toward zero otherwise. -/
def dropXPower {R : Type*} [Zero R] (p : CPolynomial R) : Nat → CPolynomial R
  | 0 => p
  | n + 1 => dropXPower (CPolynomial.divX p) n

/-- Keep only coefficients of degree `< n`. -/
def truncate {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n : Nat) : CPolynomial R :=
  ofArray (p.val.extract 0 n)

/-- First nonzero coefficient index of a univariate polynomial, if it is
nonzero. -/
def xAdicOrder? {R : Type*} [Zero R] [BEq R] (p : CPolynomial R) : Option Nat :=
  (List.range' 0 p.val.size).find? fun i ↦ !(p.coeff i == 0)

/-- Coefficients of the inverse of a power series with known nonzero constant
coefficient, truncated to length `n`. -/
def inverseSeriesNextCoeff {F : Type*} [Field F]
    (p : CPolynomial F) (constantInv : F) (prev : Array F) (idx : Nat) : F :=
  if idx = 0 then
    constantInv
  else
    -(constantInv *
      (List.range idx).foldl
        (fun acc i ↦ acc + prev.getD i 0 * p.coeff (idx - i)) 0)

/-- Coefficients of the inverse of a power series with known nonzero constant
coefficient, truncated to length `n`. -/
def inverseSeriesCoeffs {F : Type*} [Field F]
    (p : CPolynomial F) (constantInv : F) (n : Nat) : Array F :=
  (List.range n).foldl
    (fun prev idx ↦ prev.push (inverseSeriesNextCoeff p constantInv prev idx))
    #[]

/-- Inverse of a univariate power series modulo `X^n`, if the constant term is
invertible. -/
def inverseSeries? {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) (n : Nat) : Option (CPolynomial F) :=
  if p.coeff 0 == 0 then
    none
  else
    some (ofArray (inverseSeriesCoeffs p (p.coeff 0)⁻¹ n))

/-- Coefficient of `X^n` in `p * q`, computed without materializing the
product. -/
def mulCoeff {R : Type*} [Semiring R] (p q : CPolynomial R) (n : Nat) : R :=
  (List.range (n + 1)).foldl
    (fun acc i ↦ acc + p.coeff i * q.coeff (n - i))
    0

/-- Coefficient window of `p * q`, shifted down by `low` and truncated to
`width`, computed without materializing the full product. -/
def mulWindow {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (low width : Nat) : CPolynomial R :=
  ofArray ((List.range width).map fun offset ↦ mulCoeff p q (low + offset)).toArray

/-- Coefficient window of `p * q` computed through a raw low-product context. -/
def mulWindowWithLowProduct {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R]
    (mulLow : CPolynomial.Raw.MulLowContext R)
    (p q : CPolynomial R) (low width : Nat) : CPolynomial R :=
  ofArray
    ((mulLow.mulLow (low + width) p.val q.val).extract low (low + width))

/-- Coefficient of `X^n` in `p^k`, computed by coefficient convolution without
materializing the intermediate powers. -/
def powCoeff {R : Type*} [Semiring R] (p : CPolynomial R) : Nat → Nat → R
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n =>
      (List.range (n + 1)).foldl
        (fun acc i ↦ acc + p.coeff i * powCoeff p k (n - i))
        0

/-- Coefficient of `X^n` in `a * p^k`, computed coefficient-wise. -/
def mulPowCoeff {R : Type*} [Semiring R]
    (a p : CPolynomial R) (k n : Nat) : R :=
  (List.range (n + 1)).foldl
    (fun acc i ↦ acc + a.coeff i * powCoeff p k (n - i))
    0

end CPolynomial

namespace CBivariate

/-- A bivariate monomial exponent pair. -/
structure Monomial where
  xDegree : Nat
  yDegree : Nat
deriving BEq, DecidableEq, Repr

/-- One monomial contribution to a Hasse derivative. -/
structure HasseTerm (R : Type*) where
  xDegree : Nat
  yDegree : Nat
  coeff : R

/-- Construct a bivariate polynomial from a coefficient grid indexed by `grid[y][x]`. -/
def ofCoeffGrid {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (grid : Array (Array R)) : CBivariate R :=
  Id.run do
    let mut out : CBivariate R := 0
    for y in [0:grid.size] do
      let row := grid.getD y #[]
      for x in [0:row.size] do
        out := out + monomialXY x y (row.getD x 0)
    pure out

/-- Construct a bivariate polynomial from a monomial list and parallel coefficient vector. -/
def ofMonomialCoeffs {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (monomials : Array Monomial) (coeffs : Array R) : CBivariate R :=
  (List.range' 0 monomials.size).foldl
    (fun out col ↦
      let monomial := monomials.getD col ⟨0, 0⟩
      out + monomialXY monomial.xDegree monomial.yDegree (coeffs.getD col 0))
    0

/-- Candidate monomials in the finite square used by weighted-degree enumeration. -/
def monomialGrid (bound : Nat) : List Monomial :=
  (List.range (bound + 1)).flatMap fun y ↦
    (List.range (bound + 1)).map fun x ↦ ({ xDegree := x, yDegree := y } : Monomial)

/-- Enumerate monomials inside a finite weighted-degree search rectangle.

When both weights are positive this is the complete set of monomials with
weighted degree at most `bound`. If a weight is zero, `bound` also serves as the
finite exponent cap for that variable.
-/
def monomialsWeightedDegreeLE (xWeight yWeight bound : Nat) : Array Monomial :=
  ((monomialGrid bound).filter fun m ↦
    xWeight * m.xDegree + yWeight * m.yDegree ≤ bound).toArray

/-- Shared monomial contributions for materialized and directly evaluated Hasse derivatives. -/
def hasseDerivativeTermList {R : Type*} [Semiring R]
    (a b : Nat) (Q : CBivariate R) : List (HasseTerm R) :=
  (List.range' 0 Q.val.size).foldl
    (fun out y ↦
      let coeffY := Q.val.coeff y
      if b ≤ y then
        (List.range' 0 coeffY.val.size).foldl
          (fun out x ↦
            if a ≤ x then
              let coeff := (Nat.choose x a : R) * (Nat.choose y b : R) * coeffY.coeff x
              out ++ [⟨x - a, y - b, coeff⟩]
            else out)
          out
      else out)
    []

/-- Shared monomial contributions for materialized and directly evaluated Hasse derivatives. -/
def hasseDerivativeTerms {R : Type*} [Semiring R]
    (a b : Nat) (Q : CBivariate R) : Array (HasseTerm R) :=
  (hasseDerivativeTermList a b Q).toArray

/-- Materialize a Hasse derivative from a list of derivative terms. -/
def hasseDerivativeFromTerms {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (terms : List (HasseTerm R)) : CBivariate R :=
  terms.foldl (fun out term ↦
    out + monomialXY term.xDegree term.yDegree term.coeff) 0

/-- Executable Hasse derivative of a bivariate polynomial. -/
def hasseDerivative {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : Nat) (Q : CBivariate R) : CBivariate R :=
  hasseDerivativeFromTerms (hasseDerivativeTermList a b Q)

/-- Evaluate derivative terms directly at one point. -/
def hasseDerivativeEvalFromTerms {R : Type*} [Semiring R]
    (terms : List (HasseTerm R)) (x y : R) : R :=
  terms.foldl (fun acc term ↦
    acc + term.coeff * x ^ term.xDegree * y ^ term.yDegree) 0

/-- Evaluate a Hasse derivative at one point without materializing the derivative. -/
def hasseDerivativeEval {R : Type*} [Semiring R]
    (a b : Nat) (x y : R) (Q : CBivariate R) : R :=
  hasseDerivativeEvalFromTerms (hasseDerivativeTermList a b Q) x y

/-- Candidate derivative orders in the finite square used by multiplicity checks. -/
def derivativeOrderGrid (multiplicity : Nat) : List (Nat × Nat) :=
  (List.range multiplicity).flatMap fun a ↦
    (List.range multiplicity).map fun b ↦ (a, b)

/-- Derivative orders `(a, b)` with `a + b < multiplicity`. -/
def derivativeOrders (multiplicity : Nat) : Array (Nat × Nat) :=
  ((derivativeOrderGrid multiplicity).filter fun order ↦
    order.1 + order.2 < multiplicity).toArray

/-- Mathematical multiplicity constraint used by the GS interpolation specification. -/
def HasMultiplicityAtLeast {R : Type*} [Semiring R]
    (Q : CBivariate R) (x y : R) (multiplicity : Nat) : Prop :=
  ∀ a b, a + b < multiplicity → hasseDerivativeEval a b x y Q = 0

/-- Executable multiplicity check at one point. -/
def multiplicityAtLeastBool {R : Type*} [Semiring R] [BEq R]
    (Q : CBivariate R) (x y : R) (multiplicity : Nat) : Bool :=
  (derivativeOrders multiplicity).all fun order ↦
    hasseDerivativeEval order.1 order.2 x y Q == 0

/-- Mathematical batch multiplicity constraints over packed point pairs. -/
def SatisfiesMultiplicityConstraints {R : Type*} [Semiring R]
    (Q : CBivariate R) (points : Array (R × R)) (multiplicity : Nat) : Prop :=
  ∀ point, point ∈ points.toList →
    HasMultiplicityAtLeast Q point.1 point.2 multiplicity

/-- Executable batch multiplicity check over packed point pairs. -/
def satisfiesMultiplicityConstraintsBool {R : Type*} [Semiring R] [BEq R]
    (Q : CBivariate R) (points : Array (R × R)) (multiplicity : Nat) : Bool :=
  points.all fun point ↦
    multiplicityAtLeastBool Q point.1 point.2 multiplicity

/-- Compose a bivariate polynomial with a univariate polynomial in the `Y` slot:
`Q(X, p(X))`. -/
def composeY {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (p : CPolynomial R) : CPolynomial R :=
  CPolynomial.eval p Q

/-- Horner implementation of `Q(X, p(X))` in the outer `Y` variable. -/
@[inline, specialize]
def composeYHorner {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (p : CPolynomial R) : CPolynomial R :=
  CPolynomial.evalHorner p Q

/-- Truncated Horner implementation of `Q(X, p(X))` in the outer `Y`
variable.

After each Horner step, the accumulator is truncated modulo `X^n`, so callers
that only need an `X`-adic certificate do not materialize coefficients that
will be discarded immediately. -/
@[inline, specialize]
def composeYHornerTruncated {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (p : CPolynomial R) (n : Nat) : CPolynomial R :=
  (List.range Q.val.size).reverse.foldl
    (fun acc y ↦ CPolynomial.truncate (acc * p + Q.val.coeff y) n)
    (0 : CPolynomial R)

/-- Coefficient of `X^depth` in `Q(X, p(X))`, computed without materializing
the whole composed polynomial. -/
def composeYCoeff {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (p : CPolynomial R) (depth : Nat) : R :=
  (List.range' 0 Q.val.size).foldl
    (fun acc y ↦ acc + CPolynomial.mulPowCoeff (Q.val.coeff y) p y depth)
    0

/-- Formal derivative in the outer `Y` variable. -/
def yDerivative {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) : CBivariate R :=
  (List.range' 1 Q.val.size).foldl
    (fun out y ↦
      let coeffY := Q.val.coeff y
      (List.range' 0 coeffY.val.size).foldl
        (fun out x ↦ out + monomialXY x (y - 1) ((y : R) * coeffY.coeff x))
        out)
    0

/-- Minimum `X`-adic order across all nonzero `Y`-coefficients of a bivariate
polynomial. -/
def xAdicOrder? {R : Type*} [Zero R] [BEq R] (Q : CBivariate R) : Option Nat :=
  (List.range' 0 Q.val.size).foldl
    (fun best y ↦
      match CPolynomial.xAdicOrder? (Q.val.coeff y) with
      | none => best
      | some order =>
          match best with
          | none => some order
          | some current => some (min current order))
    none

/-- Divide every `Y`-coefficient by `X^n`, truncating coefficients with lower
`X`-degree to zero. -/
def divXPower {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (n : Nat) : CBivariate R :=
  CPolynomial.ofArray (Q.val.map fun coeff ↦ CPolynomial.dropXPower coeff n)

/-- Keep only coefficients of `X`-degree `< n` in every `Y`-coefficient. -/
def truncateX {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) (n : Nat) : CBivariate R :=
  CPolynomial.ofArray (Q.val.map fun coeff ↦ CPolynomial.truncate coeff n)

/-- Strip the common `X`-adic factor from a bivariate polynomial. -/
def stripXAdicFactor {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (Q : CBivariate R) : CBivariate R :=
  match xAdicOrder? Q with
  | none => default
  | some order => divXPower Q order

/-- View a univariate polynomial in `X` as a bivariate polynomial constant in
`Y`. -/
def ofYConstant {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CBivariate R :=
  CPolynomial.C p

/-- View a univariate polynomial in `X` as the coefficient of `Y^y` in a
bivariate polynomial. -/
def ofYCoefficient {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (y : Nat) (p : CPolynomial R) : CBivariate R :=
  CPolynomial.monomial y p

end CBivariate

end CompPoly
