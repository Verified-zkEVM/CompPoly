/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Context

/-!
# Guruswami-Sudan Interpolation Basics

Dense interpolation constraints and normalized witness helpers shared by
concrete interpolation backends.
-/

namespace CompPoly

namespace GuruswamiSudan

open CBivariate

/-- Weighted-degree monomial basis used by dense interpolation. -/
def interpolationMonomials (params : GSInterpParams) : Array CBivariate.Monomial :=
  CBivariate.monomialsWeightedDegreeLE 1 (yWeight params) params.weightedDegreeBound

/-- Packed interpolation constraint `(x, y, a, b)`. -/
structure InterpolationConstraint (F : Type*) where
  x : F
  y : F
  xOrder : Nat
  yOrder : Nat
deriving Repr

/-- Hasse-derivative constraints for every point and every order `a + b < m`. -/
def interpolationConstraints {F : Type*}
    (points : Array (Prod F F)) (multiplicity : Nat) :
    Array (InterpolationConstraint F) :=
  Id.run do
    let mut constraints := #[]
    for point in points do
      for a in [0:multiplicity] do
        for b in [0:multiplicity - a] do
          constraints := constraints.push
            { x := point.1, y := point.2, xOrder := a, yOrder := b }
    pure constraints

/-- One interpolation-matrix entry contributed by one monomial and one Hasse constraint. -/
def hasseMonomialEval {F : Type*} [Semiring F]
    (monomial : CBivariate.Monomial) (constraint : InterpolationConstraint F) : F :=
  if constraint.xOrder ≤ monomial.xDegree && constraint.yOrder ≤ monomial.yDegree then
    (Nat.choose monomial.xDegree constraint.xOrder : F) *
      (Nat.choose monomial.yDegree constraint.yOrder : F) *
        constraint.x ^ (monomial.xDegree - constraint.xOrder) *
          constraint.y ^ (monomial.yDegree - constraint.yOrder)
  else
    0

/-- Dense Hasse-constraint matrix over an explicitly supplied monomial basis. -/
def interpolationConstraintMatrixOnBasis {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial) (constraints : Array (InterpolationConstraint F)) :
    DenseMatrix F :=
  DenseMatrix.ofFn constraints.size basis.size fun row col ↦
    let constraint := constraints.getD row
      { x := 0, y := 0, xOrder := 0, yOrder := 0 }
    let monomial := basis.getD col { xDegree := 0, yDegree := 0 }
    hasseMonomialEval monomial constraint

/-- Dense Hasse-constraint matrix for the interpolation problem. -/
def interpolationConstraintMatrix {F : Type*} [Semiring F]
    (params : GSInterpParams) (constraints : Array (InterpolationConstraint F)) :
    DenseMatrix F :=
  interpolationConstraintMatrixOnBasis (interpolationMonomials params) constraints

/-- Dense interpolation matrix for packed point pairs over an explicit basis. -/
def interpolationMatrixOnBasis {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial)
    (points : Array (Prod F F)) (params : GSInterpParams) : DenseMatrix F :=
  interpolationConstraintMatrixOnBasis basis
    (interpolationConstraints points params.multiplicity)

/-- Dense interpolation matrix for packed point pairs. -/
def interpolationMatrix {F : Type*} [Semiring F]
    (points : Array (Prod F F)) (params : GSInterpParams) : DenseMatrix F :=
  interpolationMatrixOnBasis (interpolationMonomials params) points params

/-- Rebuild a bivariate polynomial from a dense coefficient vector over a supplied basis. -/
def interpolationPolynomialOnBasis {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array CBivariate.Monomial) (coeffs : Array F) : CBivariate F :=
  CBivariate.ofMonomialCoeffs basis coeffs

/-- Rebuild a bivariate polynomial from its dense interpolation coefficient vector. -/
def interpolationPolynomial {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (coeffs : Array F) : CBivariate F :=
  interpolationPolynomialOnBasis (interpolationMonomials params) coeffs

/-- Coefficients of a bivariate polynomial in a supplied monomial order. -/
def interpolationCoefficientVectorOnBasis {F : Type*} [Zero F]
    (basis : Array CBivariate.Monomial) (Q : CBivariate F) : Array F :=
  basis.map fun monomial ↦
    CBivariate.coeff Q monomial.xDegree monomial.yDegree

/-- Coefficients of a bivariate polynomial in the interpolation monomial order. -/
def interpolationCoefficientVector {F : Type*} [Zero F]
    (params : GSInterpParams) (Q : CBivariate F) : Array F :=
  interpolationCoefficientVectorOnBasis (interpolationMonomials params) Q

/-- The first nonzero vector coordinate, if one exists. -/
def firstNonzeroIndex? {F : Type*} [Zero F] [BEq F] (v : Array F) : Option Nat :=
  (List.range v.size).find? fun i ↦ !(v.getD i 0 == 0)

/-- Normalize a nonzero vector by making its first nonzero coordinate equal to `1`. -/
def normalizeVector? {F : Type*} [Field F] [BEq F] (v : Array F) :
    Option (Array F) :=
  match firstNonzeroIndex? v with
  | none => none
  | some i =>
      let pivot := v.getD i 0
      if pivot == 0 then
        none
      else
        some (v.map fun c ↦ c / pivot)

/-- Predicate for the normalized interpolation-witness API. -/
def IsNormalizedInterpolationWitness {F : Type*} [Zero F] [One F] [BEq F]
    (coeffs : Array F) : Prop :=
  exists i, i < coeffs.size ∧
    coeffs.getD i 0 = 1 ∧
      ∀ j, j < i → coeffs.getD j 0 = 0

/-- Convert a homogeneous-kernel vector into a normalized basis polynomial. -/
def normalizeInterpolationPolynomialOnBasis? {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array CBivariate.Monomial) (coeffs : Array F) :
    Option (CBivariate F) :=
  match normalizeVector? coeffs with
  | none => none
  | some normalized => some (interpolationPolynomialOnBasis basis normalized)

/-- Convert a homogeneous-kernel vector into a normalized interpolation polynomial. -/
def normalizeInterpolationPolynomial? {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (coeffs : Array F) :
    Option (CBivariate F) :=
  normalizeInterpolationPolynomialOnBasis? (interpolationMonomials params) coeffs

/-- Dimension slack for a supplied interpolation basis. -/
def HasInterpolationDimensionSlackOnBasis {F : Type*}
    (basis : Array CBivariate.Monomial)
    (points : Array (Prod F F)) (params : GSInterpParams) : Prop :=
  (interpolationConstraints points params.multiplicity).size < basis.size

/-- Dimension slack condition that guarantees a nontrivial homogeneous kernel. -/
def HasInterpolationDimensionSlack {F : Type*}
    (points : Array (Prod F F)) (params : GSInterpParams) : Prop :=
  HasInterpolationDimensionSlackOnBasis (interpolationMonomials params) points params

end GuruswamiSudan

end CompPoly
