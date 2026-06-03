/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.BatchEval.Context
import CompPoly.Univariate.Derivative
import CompPoly.Univariate.Vanishing

/-!
# Coefficient-Form Interpolation from a Vanishing Polynomial

Build the coefficient polynomial interpolating packed points from the node
vanishing polynomial `G = ∏ᵢ (X - xᵢ)` using the formula
`R = ∑ᵢ yᵢ / G'(xᵢ) * G / (X - xᵢ)`.
-/

namespace CompPoly

namespace CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Synthetic quotient by the monic linear factor `X - x`.

This is the quotient part of division by `X - x`, computed in one high-to-low
coefficient pass. When `x` is a root of `p`, it is exactly `p / (X - x)`.
-/
def divByLinearFactor (p : CPolynomial F) (x : F) : CPolynomial F :=
  let quotientSize := p.val.size - 1
  let coeffs :=
    ((List.range quotientSize).reverse.foldl
      (fun state j ↦
        let nextCoeff := p.coeff (j + 1) + x * state.1
        (nextCoeff, nextCoeff :: state.2))
      (0, ([] : List F))).2
  CPolynomial.ofArray coeffs.toArray

/-- Synthetic division by `X - x` agrees with generic monic division. -/
theorem divByLinearFactor_eq_divByMonic (p : CPolynomial F) (x : F) :
    divByLinearFactor p x = p.divByMonic (linearFactor x) := by
  sorry

/-- One coefficient-form interpolation term from a packed point and `G'(xᵢ)`. -/
def interpolationTermWithVanishing
    (G : CPolynomial F) (point : F × F) (derivativeValue : F) : CPolynomial F :=
  CPolynomial.C (point.2 / derivativeValue) *
    divByLinearFactor G point.1

/-- Coefficient-form interpolation from packed points and an already-built node
vanishing polynomial. The supplied batch evaluator is used only for the
`G'` evaluations at the interpolation nodes. -/
def interpolateCoefficientFormWithVanishing
    (E : CPolynomial.BatchEvalContext F)
    (G : CPolynomial F) (points : Array (F × F)) : CPolynomial F :=
  let derivativeValues :=
    E.evalBatchWith (CPolynomial.derivative G) (points.map fun point ↦ point.1)
  (List.range points.size).foldl
    (fun acc i ↦
      acc + interpolationTermWithVanishing G
        (points.getD i (0, 0)) (derivativeValues.getD i 0))
    0

/-- Coefficient-form interpolation from packed points using a vanishing-polynomial
context and a batch-evaluation context. -/
def interpolateCoefficientForm
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) : CPolynomial F :=
  interpolateCoefficientFormWithVanishing E
    (V.vanishingPolynomial (points.map fun point ↦ point.1)) points

end CPolynomial

end CompPoly
