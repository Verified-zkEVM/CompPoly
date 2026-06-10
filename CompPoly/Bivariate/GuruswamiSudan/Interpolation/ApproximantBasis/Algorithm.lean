/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic

/-!
# Executable Approximant-Basis Interpolation

This backend constructs the GS diagonal modular equations, calls an explicit
solution-basis context, selects a least shifted-degree solution row, and
normalizes the resulting bivariate polynomial.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace ApproximantBasis

open PolynomialMatrix
open PolynomialMatrix.Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- Normalize a row-derived approximant candidate using the shared interpolation
vector policy. -/
def normalizeApproximantCandidate? (params : GSInterpParams) (Q : CBivariate F) :
    Option (CBivariate F) :=
  normalizeInterpolationPolynomial? params
    (interpolationCoefficientVector params Q)

/-- Positive-`Y`-weight approximant-basis interpolation branch. -/
def approximantBasisPositiveInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if distinctXCoordinatesBool points then
    let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
    let data := buildGSModularDataWithRG solver.mulContext solver.modContext R G params
    let basis := solver.solutionBasis (modularEquation data) data.shift
    match leastShiftedDegreeChoice? basis data.shift with
    | none => none
    | some choice =>
        if choice.degree ≤ params.weightedDegreeBound then
          let rawQ := CBivariate.ofCoeffRow choice.row
          normalizeApproximantCandidate? params rawQ
        else
          none
  else
    none

/-- Approximant-basis interpolation with the shared low-message branch. -/
def approximantBasisInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    approximantBasisPositiveInterpolate V E solver points params

end ApproximantBasis

end GuruswamiSudan

end CompPoly
