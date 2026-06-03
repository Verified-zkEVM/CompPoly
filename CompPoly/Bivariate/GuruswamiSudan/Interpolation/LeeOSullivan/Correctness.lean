/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Algorithm
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness

/-!
# Lee-O'Sullivan Interpolation Correctness
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- Executable distinct-`x` check agrees with the semantic predicate. -/
theorem distinctXCoordinatesBool_iff {points : Array (F × F)} :
    distinctXCoordinatesBool points = true ↔ DistinctXCoordinates points := by
  sorry

/-- The coefficient-form `R` used by Lee evaluates to the packed values at distinct nodes. -/
theorem leeCoefficientForm_eval_point
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    {points : Array (F × F)} (hdistinct : DistinctXCoordinates points)
    {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1
      (CPolynomial.interpolateCoefficientForm V E points) =
      point.2 := by
  sorry

/-- The vanishing `G` used by Lee vanishes on every listed `x`. -/
theorem leeVanishing_eval_point
    (V : CPolynomial.VanishingPolynomialContext F)
    {points : Array (F × F)} {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1 (V.vanishingPolynomial (points.map fun p ↦ p.1)) = 0 := by
  sorry

/-- Lee basis rows have exactly `ell + 1` rows. -/
theorem leeOSullivanBasisRows_size
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    (leeOSullivanBasisRows V E points params).size = leeOSullivanWidth params := by
  sorry

/-- Soundness for the executable Lee-O'Sullivan interpolation operation. -/
theorem leeOSullivanInterpolate_sound
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : leeOSullivanInterpolate V E reducer points params = some Q) :
    ValidInterpolationWitness points params Q := by
  sorry

/-- Distinct-input completeness for the executable Lee-O'Sullivan interpolation operation. -/
theorem leeOSullivanInterpolate_complete
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    {points : Array (F × F)} {params : GSInterpParams}
    (hdistinct : DistinctXCoordinates points)
    (hExists : ∃ Q, ValidInterpolationWitness points params Q) :
    ∃ Q, leeOSullivanInterpolate V E reducer points params = some Q := by
  sorry

/-- Public Lee-O'Sullivan interpolation backend context. -/
def leeOSullivanInterpContext
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F) : GSInterpContext F where
  interpolate := leeOSullivanInterpolate V E reducer
  sound := by
    intro points params Q h
    exact leeOSullivanInterpolate_sound V E reducer h
  complete := by
    intro points params hdistinct hExists
    exact leeOSullivanInterpolate_complete V E reducer hdistinct hExists

end LeeOSullivan

end GuruswamiSudan

end CompPoly
