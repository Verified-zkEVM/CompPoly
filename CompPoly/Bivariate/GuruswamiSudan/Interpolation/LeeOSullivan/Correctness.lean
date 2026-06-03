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

omit [Field F] [Nontrivial F] [DecidableEq F] in
/-- Executable distinct-`x` check agrees with the semantic predicate. -/
theorem distinctXCoordinatesBool_iff {points : Array (F × F)} :
    distinctXCoordinatesBool points = true ↔ DistinctXCoordinates points := by
  unfold distinctXCoordinatesBool DistinctXCoordinates
  generalize points.toList = xs
  induction xs with
  | nil =>
      simp [distinctXCoordinatesListBool]
  | cons point rest ih =>
      simp [distinctXCoordinatesListBool, ih]
      intro _
      constructor
      · intro h x hx
        exact h point.1 x hx rfl
      · intro h a b hab ha
        subst a
        exact h b hab

omit [Nontrivial F] in
/-- The coefficient-form `R` used by Lee evaluates to the packed values at distinct nodes. -/
theorem leeCoefficientForm_eval_point
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    {points : Array (F × F)} (hdistinct : DistinctXCoordinates points)
    {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1
      (CPolynomial.interpolateCoefficientForm V E points) =
      point.2 := by
  exact CPolynomial.interpolateCoefficientForm_eval_point V E hdistinct hpoint

omit [Nontrivial F] [DecidableEq F] in
/-- The vanishing `G` used by Lee vanishes on every listed `x`. -/
theorem leeVanishing_eval_point
    (V : CPolynomial.VanishingPolynomialContext F)
    {points : Array (F × F)} {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1 (V.vanishingPolynomial (points.map fun p ↦ p.1)) = 0 := by
  rw [V.correct]
  apply CPolynomial.eval_vanishingPolynomialArray_eq_zero_of_mem
  simp
  have hmem : (point.1, point.2) ∈ points := by
    simpa only [Array.mem_def] using hpoint
  apply Exists.intro point.2
  assumption

/-- Lee basis rows have exactly `ell + 1` rows. -/
theorem leeOSullivanBasisRows_size
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    (leeOSullivanBasisRows V E points params).size = leeOSullivanWidth params := by
  simp [leeOSullivanBasisRows, leeOSullivanBasisRowsWithRG, leeOSullivanWidth]

/-- Lee basis rows built from fixed `R` and `G` are rectangular. -/
theorem leeOSullivanBasisRowsWithRG_wellFormed
    (R G : CPolynomial F) (params : GSInterpParams) :
    WellFormed (leeOSullivanBasisRowsWithRG R G params) := by
  intro row hrow
  simp [leeOSullivanBasisRowsWithRG, MatrixRows] at hrow
  rcases hrow with ⟨i, hi, rfl⟩
  have hwidth :
      MatrixWidth (leeOSullivanBasisRowsWithRG R G params) =
        leeOSullivanWidth params := by
    simp [leeOSullivanBasisRowsWithRG, MatrixWidth, leeOSullivanWidth,
      CBivariate.toCoeffRow]
  rw [hwidth]
  exact CBivariate.toCoeffRow_size (leeOSullivanWidth params)
    (leeOSullivanBasisPolynomial R G params i)

/-- Lee basis rows built from packed points are rectangular. -/
theorem leeOSullivanBasisRows_wellFormed
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    WellFormed (leeOSullivanBasisRows V E points params) := by
  simp [leeOSullivanBasisRows]
  exact leeOSullivanBasisRowsWithRG_wellFormed _ _ params

/-- Soundness for the executable Lee-O'Sullivan interpolation operation. -/
theorem leeOSullivanInterpolate_sound
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : leeOSullivanInterpolate V E reducer points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold leeOSullivanInterpolate at h
  by_cases hLow : params.messageDegree ≤ 1
  · simp [hLow] at h
    rw [← h]
    exact lowMessageDegreeInterpolation_sound (points := points) (params := params) hLow
  · simp [hLow, leeOSullivanPositiveInterpolate] at h
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
  unfold leeOSullivanInterpolate
  by_cases hLow : params.messageDegree ≤ 1
  · refine ⟨lowMessageDegreeInterpolation points params.multiplicity, ?_⟩
    simp [hLow]
  · simp [hLow]
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
