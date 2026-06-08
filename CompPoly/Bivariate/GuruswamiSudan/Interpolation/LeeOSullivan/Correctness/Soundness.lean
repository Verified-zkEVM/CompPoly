/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Normalization
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Rows
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Selection
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness

/-!
# Lee-O'Sullivan Interpolation Soundness

Soundness for the executable Lee-O'Sullivan interpolation operation.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

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
    let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
    let basis := leeOSullivanBasisRowsWithRG R G params
    let shift := leeOSullivanShifts params
    let reduced := reducer.reduce basis shift
    change distinctXCoordinatesBool points = true ∧
        (match leastShiftedDegreeRow? reduced shift with
        | none => none
        | some row =>
            match rowShiftedDegree? row shift with
            | none => none
            | some degree =>
                if degree ≤ params.weightedDegreeBound then
                  match normalizeLeeCandidate? params (CBivariate.ofCoeffRow row) with
                  | none => none
                  | some Q => some Q
                else none) = some Q at h
    rcases h with ⟨hdistinctBool, hsome⟩
    have hdistinct : DistinctXCoordinates points :=
      distinctXCoordinatesBool_iff.mp hdistinctBool
    have hRPoints :
        ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2 := by
      intro point hpoint
      have hpointEval := leeCoefficientForm_eval_point V E hdistinct hpoint
      simpa [R, G, CPolynomial.interpolateCoefficientForm] using hpointEval
    have hGPoints :
        ∀ point, point ∈ points.toList → CPolynomial.eval point.1 G = 0 := by
      intro point hpoint
      simpa [G] using leeVanishing_eval_point V hpoint
    have hbasisWF : WellFormed basis := by
      simpa [basis] using leeOSullivanBasisRowsWithRG_wellFormed R G params
    cases hrowSel : leastShiftedDegreeRow? reduced shift with
    | none =>
        simp [hrowSel] at hsome
    | some row =>
        cases hrowDeg : rowShiftedDegree? row shift with
        | none =>
            simp [hrowSel, hrowDeg] at hsome
        | some degree =>
            by_cases hdegreeLe : degree ≤ params.weightedDegreeBound
            · simp [hrowSel, hrowDeg, hdegreeLe] at hsome
              cases hnorm :
                  normalizeLeeCandidate? params (CBivariate.ofCoeffRow row) with
              | none =>
                  simp [hnorm] at hsome
              | some Qnorm =>
                  simp [hnorm] at hsome
                  cases hsome
                  rcases leastShiftedDegreeRow?_some_valid hrowSel with
                    ⟨choice, _hchoice, hchoiceValid, hchoiceRow⟩
                  rcases hchoiceValid with
                    ⟨hchoiceIdx, hchoiceEq, _hchoiceDegree⟩
                  have hrowEq : row = reduced.getD choice.index #[] := by
                    rw [← hchoiceRow]
                    exact hchoiceEq
                  rcases ofCoeffRow_matrix_getD_semantic_rowSpan reduced hchoiceIdx with
                    ⟨spanRow, hspanReduced, hspanPolyGet⟩
                  have hspanPoly :
                      CBivariate.ofCoeffRow spanRow =
                        CBivariate.ofCoeffRow row := by
                    rw [hspanPolyGet, ← hrowEq]
                  have hspanBasis : spanRow ∈ RowSpan basis := by
                    have hspanEq := reducer.rowSpan_eq basis shift hbasisWF
                    rw [← hspanEq]
                    exact hspanReduced
                  have hbasisSat :
                      ∀ idx,
                        idx <
                          (leeOSullivanBasisPolynomials (F := F) R G params).size →
                          CBivariate.SatisfiesMultiplicityConstraints
                            ((leeOSullivanBasisPolynomials (F := F) R G params).getD idx 0)
                            points params.multiplicity :=
                    leeOSullivanBasisPolynomials_satisfiesMultiplicityConstraints
                      R G params hRPoints hGPoints
                  have hmultSpan :
                      CBivariate.SatisfiesMultiplicityConstraints
                        (CBivariate.ofCoeffRow spanRow) points params.multiplicity :=
                    ofCoeffRow_rowSpan_lee_satisfiesMultiplicityConstraints
                      R G params hbasisSat hspanBasis
                  have hmultRaw :
                      CBivariate.SatisfiesMultiplicityConstraints
                        (CBivariate.ofCoeffRow row) points params.multiplicity := by
                    rw [← hspanPoly]
                    exact hmultSpan
                  have hYBound :
                      ∀ i j, leeOSullivanWidth params ≤ j →
                        CBivariate.coeff (CBivariate.ofCoeffRow row) i j = 0 := by
                    intro i j hj
                    rw [← hspanPoly]
                    exact ofCoeffRow_rowSpan_lee_coeff_eq_zero_of_width_le
                      R G params hspanBasis hj
                  have hdegRaw :
                      CBivariate.natWeightedDegree (CBivariate.ofCoeffRow row)
                        1 (yWeight params) ≤ params.weightedDegreeBound :=
                    natWeightedDegree_ofCoeffRow_le_of_lee_rowShiftedDegree?_le
                      params row (by simpa [shift] using hrowDeg) hdegreeLe hYBound
                  exact normalizeLeeCandidate?_sound_of_raw
                    (points := points) (params := params) hLow hdegRaw hmultRaw hnorm
            · simp [hrowSel, hrowDeg, hdegreeLe] at hsome

end LeeOSullivan

end GuruswamiSudan

end CompPoly
