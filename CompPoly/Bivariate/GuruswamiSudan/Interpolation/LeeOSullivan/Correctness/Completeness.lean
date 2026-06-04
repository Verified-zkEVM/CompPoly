/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Divisibility
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Soundness

/-!
# Lee-O'Sullivan Interpolation Completeness

Completeness theorems and public context wrapper for Lee-O'Sullivan interpolation.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

theorem leeOSullivanPositiveInterpolate_complete_of_row
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    {points : Array (F × F)} {params : GSInterpParams}
    (hdistinct : DistinctXCoordinates points)
    (hHigh : ¬ params.messageDegree ≤ 1)
    {row : PolynomialRow F} {rowDegree : Nat}
    (hrowSpan :
      row ∈ RowSpan
        (leeOSullivanBasisRowsWithRG
          (CPolynomial.interpolateCoefficientFormWithVanishing E
            (V.vanishingPolynomial (points.map fun point ↦ point.1)) points)
          (V.vanishingPolynomial (points.map fun point ↦ point.1)) params))
    (hrowDegree :
      rowShiftedDegree? row (leeOSullivanShifts params) = some rowDegree)
    (hrowBound : rowDegree ≤ params.weightedDegreeBound) :
    ∃ Q, leeOSullivanPositiveInterpolate V E reducer points params = some Q := by
  unfold leeOSullivanPositiveInterpolate
  have hdistinctBool : distinctXCoordinatesBool points = true :=
    distinctXCoordinatesBool_iff.mpr hdistinct
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
  let basis := leeOSullivanBasisRowsWithRG R G params
  let shift := leeOSullivanShifts params
  let reduced := reducer.reduce basis shift
  have hbasisWF : WellFormed basis := by
    simpa [basis, R, G] using leeOSullivanBasisRowsWithRG_wellFormed R G params
  have hshiftSize : shift.size = MatrixWidth basis := by
    simp [shift, basis, leeOSullivanShifts, CBivariate.weightedDegreeShift,
      leeOSullivanBasisRowsWithRG_width]
  have hrowSpan' : row ∈ RowSpan basis := by
    simpa [basis, R, G] using hrowSpan
  have hrowDegree' : rowShiftedDegree? row shift = some rowDegree := by
    simpa [shift] using hrowDegree
  rcases reducer.least_row_minimal basis shift row hbasisWF hshiftSize hrowSpan'
      (by rw [hrowDegree']; simp) with
    ⟨outRow, outDegree, inputDegree, houtMem, houtDegree, hinputDegree, houtLe⟩
  have hinputEq : inputDegree = rowDegree := by
    rw [hrowDegree'] at hinputDegree
    exact (Option.some.inj hinputDegree).symm
  have houtBound : outDegree ≤ params.weightedDegreeBound := by
    omega
  rcases List.getElem_of_mem houtMem with ⟨outIndex, houtIndexList, houtGet⟩
  have houtIndex : outIndex < reduced.size := by
    simpa [MatrixRows] using houtIndexList
  have houtGetD : reduced.getD outIndex #[] = outRow := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem houtIndex]
    simpa [MatrixRows, Array.getElem_toList] using houtGet
  rcases leastShiftedDegreeChoice?_some_of_degree
      (M := reduced) (shift := shift) (i := outIndex) (d := outDegree)
      houtIndex (by simpa [houtGetD] using houtDegree) with
    ⟨choice, hchoice, hchoiceLe⟩
  have hrowSel : leastShiftedDegreeRow? reduced shift = some choice.row := by
    unfold leastShiftedDegreeRow?
    rw [hchoice]
    rfl
  have hchoiceValid := leastShiftedDegreeChoice?_some_valid hchoice
  have hchoiceDegree : rowShiftedDegree? choice.row shift = some choice.degree :=
    hchoiceValid.2.2
  have hchoiceBound : choice.degree ≤ params.weightedDegreeBound := by
    omega
  have hrawNe : CBivariate.ofCoeffRow choice.row ≠ 0 :=
    ofCoeffRow_ne_zero_of_rowShiftedDegree?_some hchoiceDegree
  have hYBound :
      ∀ i j, leeOSullivanWidth params ≤ j →
        CBivariate.coeff (CBivariate.ofCoeffRow choice.row) i j = 0 := by
    intro i j hj
    rcases ofCoeffRow_matrix_getD_semantic_rowSpan reduced hchoiceValid.1 with
      ⟨spanRow, hspanReduced, hspanPolyGet⟩
    have hrowEq : choice.row = reduced.getD choice.index #[] := hchoiceValid.2.1
    have hspanPoly :
        CBivariate.ofCoeffRow spanRow =
          CBivariate.ofCoeffRow choice.row := by
      rw [hspanPolyGet, ← hrowEq]
    have hspanBasis : spanRow ∈ RowSpan basis := by
      have hspanEq := reducer.rowSpan_eq basis shift hbasisWF
      rw [← hspanEq]
      exact hspanReduced
    rw [← hspanPoly]
    exact ofCoeffRow_rowSpan_lee_coeff_eq_zero_of_width_le
      R G params hspanBasis hj
  have hdegRaw :
      CBivariate.natWeightedDegree (CBivariate.ofCoeffRow choice.row)
        1 (yWeight params) ≤ params.weightedDegreeBound :=
    natWeightedDegree_ofCoeffRow_le_of_lee_rowShiftedDegree?_le
      params choice.row (by simpa [shift] using hchoiceDegree) hchoiceBound hYBound
  rcases normalizeLeeCandidate?_some_of_raw hHigh hrawNe hdegRaw with
    ⟨Q, hnorm⟩
  refine ⟨Q, ?_⟩
  simp [hdistinctBool, G, R, basis, shift, reduced, hrowSel, hchoiceDegree,
    hchoiceBound, hnorm]

theorem leeOSullivanPositiveInterpolate_complete_of_span
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hdistinct : DistinctXCoordinates points)
    (hHigh : ¬ params.messageDegree ≤ 1)
    (hQ : ValidInterpolationWitness points params Q)
    (hspan :
      koetterBasisSpanContains
        (leeOSullivanBasisPolynomials (F := F)
          (CPolynomial.interpolateCoefficientFormWithVanishing E
            (V.vanishingPolynomial (points.map fun point ↦ point.1)) points)
          (V.vanishingPolynomial (points.map fun point ↦ point.1)) params) Q) :
    ∃ Q, leeOSullivanPositiveInterpolate V E reducer points params = some Q := by
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
  rcases ofCoeffRow_lee_rowSpan_of_spanContains R G params
      (by simpa [R, G] using hspan) with
    ⟨row, hrowSpan, hrowPoly⟩
  cases hrowDegree : rowShiftedDegree? row (leeOSullivanShifts params) with
  | none =>
      have hzero := ofCoeffRow_eq_zero_of_rowShiftedDegree?_none hrowDegree
      exact False.elim (hQ.1 (by simpa [← hrowPoly] using hzero))
  | some rowDegree =>
      have hrowSize := rowSpan_lee_row_size R G params hrowSpan
      have hshift :
          leeOSullivanShifts params =
            CBivariate.weightedDegreeShift (yWeight params) row.size := by
        simp [leeOSullivanShifts, hrowSize]
      have hdegreeEq :
          CBivariate.natWeightedDegree (CBivariate.ofCoeffRow row) 1
              (yWeight params) =
            rowDegree :=
        CBivariate.rowShiftedDegree?_eq_natWeightedDegree_ofCoeffRow
          row (yWeight params) rowDegree (by simpa [← hshift] using hrowDegree)
      have hrowBound : rowDegree ≤ params.weightedDegreeBound := by
        have hrawBound :
            CBivariate.natWeightedDegree (CBivariate.ofCoeffRow row) 1
                (yWeight params) ≤
              params.weightedDegreeBound := by
          simpa [hrowPoly] using hQ.2.1
        rwa [hdegreeEq] at hrawBound
      exact leeOSullivanPositiveInterpolate_complete_of_row
        V E reducer hdistinct hHigh hrowSpan hrowDegree hrowBound


omit [DecidableEq F] in
private theorem coeffY_sub (P Q : CBivariate F) (j : Nat) :
    CPolynomial.coeff (P - Q) j = CPolynomial.coeff P j - CPolynomial.coeff Q j := by
  exact CPolynomial.coeff_sub (p := (P : CPolynomial (CPolynomial F)))
    (q := (Q : CPolynomial (CPolynomial F))) (i := j)

private theorem leeOSullivanTopCancellation
    (V : CPolynomial.VanishingPolynomialContext F) (R : CPolynomial F)
    {points : Array (F × F)} (params : GSInterpParams)
    (hdistinct : DistinctXCoordinates points)
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2)
    {P : CBivariate F} {idx : Nat}
    (hidx : idx < leeOSullivanWidth params)
    (hY : ∀ j, idx < j → P.val.coeff j = 0)
    (hmult : CBivariate.SatisfiesMultiplicityConstraints P points params.multiplicity) :
    ∃ weight : CPolynomial F,
      let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
      let basis := leeOSullivanBasisPolynomials (F := F) R G params
      let term := CBivariate.ofYConstant weight * basis.getD idx 0
      CPolynomial.coeff (P - term) idx = 0 ∧
        (∀ j, idx < j → CPolynomial.coeff (P - term) j = 0) ∧
        CBivariate.SatisfiesMultiplicityConstraints (P - term) points params.multiplicity ∧
        koetterBasisSpanContains basis term := by
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let basis := leeOSullivanBasisPolynomials (F := F) R G params
  have hidxBasis : idx < basis.size := by
    simpa [basis, leeOSullivanBasisPolynomials_size] using hidx
  have hget : basis.getD idx 0 = leeOSullivanBasisPolynomial R G params idx := by
    simpa [basis] using leeOSullivanBasisPolynomials_getD_of_lt R G params hidx
  have hGPoints : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 G = 0 := by
    intro point hpoint
    simpa [G] using leeVanishing_eval_point V hpoint
  have hbasisSat :
      ∀ i, i < basis.size →
        CBivariate.SatisfiesMultiplicityConstraints
          (basis.getD i 0) points params.multiplicity := by
    intro i hi
    simpa [basis] using
      leeOSullivanBasisPolynomials_satisfiesMultiplicityConstraints R G params
        hR hGPoints i hi
  by_cases hlt : idx < params.multiplicity
  · rcases coeffY_dvd_vanishingPolynomial_pow_of_multiplicity
        V hdistinct hlt hY hmult with
      ⟨weight, hcoeffWeight⟩
    refine ⟨weight, ?_⟩
    let term := CBivariate.ofYConstant weight * basis.getD idx 0
    have hcoeffTermSelf : CPolynomial.coeff term idx = P.val.coeff idx := by
      dsimp [term]
      rw [coeff_ofYConstant_mul_outer, hget, leeOSullivanBasisPolynomial_coeffY_self]
      have ht : leeOSullivanT params idx = idx := by
        simp [leeOSullivanT, Nat.min_eq_left (Nat.le_of_lt hlt)]
      rw [ht]
      exact hcoeffWeight.symm
    have hcoeffIdx : CPolynomial.coeff (P - term) idx = 0 := by
      rw [coeffY_sub, hcoeffTermSelf]
      simp
    have hhigher : ∀ j, idx < j → CPolynomial.coeff (P - term) j = 0 := by
      intro j hj
      have htermj : CPolynomial.coeff term j = 0 := by
        dsimp [term]
        rw [coeff_ofYConstant_mul_outer, hget,
          leeOSullivanBasisPolynomial_coeffY_eq_zero_of_idx_lt R G params hj]
        simp
      have hPj : CPolynomial.coeff P j = 0 := by
        simpa using hY j hj
      rw [coeffY_sub, hPj, htermj]
      simp
    have htermMult :
        CBivariate.SatisfiesMultiplicityConstraints term points params.multiplicity := by
      intro point hpoint
      dsimp [term]
      exact hasMultiplicityAtLeast_ofYConstant_mul weight
        ((hbasisSat idx hidxBasis) point hpoint)
    have htermSpan : koetterBasisSpanContains basis term := by
      dsimp [term]
      exact koetterBasisSpanContains_single basis hidxBasis weight
    exact ⟨hcoeffIdx, hhigher,
      satisfiesMultiplicityConstraints_sub hmult htermMult, htermSpan⟩
  · let weight : CPolynomial F := P.val.coeff idx
    refine ⟨weight, ?_⟩
    let term := CBivariate.ofYConstant weight * basis.getD idx 0
    have hcoeffTermSelf : CPolynomial.coeff term idx = P.val.coeff idx := by
      dsimp [term, weight]
      rw [coeff_ofYConstant_mul_outer, hget, leeOSullivanBasisPolynomial_coeffY_self]
      have ht : leeOSullivanT params idx = params.multiplicity := by
        simp [leeOSullivanT, Nat.min_eq_right (Nat.le_of_not_gt hlt)]
      rw [ht]
      simp
    have hcoeffIdx : CPolynomial.coeff (P - term) idx = 0 := by
      rw [coeffY_sub, hcoeffTermSelf]
      simp
    have hhigher : ∀ j, idx < j → CPolynomial.coeff (P - term) j = 0 := by
      intro j hj
      have htermj : CPolynomial.coeff term j = 0 := by
        dsimp [term]
        rw [coeff_ofYConstant_mul_outer, hget,
          leeOSullivanBasisPolynomial_coeffY_eq_zero_of_idx_lt R G params hj]
        simp
      have hPj : CPolynomial.coeff P j = 0 := by
        simpa using hY j hj
      rw [coeffY_sub, hPj, htermj]
      simp
    have htermMult :
        CBivariate.SatisfiesMultiplicityConstraints term points params.multiplicity := by
      intro point hpoint
      dsimp [term]
      exact hasMultiplicityAtLeast_ofYConstant_mul weight
        ((hbasisSat idx hidxBasis) point hpoint)
    have htermSpan : koetterBasisSpanContains basis term := by
      dsimp [term]
      exact koetterBasisSpanContains_single basis hidxBasis weight
    exact ⟨hcoeffIdx, hhigher,
      satisfiesMultiplicityConstraints_sub hmult htermMult, htermSpan⟩

private theorem koetterBasisSpanContains_zero (basis : Array (CBivariate F)) :
    koetterBasisSpanContains basis 0 := by
  refine ⟨fun _ ↦ 0, ?_⟩
  exact koetterBasisCombination_eq_zero_of_weights_zero (fun _ ↦ 0) basis
    (by intro idx hidx; rfl)

omit [DecidableEq F] in
private theorem cbivariate_eq_zero_of_coeffY_zero (P : CBivariate F)
    (h : ∀ j, CPolynomial.coeff P j = 0) : P = 0 := by
  apply (CPolynomial.eq_iff_coeff
    (p := (P : CPolynomial (CPolynomial F)))
    (q := (0 : CPolynomial (CPolynomial F)))).2
  intro j
  rw [h j, CPolynomial.coeff_zero]

private theorem leeOSullivanBasisSpanContains_of_multiplicity_yDegree_le
    (V : CPolynomial.VanishingPolynomialContext F) (R : CPolynomial F)
    {points : Array (F × F)} (params : GSInterpParams)
    (hdistinct : DistinctXCoordinates points)
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2)
    {P : CBivariate F} {n : Nat}
    (hn : n < leeOSullivanWidth params)
    (hY : ∀ j, n < j → CPolynomial.coeff P j = 0)
    (hmult : CBivariate.SatisfiesMultiplicityConstraints P points params.multiplicity) :
    koetterBasisSpanContains
      (leeOSullivanBasisPolynomials (F := F) R
        (V.vanishingPolynomial (points.map fun point ↦ point.1)) params) P := by
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let basis := leeOSullivanBasisPolynomials (F := F) R G params
  change koetterBasisSpanContains basis P
  induction n generalizing P with
  | zero =>
      have hTopY : ∀ j, 0 < j → P.val.coeff j = 0 := by
        intro j hj
        simpa using hY j hj
      rcases leeOSullivanTopCancellation V R params hdistinct hR hn hTopY hmult with
        ⟨weight, hcoeffIdx, hhigher, _hresMult, htermSpan⟩
      let term := CBivariate.ofYConstant weight *
        (leeOSullivanBasisPolynomials (F := F) R
          (V.vanishingPolynomial (points.map fun point ↦ point.1)) params).getD 0 0
      have hresZero : P - term = 0 := by
        apply cbivariate_eq_zero_of_coeffY_zero
        intro j
        cases j with
        | zero =>
            exact hcoeffIdx
        | succ j =>
            exact hhigher (j + 1) (by omega)
      have hresSpan : koetterBasisSpanContains basis (P - term) := by
        rw [hresZero]
        exact koetterBasisSpanContains_zero basis
      have hsum := koetterBasisSpanContains_add hresSpan htermSpan
      have htermRepr :
          CBivariate.ofYConstant weight *
            (leeOSullivanBasisPolynomials (F := F) R
              (V.vanishingPolynomial (points.map fun point ↦ point.1)) params).getD 0 0 = term := by
        rfl
      have hsum' := hsum
      rw [htermRepr] at hsum'
      simpa [term, basis, G, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum'
  | succ n ih =>
      let idx := n + 1
      have hidxWidth : idx < leeOSullivanWidth params := by
        simpa [idx] using hn
      have hTopY : ∀ j, idx < j → P.val.coeff j = 0 := by
        intro j hj
        simpa using hY j (by omega)
      rcases leeOSullivanTopCancellation V R params hdistinct hR hidxWidth hTopY hmult with
        ⟨weight, hcoeffIdx, hhigher, hresMult, htermSpan⟩
      let term := CBivariate.ofYConstant weight *
        (leeOSullivanBasisPolynomials (F := F) R
          (V.vanishingPolynomial (points.map fun point ↦ point.1)) params).getD idx 0
      have hnWidth : n < leeOSullivanWidth params := by omega
      have hresY : ∀ j, n < j → CPolynomial.coeff (P - term) j = 0 := by
        intro j hj
        by_cases hjeq : j = idx
        · subst j
          exact hcoeffIdx
        · have hgt : idx < j := by omega
          exact hhigher j hgt
      have hresSpan : koetterBasisSpanContains basis (P - term) :=
        ih (P := P - term) hnWidth hresY hresMult
      have hsum := koetterBasisSpanContains_add hresSpan htermSpan
      have htermRepr :
          CBivariate.ofYConstant weight *
            (leeOSullivanBasisPolynomials (F := F) R
              (V.vanishingPolynomial (points.map fun point ↦ point.1)) params).getD
                idx 0 = term := by
        rfl
      have hsum' := hsum
      rw [htermRepr] at hsum'
      simpa [term, basis, G, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum'


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
    rcases hExists with ⟨Q, hQ⟩
    let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
    have hRPoints :
        ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2 := by
      intro point hpoint
      have hpointEval := leeCoefficientForm_eval_point V E hdistinct hpoint
      simpa [R, G, CPolynomial.interpolateCoefficientForm] using hpointEval
    have hYBound :
        ∀ j, interpolationYCap params < j → CPolynomial.coeff Q j = 0 := by
      intro j hj
      have hzero :=
        validWitness_coeffY_eq_zero_of_yCap_lt hLow hQ
          (by simpa [koetterYCap, interpolationYCap] using hj)
      simpa using hzero
    have hcapWidth : interpolationYCap params < leeOSullivanWidth params := by
      simp [leeOSullivanWidth]
    have hspan :
        koetterBasisSpanContains
          (leeOSullivanBasisPolynomials (F := F) R G params) Q := by
      simpa [G] using
        (leeOSullivanBasisSpanContains_of_multiplicity_yDegree_le
          V R params hdistinct hRPoints hcapWidth hYBound hQ.2.2)
    exact leeOSullivanPositiveInterpolate_complete_of_span
      V E reducer hdistinct hLow hQ (by simpa [R, G] using hspan)

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
