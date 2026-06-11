/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Correctness.ModularData
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Normalization
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Rows
import CompPoly.LinearAlgebra.PolynomialMatrix.RowSelection

/-!
# Approximant-Basis Interpolation Correctness Surface

Theorem statements for the modular-equation reduction and the public
`GSInterpContext` boundary.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace ApproximantBasis

open PolynomialMatrix
open PolynomialMatrix.Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-! ## Width truncation helpers -/

omit [Nontrivial F] [DecidableEq F] in
/-- Entries of the width truncation of a coefficient row. -/
private theorem rowGet_toCoeffRow_ofCoeffRow (row : PolynomialRow F)
    (width : Nat) {j : Nat} (hj : j < width) :
    rowGet (CBivariate.toCoeffRow width (CBivariate.ofCoeffRow row)) j =
      rowGet row j := by
  rw [CBivariate.toCoeffRow, rowGet, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, CBivariate.ofCoeffRow,
    CPolynomial.coeff_ofArray]
  rfl

omit [Nontrivial F] [DecidableEq F] in
/-- Width truncation preserves all coefficients below the width. -/
private theorem coeff_toCoeffRow_ofCoeffRow (row : PolynomialRow F)
    {width i j : Nat} (hj : j < width) :
    CBivariate.coeff
        (CBivariate.ofCoeffRow (CBivariate.toCoeffRow width
          (CBivariate.ofCoeffRow row))) i j =
      CBivariate.coeff (CBivariate.ofCoeffRow row) i j := by
  have hsize : (CBivariate.toCoeffRow width (CBivariate.ofCoeffRow row)).size =
      width := CBivariate.toCoeffRow_size _ _
  rw [CBivariate.coeff_ofCoeffRow_of_lt _ (by omega)]
  rw [show (CBivariate.toCoeffRow width (CBivariate.ofCoeffRow row)).getD j 0 =
      rowGet (CBivariate.toCoeffRow width (CBivariate.ofCoeffRow row)) j from rfl]
  rw [rowGet_toCoeffRow_ofCoeffRow row width hj]
  rcases Nat.lt_or_ge j row.size with hjrow | hjrow
  · rw [CBivariate.coeff_ofCoeffRow_of_lt _ hjrow]
    rfl
  · rw [CBivariate.coeff_ofCoeffRow_of_size_le _ hjrow]
    rw [show rowGet row j = row.getD j 0 from rfl]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hjrow]
    exact CPolynomial.coeff_zero i

omit [Nontrivial F] [DecidableEq F] in
/-- Every interpolation monomial has `Y`-degree below the interpolation width
when the `Y`-weight is positive. -/
private theorem interpolationMonomials_yDegree_lt (params : GSInterpParams)
    (hw : 0 < yWeight params) {m : CBivariate.Monomial}
    (hm : m ∈ (interpolationMonomials params).toList) :
    m.yDegree < interpolationWidth params := by
  have hbound := CBivariate.monomialsWeightedDegreeLE_sound
    (xWeight := 1) (yWeight := yWeight params)
    (bound := params.weightedDegreeBound) (by simpa [interpolationMonomials] using hm)
  have hy : yWeight params * m.yDegree ≤ params.weightedDegreeBound := by omega
  have hycap : m.yDegree ≤ interpolationYCap params := by
    rw [interpolationYCap, Nat.le_div_iff_mul_le hw]
    calc m.yDegree * yWeight params = yWeight params * m.yDegree :=
          Nat.mul_comm _ _
      _ ≤ params.weightedDegreeBound := by omega
  rw [interpolationWidth]
  omega

omit [Nontrivial F] [DecidableEq F] in
/-- The interpolation coefficient vector only sees the first
`interpolationWidth params` coefficient rows. -/
private theorem interpolationCoefficientVector_toCoeffRow (params : GSInterpParams)
    (hw : 0 < yWeight params) (row : PolynomialRow F) :
    interpolationCoefficientVector params
        (CBivariate.ofCoeffRow (CBivariate.toCoeffRow (interpolationWidth params)
          (CBivariate.ofCoeffRow row))) =
      interpolationCoefficientVector params (CBivariate.ofCoeffRow row) := by
  rw [interpolationCoefficientVector, interpolationCoefficientVector,
    interpolationCoefficientVectorOnBasis, interpolationCoefficientVectorOnBasis]
  apply Array.ext
  · simp
  · intro i hi _hi'
    have hi' : i < (interpolationMonomials params).size := by
      simpa using hi
    simp only [Array.getElem_map]
    exact coeff_toCoeffRow_ofCoeffRow row
      (interpolationMonomials_yDegree_lt params hw
        (Array.getElem_mem_toList hi'))

omit [Nontrivial F] [DecidableEq F] in
/-- Width truncation does not increase the shifted row degree. -/
private theorem rowShiftedDegree?_toCoeffRow_le {row : PolynomialRow F}
    {shift : Array Nat} {width d d' : Nat}
    (hd : rowShiftedDegree? row shift = some d)
    (hd' : rowShiftedDegree?
      (CBivariate.toCoeffRow width (CBivariate.ofCoeffRow row)) shift = some d') :
    d' ≤ d := by
  rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hd' with
    ⟨j, hj, hentry⟩
  have hjw : j < width := by
    simpa [CBivariate.toCoeffRow_size] using hj
  have hgets := rowGet_toCoeffRow_ofCoeffRow row width hjw
  simp only [shiftedEntryDegree?, hgets] at hentry
  have hne : ¬ rowGet row j == 0 := by
    by_contra h0
    rw [if_pos h0] at hentry
    cases hentry
  have hjrow : j < row.size := by
    by_contra hge
    apply hne
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp
  refine shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hd hjrow ?_
  simp only [shiftedEntryDegree?]
  exact hentry

omit [Nontrivial F] [DecidableEq F] in
/-- A vector with all-zero entries does not normalize. -/
private theorem normalizeVector?_eq_none_of_all_zero {v : Array F}
    (h : ∀ i, i < v.size → v.getD i 0 = 0) :
    normalizeVector? v = none := by
  have hfirst : firstNonzeroIndex? v = none := by
    rw [firstNonzeroIndex?, List.find?_eq_none]
    intro i hi
    have := h i (List.mem_range.mp hi)
    simp [this]
  rw [normalizeVector?, hfirst]

/-- The coefficient row of a zero row never normalizes. -/
private theorem normalizeInterpolationPolynomial?_eq_none_of_rowIsZero
    (params : GSInterpParams) {row : PolynomialRow F} (h : RowIsZero row) :
    normalizeInterpolationPolynomial? params
      (interpolationCoefficientVector params (CBivariate.ofCoeffRow row)) = none := by
  have hz : ∀ i,
      i < (interpolationCoefficientVector params
        (CBivariate.ofCoeffRow row)).size →
      (interpolationCoefficientVector params
        (CBivariate.ofCoeffRow row)).getD i 0 = 0 := by
    intro i hi
    rw [interpolationCoefficientVector, interpolationCoefficientVectorOnBasis] at hi ⊢
    have hi' : i < (interpolationMonomials params).size := by simpa using hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Option.getD_some, Array.getElem_map]
    rcases Nat.lt_or_ge ((interpolationMonomials params)[i]).yDegree row.size with
      hj | hj
    · rw [CBivariate.coeff_ofCoeffRow_of_lt _ hj]
      have hrow0 : row.getD ((interpolationMonomials params)[i]).yDegree 0 = 0 := by
        refine h _ ?_
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj,
          Option.getD_some]
        exact Array.getElem_mem_toList hj
      rw [hrow0]
      exact CPolynomial.coeff_zero _
    · exact CBivariate.coeff_ofCoeffRow_of_size_le _ hj
  rw [normalizeInterpolationPolynomial?, normalizeInterpolationPolynomialOnBasis?,
    normalizeVector?_eq_none_of_all_zero hz]

/-! ## The modular-equation layer -/

/-- The executable GS modular row predicate is equivalent to packed
multiplicity constraints for the bivariate coefficient-row view, for distinct
interpolation nodes and rows inside the interpolation width. -/
theorem gsModularEquation_row_iff_multiplicity
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (modCtx : CPolynomial.ModContext F)
    (mulCtx : CPolynomial.MulContext F)
    (points : Array (F × F)) (params : GSInterpParams)
    (row : PolynomialRow F)
    (hdistinct : DistinctXCoordinates points)
    (hwidth : row.size ≤ interpolationWidth params) :
    let data := buildGSModularData V E mulCtx modCtx points params
    rowSatisfiesModularBool mulCtx modCtx row data.matrix data.moduli = true ↔
      CBivariate.satisfiesMultiplicityConstraintsBool
        (CBivariate.ofCoeffRow row) points params.multiplicity = true := by
  intro data
  set G := V.vanishingPolynomial (points.map fun point ↦ point.1) with hGdef
  set R := CPolynomial.interpolateCoefficientFormWithVanishing E G points with hRdef
  have hGcorrect : G =
      CPolynomial.vanishingPolynomialArray (points.map fun point ↦ point.1) :=
    V.correct _
  have hG : Polynomial.Monic G.toPoly := by
    rw [hGcorrect]
    exact vanishingPolynomialArray_toPoly_monic _
  have hdata_matrix : data.matrix = gsRelationMatrixWithRG mulCtx modCtx R G params :=
    rfl
  have hdata_moduli : data.moduli = gsModuli mulCtx G params.multiplicity := rfl
  rw [hdata_matrix, hdata_moduli,
    rowSatisfiesModularBool_gsRelationMatrix_iff mulCtx modCtx hG R params hwidth]
  have hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2 := by
    intro point hpoint
    have heval := CPolynomial.interpolateCoefficientForm_eval_point V E
      (by simpa [DistinctXCoordinates] using hdistinct) hpoint
    simpa [hRdef, hGdef, CPolynomial.interpolateCoefficientForm] using heval
  rw [CBivariate.satisfiesMultiplicityConstraintsBool_iff_hasMultiplicity,
    ← CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity,
    ← vanishing_pow_dvd_hasseDeriv_eval_iff_satisfiesMultiplicityConstraints
      hdistinct hR,
    hGcorrect]

/-! ## Soundness -/

/-- Soundness for executable approximant-basis interpolation. -/
theorem approximantBasisInterpolate_sound
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h :
      approximantBasisInterpolate V E solver points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold approximantBasisInterpolate at h
  by_cases hLow : params.messageDegree ≤ 1
  · simp only [hLow, if_true, Option.some_inj] at h
    rw [← h]
    exact lowMessageDegreeInterpolation_sound (points := points) (params := params) hLow
  · simp only [hLow, if_false] at h
    rw [approximantBasisPositiveInterpolate] at h
    by_cases hdistinctBool : distinctXCoordinatesBool points = true
    · rw [if_pos hdistinctBool] at h
      have hdistinct : DistinctXCoordinates points :=
        LeeOSullivan.distinctXCoordinatesBool_iff.mp hdistinctBool
      set G := V.vanishingPolynomial (points.map fun point ↦ point.1) with hGdef
      set R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
        with hRdef
      set data := buildGSModularDataWithRG solver.mulContext solver.modContext
        R G params with hdata
      set basis := solver.solutionBasis (modularEquation data) data.shift
        (some params.weightedDegreeBound) with hbasis
      change (match leastShiftedDegreeChoice? basis data.shift with
        | none => none
        | some choice =>
            if choice.degree ≤ params.weightedDegreeBound then
              normalizeApproximantCandidate? params (CBivariate.ofCoeffRow choice.row)
            else none) = some Q at h
      cases hchoice : leastShiftedDegreeChoice? basis data.shift with
      | none =>
          rw [hchoice] at h
          change (none : Option (CBivariate F)) = some Q at h
          simp at h
      | some choice =>
          rw [hchoice] at h
          change (if choice.degree ≤ params.weightedDegreeBound then
              normalizeApproximantCandidate? params (CBivariate.ofCoeffRow choice.row)
            else none) = some Q at h
          by_cases hdeg : choice.degree ≤ params.weightedDegreeBound
          · rw [if_pos hdeg] at h
            -- The chosen row is a basis member satisfying the modular predicate.
            rcases leastShiftedDegreeChoice?_some_valid hchoice with
              ⟨hindex, hrowEq, hrowDeg⟩
            have hmem : choice.row ∈ MatrixRows basis := by
              rw [MatrixRows, hrowEq, Array.getD_eq_getD_getElem?,
                Array.getElem?_eq_getElem hindex, Option.getD_some]
              exact Array.getElem_mem_toList hindex
            have hsat := solver.sound (modularEquation data) data.shift
              (some params.weightedDegreeBound) choice.row hmem
            -- Truncate the chosen row to the interpolation width.
            set width := interpolationWidth params with hwidthdef
            set row' := CBivariate.toCoeffRow width
              (CBivariate.ofCoeffRow choice.row) with hrow'
            have hrow'size : row'.size = width := CBivariate.toCoeffRow_size _ _
            have hmatrixsize : (modularEquation data).matrix.size = width :=
              gsRelationMatrixWithModuli_size _ _ _ _ _
            have hagree : ∀ k, k < (modularEquation data).matrix.size →
                rowGet choice.row k = rowGet row' k := by
              intro k hk
              rw [hrow', rowGet_toCoeffRow_ofCoeffRow choice.row width
                (by omega)]
            have hsat' : rowSatisfiesModularBool solver.mulContext solver.modContext
                row' (modularEquation data).matrix (modularEquation data).moduli =
                  true := by
              rw [← rowSatisfiesModularBool_congr_of_agree solver.mulContext
                solver.modContext (modularEquation data).matrix
                (modularEquation data).moduli hagree]
              exact hsat
            -- Transfer to multiplicity constraints for the truncated polynomial.
            have hiff := gsModularEquation_row_iff_multiplicity V E
              solver.modContext solver.mulContext points params row' hdistinct
              (by omega)
            have hdataEq : buildGSModularData V E solver.mulContext
                solver.modContext points params = data := rfl
            rw [hdataEq] at hiff
            have hmultBool := hiff.mp hsat'
            have hmult : CBivariate.SatisfiesMultiplicityConstraints
                (CBivariate.ofCoeffRow row') points params.multiplicity := by
              rw [CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity]
              exact (CBivariate.satisfiesMultiplicityConstraintsBool_iff_hasMultiplicity
                _ _ _).mp hmultBool
            -- The normalization only sees in-width coefficients.
            have hw : 0 < yWeight params := by
              rw [yWeight]
              omega
            have hvec := interpolationCoefficientVector_toCoeffRow params hw
              choice.row
            have hnorm' : LeeOSullivan.normalizeLeeCandidate? params
                (CBivariate.ofCoeffRow row') = some Q := by
              rw [LeeOSullivan.normalizeLeeCandidate?,
                normalizeInterpolationPolynomial?, hrow', hvec]
              rw [normalizeApproximantCandidate?,
                normalizeInterpolationPolynomial?] at h
              exact h
            -- The truncated row is nonzero with bounded shifted degree.
            cases hd' : rowShiftedDegree? row' data.shift with
            | none =>
                exfalso
                have hzero : RowIsZero row' :=
                  rowShiftedDegree?_eq_none_iff.mp hd'
                rw [LeeOSullivan.normalizeLeeCandidate?,
                  normalizeInterpolationPolynomial?_eq_none_of_rowIsZero params
                    hzero] at hnorm'
                simp at hnorm'
            | some d' =>
                have hd'le : d' ≤ choice.degree :=
                  rowShiftedDegree?_toCoeffRow_le hrowDeg hd'
                have hshiftEq : data.shift =
                    CBivariate.weightedDegreeShift (yWeight params) row'.size := by
                  rw [hrow'size, hwidthdef]
                  rfl
                have hdegRaw : CBivariate.natWeightedDegree
                    (CBivariate.ofCoeffRow row') 1 (yWeight params) ≤
                      params.weightedDegreeBound := by
                  refine CBivariate.natWeightedDegree_ofCoeffRow_le_of_rowShiftedDegree?_le
                    row' (yWeight params) params.weightedDegreeBound d' ?_ (by omega)
                  rw [← hshiftEq]
                  exact hd'
                exact LeeOSullivan.normalizeLeeCandidate?_sound_of_raw
                  (points := points) (params := params) hLow hdegRaw hmult hnorm'
          · rw [if_neg hdeg] at h
            simp at h
    · rw [if_neg hdistinctBool] at h
      simp at h

/-! ## Completeness -/

omit [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- The shifted row degree only sees shift entries below the row size. -/
private theorem rowShiftedDegree?_congr_shift {row : PolynomialRow F}
    {shift shift' : Array Nat}
    (h : ∀ j, j < row.size → shift.getD j 0 = shift'.getD j 0) :
    rowShiftedDegree? row shift = rowShiftedDegree? row shift' := by
  rw [rowShiftedDegree?, rowShiftedDegree?]
  refine List.foldl_ext _ _ _ fun acc j hj ↦ ?_
  have hj' : j < row.size := List.mem_range.mp hj
  simp only [shiftedEntryDegree?, h j hj']

omit [Nontrivial F] [DecidableEq F] in
/-- Entry access for the weighted-degree shift array. -/
private theorem weightedDegreeShift_getD {w width j : Nat} (hj : j < width) :
    (CBivariate.weightedDegreeShift w width).getD j 0 = j * w := by
  rw [CBivariate.weightedDegreeShift, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

omit [DecidableEq F] in
/-- Zero rows have zero coefficient rows. -/
private theorem ofCoeffRow_eq_zero_of_rowIsZero {row : PolynomialRow F}
    (h : RowIsZero row) : CBivariate.ofCoeffRow row = 0 := by
  rw [CBivariate.ofCoeffRow]
  show (CPolynomial.ofArray row : CPolynomial (CPolynomial F)) = 0
  rw [CPolynomial.eq_zero_iff_coeff_zero]
  intro n
  rw [CPolynomial.coeff_ofArray]
  rcases Nat.lt_or_ge n row.size with hn | hn
  · refine h _ ?_
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hn, Option.getD_some]
    exact Array.getElem_mem_toList hn
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn]
    rfl

omit [Nontrivial F] [DecidableEq F] in
/-- Bounded-weighted-degree polynomials have no `Y`-coefficients at or above
the interpolation width. -/
private theorem coeff_eq_zero_of_interpolationWidth_le
    {params : GSInterpParams} (hw : 0 < yWeight params) {Q : CBivariate F}
    (hdeg : CBivariate.natWeightedDegree Q 1 (yWeight params) ≤
      params.weightedDegreeBound)
    {j : Nat} (hj : interpolationWidth params ≤ j) :
    CPolynomial.coeff Q j = 0 := by
  have hcoeffs : ∀ i, CBivariate.coeff Q i j = 0 := by
    intro i
    by_contra hne0
    have hle := (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params)
      params.weightedDegreeBound).mp hdeg i j hne0
    have hdm := Nat.div_add_mod params.weightedDegreeBound (yWeight params)
    have hmod := Nat.mod_lt params.weightedDegreeBound hw
    have hsum : (params.weightedDegreeBound / yWeight params + 1) * yWeight params
        = yWeight params * (params.weightedDegreeBound / yWeight params) +
          yWeight params := by
      ring
    have hwidthmul : (params.weightedDegreeBound / yWeight params + 1) *
        yWeight params ≤ j * yWeight params := by
      refine Nat.mul_le_mul_right _ ?_
      rw [interpolationWidth, interpolationYCap] at hj
      omega
    have hcomm : j * yWeight params = yWeight params * j := Nat.mul_comm _ _
    omega
  show CPolynomial.coeff Q j = 0
  rw [CPolynomial.eq_zero_iff_coeff_zero]
  intro i
  exact hcoeffs i

omit [Nontrivial F] [DecidableEq F] in
/-- Width truncation is the identity on bounded-weighted-degree polynomials. -/
private theorem ofCoeffRow_toCoeffRow_eq
    {params : GSInterpParams} (hw : 0 < yWeight params) {Q : CBivariate F}
    (hdeg : CBivariate.natWeightedDegree Q 1 (yWeight params) ≤
      params.weightedDegreeBound) :
    CBivariate.ofCoeffRow (CBivariate.toCoeffRow (interpolationWidth params) Q) =
      Q := by
  rw [CBivariate.ofCoeffRow]
  show (CPolynomial.ofArray (CBivariate.toCoeffRow (interpolationWidth params) Q) :
    CPolynomial (CPolynomial F)) = Q
  apply CPolynomial.eq_iff_coeff.2
  intro n
  rw [CPolynomial.coeff_ofArray]
  rcases Nat.lt_or_ge n (interpolationWidth params) with hn | hn
  · rw [CBivariate.toCoeffRow, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_range hn, Option.map_some, Option.getD_some]
  · rw [CBivariate.toCoeffRow, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_eq_none (by simpa using hn),
      Option.map_none, Option.getD_none]
    exact (coeff_eq_zero_of_interpolationWidth_le hw hdeg hn).symm

/-- Completeness for executable approximant-basis interpolation on distinct
input `x`-coordinates. -/
theorem approximantBasisInterpolate_complete
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (points : Array (F × F)) (params : GSInterpParams)
    (hdistinct : DistinctXCoordinates points)
    (hexists : ∃ Q, ValidInterpolationWitness points params Q) :
    ∃ Q, approximantBasisInterpolate V E solver points params = some Q := by
  by_cases hLow : params.messageDegree ≤ 1
  · refine ⟨lowMessageDegreeInterpolation points params.multiplicity, ?_⟩
    unfold approximantBasisInterpolate
    rw [if_pos hLow]
  · rcases hexists with ⟨Q₀, hQ₀ne, hQ₀deg, hQ₀mult⟩
    have hw : 0 < yWeight params := by
      rw [yWeight]
      omega
    have hdistinctBool : distinctXCoordinatesBool points = true :=
      LeeOSullivan.distinctXCoordinatesBool_iff.mpr hdistinct
    set G := V.vanishingPolynomial (points.map fun point ↦ point.1) with hGdef
    set R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
      with hRdef
    set data := buildGSModularDataWithRG solver.mulContext solver.modContext
      R G params with hdata
    set basis := solver.solutionBasis (modularEquation data) data.shift
      (some params.weightedDegreeBound) with hbasis
    set width := interpolationWidth params with hwidthdef
    -- The witness coefficient row.
    set row₀ := CBivariate.toCoeffRow width Q₀ with hrow₀
    have hround : CBivariate.ofCoeffRow row₀ = Q₀ :=
      ofCoeffRow_toCoeffRow_eq hw hQ₀deg
    have hrow₀size : row₀.size = width := CBivariate.toCoeffRow_size _ _
    have hnz₀ : rowIsZero row₀ = false := by
      rw [Bool.eq_false_iff]
      intro htrue
      exact hQ₀ne (by rw [← hround,
        ofCoeffRow_eq_zero_of_rowIsZero (rowIsZero_iff.mp htrue)])
    have hmatrixsize : (modularEquation data).matrix.size = width :=
      gsRelationMatrixWithModuli_size _ _ _ _ _
    have hsolwidth : (modularEquation data).solutionWidth = width := by
      rw [ModularEquation.solutionWidth, hmatrixsize]
    -- The witness row satisfies the modular predicate.
    have hsat₀ : rowSatisfiesModularBool solver.mulContext solver.modContext row₀
        (modularEquation data).matrix (modularEquation data).moduli = true := by
      have hiff := gsModularEquation_row_iff_multiplicity V E
        solver.modContext solver.mulContext points params row₀ hdistinct
        (by omega)
      have hdataEq : buildGSModularData V E solver.mulContext
          solver.modContext points params = data := rfl
      rw [hdataEq] at hiff
      refine hiff.mpr ?_
      rw [hround]
      exact (CBivariate.satisfiesMultiplicityConstraintsBool_iff_hasMultiplicity
        _ _ _).mpr hQ₀mult
    -- The witness row has shifted degree at most the weighted-degree bound.
    have hshift₀ : data.shift = CBivariate.weightedDegreeShift (yWeight params)
        row₀.size := by
      rw [hrow₀size]
      rfl
    obtain ⟨d₀, hd₀⟩ : ∃ d₀, rowShiftedDegree? row₀ data.shift = some d₀ := by
      cases hcase : rowShiftedDegree? row₀ data.shift with
      | none =>
          have hzero := rowShiftedDegree?_eq_none_iff.mp hcase
          rw [Bool.eq_false_iff] at hnz₀
          exact absurd (rowIsZero_iff.mpr hzero) hnz₀
      | some d => exact ⟨d, rfl⟩
    have hd₀le : d₀ ≤ params.weightedDegreeBound := by
      have hnat := CBivariate.rowShiftedDegree?_eq_natWeightedDegree_ofCoeffRow
        row₀ (yWeight params) d₀ (by rw [← hshift₀]; exact hd₀)
      rw [hround] at hnat
      omega
    -- The GS moduli are monic powers of the vanishing polynomial.
    have hGmonic : Polynomial.Monic G.toPoly := by
      rw [show G = CPolynomial.vanishingPolynomialArray
          (points.map fun point ↦ point.1) from V.correct _]
      exact vanishingPolynomialArray_toPoly_monic _
    have hmonic : ∀ b, b < (modularEquation data).moduli.size →
        ((modularEquation data).moduli.getD b 0).monic := by
      intro b hb
      have hsize : (modularEquation data).moduli.size = params.multiplicity :=
        gsModuli_size _ _ _
      have hgetD : (modularEquation data).moduli.getD b 0 =
          G ^ (params.multiplicity - b) :=
        gsModuli_getD solver.mulContext G (by omega)
      rw [hgetD]
      refine (CPolynomial.monic_toPoly_iff _).mpr ?_
      rw [CPolynomial.toPoly_pow]
      exact hGmonic.pow _
    -- The relation matrix exposes every modular column to the row predicate.
    have hcols : (modularEquation data).moduli.size ≤
        MatrixWidth (modularEquation data).matrix := by
      have hmodsize : (modularEquation data).moduli.size = params.multiplicity :=
        gsModuli_size _ _ _
      have hmatwidth : MatrixWidth (modularEquation data).matrix =
          params.multiplicity :=
        gsRelationMatrixWithModuli_matrixWidth _ _ _ _ _
      omega
    -- The GS shift is aligned with the principal solution width.
    have hshiftsize : data.shift.size = (modularEquation data).solutionWidth := by
      have hdatashift : data.shift =
          CBivariate.weightedDegreeShift (yWeight params) width := rfl
      rw [hdatashift, hsolwidth, CBivariate.weightedDegreeShift]
      simp
    -- Apply the solver completeness/minimality contract with the GS
    -- weighted-degree bound: the witness row is within the bound, so the
    -- returned basis contains a row whose shifted degree meets it.
    rcases solver.complete_minimal (modularEquation data) data.shift
        (some params.weightedDegreeBound) row₀ d₀ hmonic hcols
        hshiftsize hsat₀ hnz₀ (by omega) hd₀
        (fun bound hbound ↦ by
          obtain rfl : params.weightedDegreeBound = bound :=
            Option.some.inj hbound
          exact hd₀le) with
      ⟨hbasisWidth, basisRow, bDeg, hbMem, hbDeg, hbLe⟩
    have hbDegLe : bDeg ≤ params.weightedDegreeBound := by
      rwa [Option.getD_some] at hbLe
    -- Select the least shifted-degree basis row.
    rcases List.getElem_of_mem hbMem with ⟨bIdx, hbIdxList, hbGet⟩
    have hbIdx : bIdx < basis.size := by
      simpa [MatrixRows] using hbIdxList
    have hbGetD : basis.getD bIdx #[] = basisRow := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hbIdx,
        Option.getD_some]
      simpa [MatrixRows, Array.getElem_toList] using hbGet
    rcases leastShiftedDegreeChoice?_some_of_degree (M := basis)
        (shift := data.shift) (i := bIdx) (d := bDeg) hbIdx
        (by rw [hbGetD]; exact hbDeg) with
      ⟨choice, hchoice, hchoiceLe⟩
    have hchoiceBound : choice.degree ≤ params.weightedDegreeBound := by
      omega
    rcases leastShiftedDegreeChoice?_some_valid hchoice with
      ⟨hcIdx, hcRow, hcDeg⟩
    have hcMem : choice.row ∈ MatrixRows basis := by
      rw [MatrixRows, hcRow, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hcIdx, Option.getD_some]
      exact Array.getElem_mem_toList hcIdx
    have hcWidth : choice.row.size ≤ width := by
      have := hbasisWidth choice.row hcMem
      omega
    -- The chosen row reconstructs and normalizes.
    have hrawNe : CBivariate.ofCoeffRow choice.row ≠ 0 :=
      LeeOSullivan.ofCoeffRow_ne_zero_of_rowShiftedDegree?_some hcDeg
    have hcShift : rowShiftedDegree? choice.row
        (CBivariate.weightedDegreeShift (yWeight params) choice.row.size) =
          some choice.degree := by
      rw [← hcDeg]
      refine (rowShiftedDegree?_congr_shift fun j hj ↦ ?_).symm
      rw [weightedDegreeShift_getD hj]
      have hjwidth : j < width := by omega
      have hdatashift : data.shift =
          CBivariate.weightedDegreeShift (yWeight params) width := rfl
      rw [hdatashift, weightedDegreeShift_getD hjwidth]
    have hdegRaw : CBivariate.natWeightedDegree (CBivariate.ofCoeffRow choice.row)
        1 (yWeight params) ≤ params.weightedDegreeBound :=
      CBivariate.natWeightedDegree_ofCoeffRow_le_of_rowShiftedDegree?_le
        choice.row (yWeight params) params.weightedDegreeBound choice.degree
        hcShift hchoiceBound
    rcases LeeOSullivan.normalizeLeeCandidate?_some_of_raw hLow hrawNe hdegRaw with
      ⟨Q, hnorm⟩
    -- Assemble the executable run.
    refine ⟨Q, ?_⟩
    unfold approximantBasisInterpolate
    rw [if_neg hLow, approximantBasisPositiveInterpolate, if_pos hdistinctBool]
    change (match leastShiftedDegreeChoice? basis data.shift with
      | none => none
      | some choice =>
          if choice.degree ≤ params.weightedDegreeBound then
            normalizeApproximantCandidate? params (CBivariate.ofCoeffRow choice.row)
          else none) = some Q
    rw [hchoice]
    change (if choice.degree ≤ params.weightedDegreeBound then
        normalizeApproximantCandidate? params (CBivariate.ofCoeffRow choice.row)
      else none) = some Q
    rw [if_pos hchoiceBound]
    rw [normalizeApproximantCandidate?]
    rw [LeeOSullivan.normalizeLeeCandidate?] at hnorm
    exact hnorm

/-- Public approximant-basis interpolation backend context. -/
def approximantBasisInterpContext
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F) : GSInterpContext F where
  interpolate := approximantBasisInterpolate V E solver
  sound := by
    intro points params Q h
    exact approximantBasisInterpolate_sound V E solver h
  complete := by
    intro points params hdistinct hexists
    exact approximantBasisInterpolate_complete V E solver points params hdistinct hexists

end ApproximantBasis

end GuruswamiSudan

end CompPoly
