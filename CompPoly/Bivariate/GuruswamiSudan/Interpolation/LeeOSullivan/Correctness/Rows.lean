/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Basis
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Combinations
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness

/-!
# Lee-O'Sullivan Row-Span Transport Helpers

Transport between executable polynomial rows and semantic bivariate span combinations.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- Within the Lee row width, a row-linear combination of executable Lee rows
has the same coefficients as the corresponding bivariate basis combination. -/
theorem coeff_ofCoeffRow_rowLinearCombination_lee_of_lt
    (R G : CPolynomial F) (params : GSInterpParams)
    (coeffs : Array (CPolynomial F)) {k j : Nat}
    (hj : j < leeOSullivanWidth params) :
    CBivariate.coeff
        (CBivariate.ofCoeffRow
          (rowLinearCombination coeffs
            (leeOSullivanBasisRowsWithRG R G params))) k j =
      CBivariate.coeff
        (koetterBasisCombination (fun i ↦ coeffs.getD i 0)
          (leeOSullivanBasisPolynomials (F := F) R G params)) k j := by
  have hrowSize :
      (rowLinearCombination coeffs (leeOSullivanBasisRowsWithRG R G params)).size =
        leeOSullivanWidth params := by
    rw [rowLinearCombination_size
      (M := leeOSullivanBasisRowsWithRG R G params)
      (leeOSullivanBasisRowsWithRG_wellFormed R G params)]
    exact leeOSullivanBasisRowsWithRG_width R G params
  rw [CBivariate.coeff_ofCoeffRow_of_lt
    (row := rowLinearCombination coeffs (leeOSullivanBasisRowsWithRG R G params))
    (i := k) (j := j) (by simpa [hrowSize] using hj)]
  change (rowGet
      (rowLinearCombination coeffs (leeOSullivanBasisRowsWithRG R G params)) j).coeff k =
    CBivariate.coeff
      (koetterBasisCombination (fun i ↦ coeffs.getD i 0)
        (leeOSullivanBasisPolynomials (F := F) R G params)) k j
  rw [rowGet_rowLinearCombination_coeff]
  rw [coeff_koetterBasisCombination]
  rw [leeOSullivanBasisPolynomials_size]
  rw [foldl_range_add_eq_sum]
  rw [show (leeOSullivanBasisRowsWithRG R G params).size =
      leeOSullivanWidth params by
    simp [leeOSullivanBasisRowsWithRG, leeOSullivanWidth]]
  apply Finset.sum_congr rfl
  intro i hi
  have hiWidth : i < leeOSullivanWidth params := Finset.mem_range.mp hi
  rw [rowGet_leeOSullivanBasisRowsWithRG_getD R G params hiWidth hj]
  rw [leeOSullivanBasisPolynomials_getD_of_lt R G params hiWidth]
  rw [coeff_ofYConstant_mul]

/-- Lee basis polynomials are bounded by the Lee row width in `Y`. -/
theorem leeOSullivanBasisPolynomial_coeff_eq_zero_of_width_le
    (R G : CPolynomial F) (params : GSInterpParams) {idx x j : Nat}
    (hidx : idx < leeOSullivanWidth params) (hj : leeOSullivanWidth params ≤ j) :
    CBivariate.coeff (leeOSullivanBasisPolynomial R G params idx) x j = 0 := by
  let t := leeOSullivanT params idx
  let Ypow : CBivariate F := (CBivariate.Y : CBivariate F) ^ (idx - t)
  let Lpow : CBivariate F := CBivariate.linearYDivisor R ^ t
  let Gpow : CBivariate F := CBivariate.ofYConstant G ^ (params.multiplicity - t)
  have hY : (CBivariate.Y : CBivariate F).natDegree ≤ 1 := by
    have hC : (CPolynomial.C (1 : F) : CPolynomial F) ≠ 0 := by
      intro h
      have hc := congrArg (fun p : CPolynomial F ↦ CPolynomial.coeff p 0) h
      change CPolynomial.coeff (CPolynomial.C (1 : F) : CPolynomial F) 0 =
        CPolynomial.coeff (0 : CPolynomial F) 0 at hc
      rw [CPolynomial.coeff_C, if_pos rfl, CPolynomial.coeff_zero] at hc
      exact one_ne_zero hc
    rw [CBivariate.Y, CPolynomial.natDegree_monomial hC]
  have hL : (CBivariate.linearYDivisor R : CBivariate F).natDegree ≤ 1 := by
    rw [CPolynomial.natDegree_toPoly, CBivariate.linearYDivisor_toPoly]
    simp
  have hG : (CBivariate.ofYConstant G : CBivariate F).natDegree ≤ 0 := by
    rw [CPolynomial.natDegree_toPoly]
    simp [CBivariate.ofYConstant, CPolynomial.C_toPoly]
  have hYpow : Ypow.natDegree ≤ idx - t := by
    simpa [Ypow] using
      cpoly_natDegree_pow_le (P := (CBivariate.Y : CBivariate F)) hY (idx - t)
  have hLpow : Lpow.natDegree ≤ t := by
    simpa [Lpow] using
      cpoly_natDegree_pow_le (P := (CBivariate.linearYDivisor R : CBivariate F)) hL t
  have hGpow : Gpow.natDegree ≤ 0 := by
    have hpow := cpoly_natDegree_pow_le
      (P := (CBivariate.ofYConstant G : CBivariate F)) hG
      (params.multiplicity - t)
    simpa [Gpow] using hpow
  have hprod :
      (Ypow * Lpow * Gpow).natDegree ≤ idx := by
    have hYL : (Ypow * Lpow).natDegree ≤ (idx - t) + t := by
      calc
        (Ypow * Lpow).natDegree ≤ Ypow.natDegree + Lpow.natDegree :=
          cpoly_natDegree_mul_le_semiring Ypow Lpow
        _ ≤ (idx - t) + t := Nat.add_le_add hYpow hLpow
    calc
      (Ypow * Lpow * Gpow).natDegree ≤ (Ypow * Lpow).natDegree + Gpow.natDegree :=
        cpoly_natDegree_mul_le_semiring (Ypow * Lpow) Gpow
      _ ≤ ((idx - t) + t) + 0 := Nat.add_le_add hYL hGpow
      _ ≤ idx := by
        have ht : t ≤ idx := by
          simp [t, leeOSullivanT]
        omega
  have hjidx : idx < j := by
    omega
  have hdegree :
      (Ypow * Lpow * Gpow).natDegree < j := lt_of_le_of_lt hprod hjidx
  have hcoeffY :
      (Ypow * Lpow * Gpow).val.coeff j = 0 := by
    exact cpoly_coeff_eq_zero_of_natDegree_lt hdegree
  unfold CBivariate.coeff
  rw [show leeOSullivanBasisPolynomial R G params idx = Ypow * Lpow * Gpow by
    simp [leeOSullivanBasisPolynomial, Ypow, Lpow, Gpow, t]]
  rw [hcoeffY, CPolynomial.coeff_zero]

/-- Bivariate combinations of Lee basis polynomials are bounded by the Lee row
width in `Y`. -/
theorem coeff_koetterBasisCombination_lee_eq_zero_of_width_le
    (R G : CPolynomial F) (params : GSInterpParams)
    (weights : Nat → CPolynomial F) {x j : Nat}
    (hj : leeOSullivanWidth params ≤ j) :
    CBivariate.coeff
        (koetterBasisCombination weights
          (leeOSullivanBasisPolynomials (F := F) R G params)) x j = 0 := by
  rw [coeff_koetterBasisCombination]
  rw [leeOSullivanBasisPolynomials_size]
  rw [foldl_range_add_eq_sum]
  apply Finset.sum_eq_zero
  intro idx hidx
  have hidxWidth : idx < leeOSullivanWidth params := Finset.mem_range.mp hidx
  rw [leeOSullivanBasisPolynomials_getD_of_lt R G params hidxWidth]
  rw [coeff_ofYConstant_mul]
  have hcoeffY :
      (leeOSullivanBasisPolynomial R G params idx).val.coeff j = 0 := by
    apply (CPolynomial.eq_iff_coeff
      (p := (leeOSullivanBasisPolynomial R G params idx).val.coeff j)
      (q := 0)).2
    intro x
    exact leeOSullivanBasisPolynomial_coeff_eq_zero_of_width_le
      R G params hidxWidth hj
  rw [hcoeffY, CPolynomial.mul_zero, CPolynomial.coeff_zero]

/-- A polynomial-row linear combination of the executable Lee rows represents
the same bivariate polynomial as the corresponding Lee basis combination. -/
theorem ofCoeffRow_rowLinearCombination_lee_eq_combination
    (R G : CPolynomial F) (params : GSInterpParams)
    (coeffs : Array (CPolynomial F)) :
    CBivariate.ofCoeffRow
        (rowLinearCombination coeffs
          (leeOSullivanBasisRowsWithRG R G params)) =
      koetterBasisCombination (fun i ↦ coeffs.getD i 0)
        (leeOSullivanBasisPolynomials (F := F) R G params) := by
  apply (CBivariate.eq_iff_coeff).mpr
  intro x j
  by_cases hj : j < leeOSullivanWidth params
  · exact coeff_ofCoeffRow_rowLinearCombination_lee_of_lt
      R G params coeffs hj
  · have hjle : leeOSullivanWidth params ≤ j := Nat.le_of_not_gt hj
    have hrowSize :
        (rowLinearCombination coeffs (leeOSullivanBasisRowsWithRG R G params)).size =
          leeOSullivanWidth params := by
      rw [rowLinearCombination_size
        (M := leeOSullivanBasisRowsWithRG R G params)
        (leeOSullivanBasisRowsWithRG_wellFormed R G params)]
      exact leeOSullivanBasisRowsWithRG_width R G params
    rw [CBivariate.coeff_ofCoeffRow_of_size_le
      (row := rowLinearCombination coeffs (leeOSullivanBasisRowsWithRG R G params))
      (i := x) (j := j) (by simpa [hrowSize] using hjle)]
    exact (coeff_koetterBasisCombination_lee_eq_zero_of_width_le
      R G params (fun i ↦ coeffs.getD i 0) hjle).symm

/-- A row in the executable Lee row span represents a bivariate polynomial in
the corresponding Lee basis span. -/
theorem ofCoeffRow_rowSpan_lee_spanContains
    (R G : CPolynomial F) (params : GSInterpParams) {row : PolynomialRow F}
    (hrow : row ∈ RowSpan (leeOSullivanBasisRowsWithRG R G params)) :
    koetterBasisSpanContains
      (leeOSullivanBasisPolynomials (F := F) R G params)
      (CBivariate.ofCoeffRow row) := by
  rcases hrow with ⟨coeffs, _hcoeffsSize, hrowEq⟩
  refine ⟨fun i ↦ coeffs.getD i 0, ?_⟩
  rw [hrowEq]
  exact (ofCoeffRow_rowLinearCombination_lee_eq_combination
    R G params coeffs).symm

theorem koetterBasisCombination_add_weights
    (weights₁ weights₂ : Nat → CPolynomial F) (basis : Array (CBivariate F)) :
    koetterBasisCombination (fun idx ↦ weights₁ idx + weights₂ idx) basis =
      koetterBasisCombination weights₁ basis +
        koetterBasisCombination weights₂ basis := by
  unfold koetterBasisCombination
  have hterms :
      (List.range basis.size).foldl
          (fun out idx ↦
            out + CBivariate.ofYConstant (weights₁ idx + weights₂ idx) *
              basis.getD idx 0) 0 =
        (List.range basis.size).foldl
          (fun out idx ↦
            out + (CBivariate.ofYConstant (weights₁ idx) * basis.getD idx 0 +
              CBivariate.ofYConstant (weights₂ idx) * basis.getD idx 0)) 0 := by
    apply foldl_add_congr_terms
    intro idx _hidx
    rw [ofYConstant_add, add_mul]
  rw [hterms]
  rw [foldl_add_distrib_terms]

theorem koetterBasisCombination_neg_weights
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F)) :
    koetterBasisCombination (fun idx ↦ -weights idx) basis =
      -koetterBasisCombination weights basis := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [coeff_koetterBasisCombination, CBivariate.coeff_neg,
    coeff_koetterBasisCombination]
  rw [foldl_range_add_eq_sum, foldl_range_add_eq_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro idx _hidx
  rw [ofYConstant_neg, neg_mul, CBivariate.coeff_neg]

theorem koetterBasisSpanContains_add
    {basis : Array (CBivariate F)} {P Q : CBivariate F}
    (hP : koetterBasisSpanContains basis P)
    (hQ : koetterBasisSpanContains basis Q) :
    koetterBasisSpanContains basis (P + Q) := by
  rcases hP with ⟨weightsP, hweightsP⟩
  rcases hQ with ⟨weightsQ, hweightsQ⟩
  refine ⟨fun idx ↦ weightsP idx + weightsQ idx, ?_⟩
  rw [koetterBasisCombination_add_weights, hweightsP, hweightsQ]

theorem koetterBasisSpanContains_neg
    {basis : Array (CBivariate F)} {P : CBivariate F}
    (hP : koetterBasisSpanContains basis P) :
    koetterBasisSpanContains basis (-P) := by
  rcases hP with ⟨weights, hweights⟩
  refine ⟨fun idx ↦ -weights idx, ?_⟩
  rw [koetterBasisCombination_neg_weights, hweights]

theorem koetterBasisSpanContains_sub
    {basis : Array (CBivariate F)} {P Q : CBivariate F}
    (hP : koetterBasisSpanContains basis P)
    (hQ : koetterBasisSpanContains basis Q) :
    koetterBasisSpanContains basis (P - Q) := by
  rw [sub_eq_add_neg]
  exact koetterBasisSpanContains_add hP (koetterBasisSpanContains_neg hQ)

theorem koetterBasisCombination_single_weight
    (basis : Array (CBivariate F)) {idx : Nat} (hidx : idx < basis.size)
    (weight : CPolynomial F) :
    koetterBasisCombination
        (fun j ↦ if j == idx then weight else 0) basis =
      CBivariate.ofYConstant weight * basis.getD idx 0 := by
  unfold koetterBasisCombination
  have hgetD : basis.getD idx 0 = basis[idx] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hidx]
  let targetTerm : CBivariate F := CBivariate.ofYConstant weight * basis[idx]
  have hterms :
      ∀ j, j ∈ List.range basis.size →
        CBivariate.ofYConstant (if j == idx then weight else 0) *
            basis.getD j 0 =
          if j == idx then targetTerm else 0 := by
    intro j _hj
    by_cases hbeq : j == idx
    · have hEq : j = idx := LawfulBEq.eq_of_beq hbeq
      subst j
      simp [targetTerm, hgetD]
    · rw [if_neg hbeq, if_neg hbeq, ofYConstant_zero, zero_mul]
  have hfold :
      (List.range basis.size).foldl
          (fun out j ↦
            out + CBivariate.ofYConstant (if j == idx then weight else 0) *
              basis.getD j 0) 0 =
        (List.range basis.size).foldl
          (fun out j ↦ out + if j == idx then targetTerm else 0) 0 := by
    apply foldl_add_congr_terms
    exact hterms
  rw [hfold]
  rw [hgetD]
  simpa [targetTerm] using
    foldl_add_single_beq_of_nodup_mem (List.range basis.size) idx targetTerm
      List.nodup_range (List.mem_range.mpr hidx)

theorem koetterBasisSpanContains_single
    (basis : Array (CBivariate F)) {idx : Nat} (hidx : idx < basis.size)
    (weight : CPolynomial F) :
    koetterBasisSpanContains basis
      (CBivariate.ofYConstant weight * basis.getD idx 0) := by
  refine ⟨fun j ↦ if j == idx then weight else 0, ?_⟩
  exact koetterBasisCombination_single_weight basis hidx weight

theorem koetterBasisCombination_congr_weights
    {basis : Array (CBivariate F)} {weights₁ weights₂ : Nat → CPolynomial F}
    (hweights : ∀ idx, idx < basis.size → weights₁ idx = weights₂ idx) :
    koetterBasisCombination weights₁ basis =
      koetterBasisCombination weights₂ basis := by
  unfold koetterBasisCombination
  apply foldl_add_congr_terms
  intro idx hidx
  rw [hweights idx (List.mem_range.mp hidx)]

omit [Nontrivial F] [DecidableEq F] in
theorem ofCoeffRow_toCoeffRow_eq_of_width_le
    {width : Nat} {Q : CBivariate F}
    (hY : ∀ i j, width ≤ j → CBivariate.coeff Q i j = 0) :
    CBivariate.ofCoeffRow (CBivariate.toCoeffRow width Q) = Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  by_cases hj : j < width
  · rw [CBivariate.coeff_ofCoeffRow_of_lt
      (row := CBivariate.toCoeffRow width Q)
      (i := i) (j := j) (by simpa [CBivariate.toCoeffRow_size] using hj)]
    simp [CBivariate.toCoeffRow, CBivariate.coeff, Array.getD_eq_getD_getElem?, hj]
  · rw [CBivariate.coeff_ofCoeffRow_of_size_le
      (row := CBivariate.toCoeffRow width Q)
      (i := i) (j := j) (by simpa [CBivariate.toCoeffRow_size] using Nat.le_of_not_gt hj)]
    exact (hY i j (Nat.le_of_not_gt hj)).symm

theorem ofCoeffRow_lee_rowSpan_of_spanContains
    (R G : CPolynomial F) (params : GSInterpParams) {Q : CBivariate F}
    (hspan :
      koetterBasisSpanContains
        (leeOSullivanBasisPolynomials (F := F) R G params) Q) :
    ∃ row,
      row ∈ RowSpan (leeOSullivanBasisRowsWithRG R G params) ∧
        CBivariate.ofCoeffRow row = Q := by
  rcases hspan with ⟨weights, hweights⟩
  let coeffs : Array (CPolynomial F) :=
    (List.range (leeOSullivanWidth params)).map (fun idx ↦ weights idx) |>.toArray
  refine ⟨rowLinearCombination coeffs (leeOSullivanBasisRowsWithRG R G params), ?_, ?_⟩
  · refine ⟨coeffs, ?_, rfl⟩
    simp [coeffs, leeOSullivanBasisRowsWithRG]
  · rw [ofCoeffRow_rowLinearCombination_lee_eq_combination]
    rw [← hweights]
    apply koetterBasisCombination_congr_weights
    intro idx hidx
    have hidxWidth : idx < leeOSullivanWidth params := by
      simpa [leeOSullivanBasisPolynomials_size] using hidx
    simp [coeffs, Array.getD_eq_getD_getElem?, hidxWidth]

omit [Nontrivial F] [DecidableEq F] in
private theorem cpoly_C_one_mul
    (P : CPolynomial F) :
    CPolynomial.C (1 : F) * P = P := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly (CPolynomial.C (1 : F) * P) i,
    CPolynomial.coeff_toPoly P i]
  rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
  simp

omit [Nontrivial F] [DecidableEq F] in
private theorem cpoly_C_zero_mul
    (P : CPolynomial F) :
    CPolynomial.C (0 : F) * P = 0 := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly (CPolynomial.C (0 : F) * P) i,
    CPolynomial.coeff_toPoly (0 : CPolynomial F) i]
  rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.toPoly_zero]
  simp

private def semanticUnitRowCoeffs
    (height i : Nat) : Array (CPolynomial F) :=
  Array.ofFn (fun j : Fin height ↦
    if j.val = i then CPolynomial.C (1 : F) else CPolynomial.C (0 : F))

omit [Nontrivial F] [DecidableEq F] in
private theorem semanticUnitRowCoeffs_size
    (height i : Nat) :
    (semanticUnitRowCoeffs (F := F) height i).size = height := by
  simp [semanticUnitRowCoeffs]

omit [Nontrivial F] [DecidableEq F] in
private theorem semanticUnitRowCoeffs_getD_self
    {height i : Nat} (hi : i < height) :
    (semanticUnitRowCoeffs (F := F) height i).getD i 0 =
      CPolynomial.C (1 : F) := by
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simp [semanticUnitRowCoeffs]
  · simpa [semanticUnitRowCoeffs_size] using hi

omit [Nontrivial F] [DecidableEq F] in
private theorem semanticUnitRowCoeffs_getD_ne
    {height i k : Nat} (hne : k ≠ i) :
    (semanticUnitRowCoeffs (F := F) height i).getD k 0 =
      CPolynomial.C (0 : F) := by
  by_cases hk : k < height
  · rw [Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem]
    · simp [semanticUnitRowCoeffs, hne]
    · simpa [semanticUnitRowCoeffs_size] using hk
  · have hle : (semanticUnitRowCoeffs (F := F) height i).size ≤ k := by
      simpa [semanticUnitRowCoeffs_size] using Nat.le_of_not_gt hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp

omit [Nontrivial F] [DecidableEq F] in
theorem coeff_ofCoeffRow_rowGet
    (row : PolynomialRow F) (i j : Nat) :
    CBivariate.coeff (CBivariate.ofCoeffRow row) i j =
      CPolynomial.coeff (rowGet row j) i := by
  rw [CBivariate.ofCoeffRow, CBivariate.coeff]
  unfold CPolynomial.ofArray CPolynomial.coeff rowGet
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]

omit [Nontrivial F] [DecidableEq F] in
theorem ofCoeffRow_rowLinearCombination_unit
    (M : PolynomialMatrix F) {i : Nat} (hi : i < M.size) :
    CBivariate.ofCoeffRow
        (rowLinearCombination (semanticUnitRowCoeffs (F := F) M.size i) M) =
      CBivariate.ofCoeffRow (M.getD i #[]) := by
  apply (CBivariate.eq_iff_coeff).mpr
  intro x j
  rw [coeff_ofCoeffRow_rowGet, coeff_ofCoeffRow_rowGet]
  rw [rowGet_rowLinearCombination_coeff]
  trans
    (((semanticUnitRowCoeffs (F := F) M.size i).getD i 0 *
      rowGet (M.getD i #[]) j).coeff x)
  · apply Finset.sum_eq_single (s := Finset.range M.size)
      (f := fun idx ↦
        (((semanticUnitRowCoeffs (F := F) M.size i).getD idx 0 *
          rowGet (M.getD idx #[]) j).coeff x)) i
    · intro idx _hidx hidxNe
      rw [semanticUnitRowCoeffs_getD_ne (F := F) hidxNe]
      rw [cpoly_C_zero_mul, CPolynomial.coeff_zero]
    · intro hnot
      rw [semanticUnitRowCoeffs_getD_self (F := F) hi]
      rw [cpoly_C_one_mul]
      exact False.elim (hnot (Finset.mem_range.mpr hi))
  · rw [semanticUnitRowCoeffs_getD_self (F := F) hi]
    rw [cpoly_C_one_mul]

omit [Nontrivial F] [DecidableEq F] in
theorem ofCoeffRow_matrix_getD_semantic_rowSpan
    (M : PolynomialMatrix F) {i : Nat} (hi : i < M.size) :
    ∃ spanRow,
      spanRow ∈ RowSpan M ∧
        CBivariate.ofCoeffRow spanRow =
          CBivariate.ofCoeffRow (M.getD i #[]) := by
  refine ⟨rowLinearCombination (semanticUnitRowCoeffs (F := F) M.size i) M,
    ?_, ofCoeffRow_rowLinearCombination_unit M hi⟩
  exact ⟨semanticUnitRowCoeffs (F := F) M.size i,
    semanticUnitRowCoeffs_size M.size i, rfl⟩

omit [DecidableEq F] in
theorem ofCoeffRow_eq_zero_of_rowShiftedDegree?_none
    {row : PolynomialRow F} {shift : Array Nat}
    (hdeg : rowShiftedDegree? row shift = none) :
    CBivariate.ofCoeffRow row = 0 := by
  have hzero : RowIsZero row :=
    (rowShiftedDegree?_eq_none_iff (row := row) (shift := shift)).1 hdeg
  rw [CBivariate.eq_iff_coeff]
  intro i j
  by_cases hj : j < row.size
  · rw [CBivariate.coeff_ofCoeffRow_of_lt row (i := i) (j := j) hj]
    have hentry : row.getD j 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
      exact hzero row[j] (by
        simpa only [Array.mem_def] using Array.getElem_mem_toList hj)
    rw [hentry, CPolynomial.coeff_zero, CBivariate.coeff_zero]
  · rw [CBivariate.coeff_ofCoeffRow_of_size_le row
      (i := i) (j := j) (Nat.le_of_not_gt hj), CBivariate.coeff_zero]

theorem rowSpan_lee_row_size
    (R G : CPolynomial F) (params : GSInterpParams) {row : PolynomialRow F}
    (hrow : row ∈ RowSpan (leeOSullivanBasisRowsWithRG R G params)) :
    row.size = leeOSullivanWidth params := by
  rcases hrow with ⟨coeffs, _hcoeffs, hrowEq⟩
  rw [hrowEq]
  rw [rowLinearCombination_size
    (M := leeOSullivanBasisRowsWithRG R G params)
    (leeOSullivanBasisRowsWithRG_wellFormed R G params)]
  exact leeOSullivanBasisRowsWithRG_width R G params

theorem ofCoeffRow_rowSpan_lee_coeff_eq_zero_of_width_le
    (R G : CPolynomial F) (params : GSInterpParams) {row : PolynomialRow F}
    (hrow : row ∈ RowSpan (leeOSullivanBasisRowsWithRG R G params))
    {i j : Nat} (hj : leeOSullivanWidth params ≤ j) :
    CBivariate.coeff (CBivariate.ofCoeffRow row) i j = 0 := by
  have hsize := rowSpan_lee_row_size R G params hrow
  exact CBivariate.coeff_ofCoeffRow_of_size_le row
    (i := i) (j := j) (by simpa [hsize] using hj)

omit [Nontrivial F] [DecidableEq F] in
theorem natWeightedDegree_ofCoeffRow_le_of_lee_rowShiftedDegree?_le
    (params : GSInterpParams) (row : PolynomialRow F) {degree : Nat}
    (hdeg : rowShiftedDegree? row (leeOSullivanShifts params) = some degree)
    (hle : degree ≤ params.weightedDegreeBound)
    (hYBound :
      ∀ i j, leeOSullivanWidth params ≤ j →
        CBivariate.coeff (CBivariate.ofCoeffRow row) i j = 0) :
    CBivariate.natWeightedDegree (CBivariate.ofCoeffRow row) 1 (yWeight params) ≤
      params.weightedDegreeBound := by
  rw [CBivariate.natWeightedDegree_le_iff_coeff]
  intro i j hcoeff
  have hjRow : j < row.size := by
    by_contra hnot
    have hzero := CBivariate.coeff_ofCoeffRow_of_size_le row
      (i := i) (j := j) (Nat.le_of_not_gt hnot)
    exact hcoeff hzero
  have hrowCoeff :
      CPolynomial.coeff (rowGet row j) i ≠ 0 := by
    rwa [coeff_ofCoeffRow_rowGet] at hcoeff
  have hrowNe : rowGet row j ≠ 0 := by
    intro hzero
    rw [hzero, CPolynomial.coeff_zero] at hrowCoeff
    exact hrowCoeff rfl
  have hentry :
      shiftedEntryDegree? row (leeOSullivanShifts params) j =
        some ((rowGet row j).natDegree +
          (leeOSullivanShifts params).getD j 0) := by
    have hrowNe' : row[j]?.getD 0 ≠ 0 := by
      simpa [rowGet, Array.getD_eq_getD_getElem?] using hrowNe
    simp [shiftedEntryDegree?, hrowNe', rowGet, Array.getD_eq_getD_getElem?]
  have hentryLe :=
    shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hdeg hjRow hentry
  have hjWidth : j < leeOSullivanWidth params := by
    by_contra hnot
    exact hcoeff (hYBound i j (Nat.le_of_not_gt hnot))
  have hshift :
      (leeOSullivanShifts params).getD j 0 = j * yWeight params := by
    simp [leeOSullivanShifts, CBivariate.weightedDegreeShift,
      Array.getD_eq_getD_getElem?, hjWidth]
  rw [hshift, Nat.mul_comm j (yWeight params)] at hentryLe
  have hiLe : i ≤ (rowGet row j).natDegree :=
    CPolynomial.le_natDegree_of_ne_zero hrowCoeff
  omega

omit [DecidableEq F] in
theorem ofCoeffRow_ne_zero_of_rowShiftedDegree?_some
    {row : PolynomialRow F} {shift : Array Nat} {degree : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree) :
    CBivariate.ofCoeffRow row ≠ 0 := by
  have hnotZero : ¬ RowIsZero row := by
    intro hzero
    have hnone : rowShiftedDegree? row shift = none :=
      (rowShiftedDegree?_eq_none_iff (row := row) (shift := shift)).2 hzero
    rw [hdeg] at hnone
    contradiction
  rw [RowIsZero] at hnotZero
  push Not at hnotZero
  rcases hnotZero with ⟨p, hp, hpne⟩
  rcases List.getElem_of_mem hp with ⟨j, hj, hget⟩
  have hrowGetNe : rowGet row j ≠ 0 := by
    have hrowGet : rowGet row j = p := by
      unfold rowGet
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)]
      simpa [Array.getElem_toList] using hget
    simpa [hrowGet] using hpne
  intro hzero
  apply hrowGetNe
  apply (CPolynomial.eq_iff_coeff).mpr
  intro i
  have hcoeff :
      CBivariate.coeff (CBivariate.ofCoeffRow row) i j = 0 := by
    rw [hzero, CBivariate.coeff_zero]
  rw [CBivariate.coeff_ofCoeffRow_of_lt row (by simpa using hj)] at hcoeff
  exact hcoeff


/-- A `Y`-constant linear combination of basis entries satisfying a pointwise
multiplicity constraint satisfies that constraint. -/
theorem hasMultiplicityAtLeast_koetterBasisCombination
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F))
    {x y : F} {m : Nat}
    (hbasis :
      ∀ idx, idx < basis.size →
        CBivariate.HasMultiplicityAtLeast (basis.getD idx 0) x y m) :
    CBivariate.HasMultiplicityAtLeast
      (koetterBasisCombination weights basis) x y m := by
  intro a b hab
  unfold koetterBasisCombination
  let step : CBivariate F → Nat → CBivariate F :=
    fun out idx ↦ out + CBivariate.ofYConstant (weights idx) * basis.getD idx 0
  have hfoldAcc :
      ∀ xs : List Nat, ∀ acc : CBivariate F,
        CBivariate.hasseDerivativeEval a b x y acc = 0 →
        (∀ idx, idx ∈ xs → idx < basis.size) →
          CBivariate.hasseDerivativeEval a b x y
              (xs.foldl step acc) = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc _hidx
        exact hacc
    | cons idx xs ih =>
        intro acc hacc hidx
        simp only [List.foldl_cons]
        apply ih
        · change CBivariate.hasseDerivativeEval a b x y
            (acc + CBivariate.ofYConstant (weights idx) * basis.getD idx 0) = 0
          rw [CBivariate.hasseDerivativeEval_add, hacc]
          have hterm :=
            hasMultiplicityAtLeast_ofYConstant_mul (weights idx)
              (hbasis idx (hidx idx (by simp)))
          rw [hterm a b hab]
          simp
        · intro j hj
          exact hidx j (by simp [hj])
  exact hfoldAcc (List.range basis.size) 0
    (CBivariate.hasseDerivativeEval_zero a b x y)
    (fun idx hmem ↦ List.mem_range.mp hmem)

/-- A `Y`-constant linear combination of basis entries satisfying all packed
multiplicity constraints satisfies the same packed constraints. -/
theorem koetterBasisCombination_satisfiesMultiplicityConstraints
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F))
    {points : Array (F × F)} {m : Nat}
    (hbasis :
      ∀ idx, idx < basis.size →
        CBivariate.SatisfiesMultiplicityConstraints
          (basis.getD idx 0) points m) :
    CBivariate.SatisfiesMultiplicityConstraints
      (koetterBasisCombination weights basis) points m := by
  intro point hpoint
  exact hasMultiplicityAtLeast_koetterBasisCombination weights basis
    (fun idx hidx ↦ hbasis idx hidx point hpoint)

/-- Any executable row in the Lee row span represents a bivariate polynomial
satisfying the packed multiplicity constraints, provided every Lee basis entry
does. -/
theorem ofCoeffRow_rowSpan_lee_satisfiesMultiplicityConstraints
    (R G : CPolynomial F) (params : GSInterpParams)
    {points : Array (F × F)} {row : PolynomialRow F}
    (hbasis :
      ∀ idx, idx < (leeOSullivanBasisPolynomials (F := F) R G params).size →
        CBivariate.SatisfiesMultiplicityConstraints
          ((leeOSullivanBasisPolynomials (F := F) R G params).getD idx 0)
          points params.multiplicity)
    (hrow : row ∈ RowSpan (leeOSullivanBasisRowsWithRG R G params)) :
    CBivariate.SatisfiesMultiplicityConstraints
      (CBivariate.ofCoeffRow row) points params.multiplicity := by
  rcases ofCoeffRow_rowSpan_lee_spanContains R G params hrow with
    ⟨weights, hweights⟩
  rw [← hweights]
  exact koetterBasisCombination_satisfiesMultiplicityConstraints
    weights (leeOSullivanBasisPolynomials (F := F) R G params) hbasis

end LeeOSullivan

end GuruswamiSudan

end CompPoly
