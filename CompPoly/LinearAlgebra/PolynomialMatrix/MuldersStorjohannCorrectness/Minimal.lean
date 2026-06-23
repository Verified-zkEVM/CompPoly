/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Reduction

/-!
# Mulders-Storjohann Correctness Reducer Minimality

Least-row minimality and the certified reducer context.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem muldersStorjohannReduce_least_row_minimal
    (M : PolynomialMatrix F) (shift : Array Nat) (row : PolynomialRow F)
    (hM : WellFormed M) (hshift : shift.size = MatrixWidth M)
    (hrow : row ∈ RowSpan M)
    (hdeg : rowShiftedDegree? row shift ≠ none) :
    ∃ outRow outDeg rowDeg,
      outRow ∈ MatrixRows (muldersStorjohannReduce M shift) ∧
      rowShiftedDegree? outRow shift = some outDeg ∧
      rowShiftedDegree? row shift = some rowDeg ∧
      outDeg ≤ rowDeg := by
  let R := muldersStorjohannReduce M shift
  have hRwf : WellFormed R := muldersStorjohannReduce_wellFormed M shift hM
  have hwp : ShiftedWeakPopov R shift :=
    muldersStorjohannReduce_weakPopov M shift hM hshift
  have hspan : RowSpan R = RowSpan M :=
    muldersStorjohannReduce_rowSpan_eq M shift hM
  have hrowR : row ∈ RowSpan R := by
    rwa [hspan]
  rcases hrowR with ⟨coeffs, _hcoeffsSize, hrowEq⟩
  subst row
  cases hrowDeg : rowShiftedDegree? (rowLinearCombination coeffs R) shift with
  | none =>
      exact False.elim (hdeg hrowDeg)
  | some rowDeg =>
      let S := rowCombinationTermSupport coeffs R shift
      have hS : S.Nonempty :=
        rowCombinationTermSupport_nonempty_of_combination_degree_some
          hRwf hrowDeg
      obtain ⟨imax, himaxS, hmaxDegree⟩ :=
        Finset.exists_max_image S
          (rowCombinationTermDegree coeffs R shift) hS
      let D := rowCombinationTermDegree coeffs R shift imax
      let T := S.filter fun i ↦ rowCombinationTermDegree coeffs R shift i = D
      have hT : T.Nonempty := by
        refine ⟨imax, ?_⟩
        exact Finset.mem_filter.mpr ⟨himaxS, rfl⟩
      obtain ⟨i, hiT, hmaxPos⟩ :=
        Finset.exists_max_image T (rowCombinationTermPosition R shift) hT
      have hiS : i ∈ S := (Finset.mem_filter.mp hiT).1
      have hiDegreeEq :
          rowCombinationTermDegree coeffs R shift i = D :=
        (Finset.mem_filter.mp hiT).2
      rcases (Finset.mem_filter.mp hiS) with
        ⟨hiRange, hcoeffI, hrowDegI_ne⟩
      have hi : i < R.size := Finset.mem_range.mp hiRange
      cases hrowDegI : rowShiftedDegree? (R.getD i #[]) shift with
      | none =>
          exact False.elim (hrowDegI_ne hrowDegI)
      | some outDeg =>
          rcases rowShiftedLeadingPosition?_some_of_degree hrowDegI with
            ⟨posI, hposI⟩
          have hposIRow : posI < (R.getD i #[]).size :=
            rowShiftedLeadingPosition?_lt hposI
          have hposIWidth : posI < MatrixWidth R := by
            rw [matrix_getD_size_of_wellFormed hRwf hi] at hposIRow
            exact hposIRow
          have hentryIData :=
            shiftedEntryDegree?_eq_some_iff_data.1
              (rowShiftedLeadingPosition?_entry_eq hrowDegI hposI)
          rcases hentryIData with ⟨hentryINe, hentryIShift⟩
          let coeffI := coeffs.getD i 0
          let entryI := rowGet (R.getD i #[]) posI
          let k := coeffI.natDegree + entryI.natDegree
          have hdegreeI_expr :
              rowCombinationTermDegree coeffs R shift i =
                coeffI.natDegree + outDeg := by
            unfold rowCombinationTermDegree coeffI
            rw [hrowDegI]
          have hD_eq : D = k + shift.getD posI 0 := by
            rw [← hiDegreeEq, hdegreeI_expr, ← hentryIShift]
            unfold k entryI
            omega
          have hselectedCoeffNe :
              (coeffs.getD i 0 * rowGet (R.getD i #[]) posI).coeff k ≠ 0 := by
            simpa [coeffI, entryI, k] using
              cpoly_coeff_mul_natDegree_add_ne_zero
                (P := coeffI) (Q := entryI) hcoeffI hentryINe
          have hotherCoeffZero :
              ∀ l, l < R.size → l ≠ i →
                (coeffs.getD l 0 * rowGet (R.getD l #[]) posI).coeff k = 0 := by
            intro l hl hli
            by_contra hcoeffAtK
            let coeffL := coeffs.getD l 0
            let entryL := rowGet (R.getD l #[]) posI
            have hprodNonzero : coeffL * entryL ≠ 0 := by
              intro hprodZero
              exact hcoeffAtK (by
                have hprodZero' :
                    coeffs.getD l 0 * rowGet (R.getD l #[]) posI = 0 := by
                  simpa [coeffL, entryL] using hprodZero
                rw [hprodZero']
                exact CPolynomial.coeff_zero k)
            have hcoeffL : coeffL ≠ 0 := by
              intro hzero
              exact hprodNonzero (by simp [coeffL, hzero])
            have hentryL : entryL ≠ 0 := by
              intro hzero
              exact hprodNonzero (by simp [entryL, hzero])
            have hposIRowL : posI < (R.getD l #[]).size := by
              rw [matrix_getD_size_of_wellFormed hRwf hl]
              exact hposIWidth
            have hrowDegL_ne :
                rowShiftedDegree? (R.getD l #[]) shift ≠ none := by
              intro hnone
              have hrowZero :=
                (rowShiftedDegree?_eq_none_iff
                  (row := R.getD l #[]) (shift := shift)).1 hnone
              have hentryZero : rowGet (R.getD l #[]) posI = 0 := by
                unfold rowGet
                rw [Array.getD_eq_getD_getElem?,
                  Array.getElem?_eq_getElem hposIRowL]
                exact hrowZero (R.getD l #[])[posI]
                  (by simpa only [Array.mem_def] using
                    Array.getElem_mem_toList hposIRowL)
              exact hentryL (by simpa [entryL] using hentryZero)
            have hlS : l ∈ S :=
              Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hl, hcoeffL, hrowDegL_ne⟩
            cases hrowDegL : rowShiftedDegree? (R.getD l #[]) shift with
            | none =>
                exact hrowDegL_ne hrowDegL
            | some outDegL =>
                rcases rowShiftedLeadingPosition?_some_of_degree hrowDegL with
                  ⟨posL, hposL⟩
                have hdegreeL_le_D :
                    rowCombinationTermDegree coeffs R shift l ≤ D := by
                  simpa [D] using hmaxDegree l hlS
                have hk_le_prod :
                    k ≤ (coeffL * entryL).natDegree :=
                  CPolynomial.le_natDegree_of_ne_zero hcoeffAtK
                have hprodDeg_le :
                    (coeffL * entryL).natDegree ≤
                      coeffL.natDegree + entryL.natDegree :=
                  cpoly_natDegree_mul_le coeffL entryL
                have hentryBound :
                    entryL.natDegree + shift.getD posI 0 ≤ outDegL := by
                  exact rowShiftedDegree?_entry_bound hrowDegL
                    hposIRowL (by simpa [entryL] using hentryL)
                have hD_le_degreeL : D ≤ coeffL.natDegree + outDegL := by
                  rw [hD_eq]
                  omega
                have hdegreeL_eq_D : coeffL.natDegree + outDegL = D := by
                  have hdegreeL_expr :
                      rowCombinationTermDegree coeffs R shift l =
                        coeffL.natDegree + outDegL := by
                    unfold rowCombinationTermDegree coeffL
                    rw [hrowDegL]
                  have hle : coeffL.natDegree + outDegL ≤ D := by
                    simpa [hdegreeL_expr] using hdegreeL_le_D
                  exact le_antisymm hle hD_le_degreeL
                have hD_le_entry :
                    D ≤ coeffL.natDegree +
                      (entryL.natDegree + shift.getD posI 0) := by
                  rw [hD_eq]
                  omega
                have hentryShiftEq :
                    entryL.natDegree + shift.getD posI 0 = outDegL := by
                  omega
                have hentryShiftL :
                    shiftedEntryDegree? (R.getD l #[]) shift posI =
                      some outDegL := by
                  have hsome :=
                    shiftedEntryDegree?_eq_some_of_rowGet_ne_zero
                      (row := R.getD l #[]) (shift := shift) (j := posI)
                      (by simpa [entryL] using hentryL)
                  have hentryShiftEq' :
                      (rowGet (R.getD l #[]) posI).natDegree +
                          shift.getD posI 0 = outDegL := by
                    simpa [entryL] using hentryShiftEq
                  rw [hentryShiftEq'] at hsome
                  exact hsome
                have hposI_le_posL : posI ≤ posL :=
                  rowShiftedLeadingPosition?_le_of_entry_eq_degree
                    hrowDegL hposL hposIRowL hentryShiftL
                have hlDegreeEq :
                    rowCombinationTermDegree coeffs R shift l = D := by
                  have hdegreeL_expr :
                      rowCombinationTermDegree coeffs R shift l =
                        coeffL.natDegree + outDegL := by
                    unfold rowCombinationTermDegree coeffL
                    rw [hrowDegL]
                  rw [hdegreeL_expr, hdegreeL_eq_D]
                have hlT : l ∈ T :=
                  Finset.mem_filter.mpr ⟨hlS, hlDegreeEq⟩
                have hposL_le_posI : posL ≤ posI := by
                  have hle := hmaxPos l hlT
                  have hposLval :
                      rowCombinationTermPosition R shift l = posL := by
                    unfold rowCombinationTermPosition
                    rw [hposL]
                    rfl
                  have hposIval :
                      rowCombinationTermPosition R shift i = posI := by
                    unfold rowCombinationTermPosition
                    rw [hposI]
                    rfl
                  rwa [hposLval, hposIval] at hle
                have hposEq : posL = posI :=
                  le_antisymm hposL_le_posI hposI_le_posL
                have hposNe :=
                  hwp l i hl hi hli
                    (by rw [hposL]; simp)
                    (by rw [hposI]; simp)
                exact hposNe (by rw [hposL, hposI, hposEq])
          have hcomboCoeffNe :
              (rowGet (rowLinearCombination coeffs R) posI).coeff k ≠ 0 := by
            rw [rowGet_rowLinearCombination_coeff]
            rw [Finset.sum_eq_single i]
            · exact hselectedCoeffNe
            · intro l hlRange hli
              exact hotherCoeffZero l (Finset.mem_range.mp hlRange) hli
            · intro hiNot
              exact False.elim (hiNot (Finset.mem_range.mpr hi))
          have hcomboEntryNe :
              rowGet (rowLinearCombination coeffs R) posI ≠ 0 := by
            intro hzero
            exact hcomboCoeffNe (by
              rw [hzero]
              exact CPolynomial.coeff_zero k)
          have hcomboPos : posI < (rowLinearCombination coeffs R).size := by
            simpa [rowLinearCombination_size hRwf coeffs] using hposIWidth
          have hcomboEntryBound :
              (rowGet (rowLinearCombination coeffs R) posI).natDegree +
                  shift.getD posI 0 ≤ rowDeg :=
            rowShiftedDegree?_entry_bound hrowDeg hcomboPos hcomboEntryNe
          have hk_le_combo :
              k ≤ (rowGet (rowLinearCombination coeffs R) posI).natDegree :=
            CPolynomial.le_natDegree_of_ne_zero hcomboCoeffNe
          have hD_le_rowDeg : D ≤ rowDeg := by
            rw [hD_eq]
            exact le_trans (Nat.add_le_add_right hk_le_combo _)
              hcomboEntryBound
          have houtDeg_le_D : outDeg ≤ D := by
            rw [← hiDegreeEq, hdegreeI_expr]
            omega
          refine ⟨R.getD i #[], outDeg, rowDeg, ?_, hrowDegI, rfl, ?_⟩
          · rw [MatrixRows]
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
            exact Array.getElem_mem_toList hi
          · exact le_trans houtDeg_le_D hD_le_rowDeg

/-- Certified direct Mulders-Storjohann shifted row-reducer context. -/
def muldersStorjohannReducerContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] : ShiftedRowReducerContext F where
  reduce := muldersStorjohannReduce
  shape_preserved := by
    intro M shift hM
    exact muldersStorjohannReduce_shape_preserved M shift hM
  rowSpan_eq := by
    intro M shift hM
    exact muldersStorjohannReduce_rowSpan_eq M shift hM
  weakPopov := by
    intro M shift hM hshift
    exact muldersStorjohannReduce_weakPopov M shift hM hshift
  least_row_minimal := by
    intro M shift row hM hshift hrow hdeg
    exact muldersStorjohannReduce_least_row_minimal M shift row hM hshift hrow hdeg

end PolynomialMatrix

end CompPoly
