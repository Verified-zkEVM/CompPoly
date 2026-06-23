/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Combinations

/-!
# Mulders-Storjohann Correctness Reduction Invariants

Shape, well-formedness, row-span, and weak-Popov correctness for the reducer.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem muldersStorjohannStep_shape_preserved
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    MatrixShape (muldersStorjohannStep M shift i j) = MatrixShape M := by
  simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
  cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      simp
  | some degI =>
      cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
      | none =>
          simp
      | some degJ =>
          simp only
          have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
          have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
          split
          · apply replaceRow_shape
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
          · apply replaceRow_shape
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift

theorem muldersStorjohannStep_rowSpan_subset
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    RowSpan (muldersStorjohannStep M shift i j) ⊆ RowSpan M := by
  apply rowSpan_subset_of_rows_mem hM
  · exact congrArg PolynomialMatrixShape.width
      (muldersStorjohannStep_shape_preserved shift hM)
  · intro row hrow
    simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?] at hrow
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        exact matrix_row_mem_rowSpan hM (by simpa [hI] using hrow)
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            exact matrix_row_mem_rowSpan hM (by simpa [hI, hJ] using hrow)
        | some degJ =>
            have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
            have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
            have hrowI : (M[i]?.getD #[]) ∈ RowSpan M := by
              have hget : M[i]?.getD #[] = M[i] := by
                simp [Array.getElem?_eq_getElem hi]
              rw [hget]
              exact matrix_row_mem_rowSpan hM
                (by simp [MatrixRows, Array.getElem_mem_toList hi])
            have hrowJ : (M[j]?.getD #[]) ∈ RowSpan M := by
              have hget : M[j]?.getD #[] = M[j] := by
                simp [Array.getElem?_eq_getElem hj]
              rw [hget]
              exact matrix_row_mem_rowSpan hM
                (by simp [MatrixRows, Array.getElem_mem_toList hj])
            simp [hI, hJ] at hrow
            split at hrow
            · exact replaceRow_rows_mem_rowSpan hM
                (cancelShiftedLeadingTerm_mem_rowSpan hrowJ hrowI) hrow
            · exact replaceRow_rows_mem_rowSpan hM
                (cancelShiftedLeadingTerm_mem_rowSpan hrowI hrowJ) hrow

theorem muldersStorjohannStep_rowSpan_superset
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat}
    (hM : WellFormed M) (hi : i < M.size) (hj : j < M.size) (hne : i ≠ j) :
    RowSpan M ⊆ RowSpan (muldersStorjohannStep M shift i j) := by
  apply rowSpan_subset_of_rows_mem
  · simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        simpa [hI] using hM
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            simpa [hI, hJ] using hM
        | some degJ =>
            simp only
            split
            · apply replaceRow_wellFormed hM
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
            · apply replaceRow_wellFormed hM
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift
  · exact (congrArg PolynomialMatrixShape.width
      (muldersStorjohannStep_shape_preserved shift hM)).symm
  · intro row hrow
    rcases List.getElem_of_mem hrow with ⟨k, hk, hget⟩
    have hkM : k < M.size := by
      simpa [MatrixRows] using hk
    have hrow_eq : M[k] = row := by
      simpa [MatrixRows, Array.getElem_toList] using hget
    rw [← hrow_eq]
    simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        exact matrix_row_mem_rowSpan hM
          (by simp [MatrixRows, Array.getElem_mem_toList hkM])
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            exact matrix_row_mem_rowSpan hM
              (by simp [MatrixRows, Array.getElem_mem_toList hkM])
        | some degJ =>
            have hcancelJ_size :
                (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift).size =
                  MatrixWidth M := by
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
            have hreplaceJ_wf :
                WellFormed
                  (replaceRow M j
                    (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) :=
              replaceRow_wellFormed hM hcancelJ_size
            have hcancelI_size :
                (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift).size =
                  MatrixWidth M := by
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift
            have hreplaceI_wf :
                WellFormed
                  (replaceRow M i
                    (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) :=
              replaceRow_wellFormed hM hcancelI_size
            have hrowI : (M[i]?.getD #[]) ∈
                RowSpan
                  (replaceRow M j
                    (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) := by
              have hgetI : M[i]?.getD #[] = M[i] := by
                simp [Array.getElem?_eq_getElem hi]
              exact matrix_row_mem_rowSpan hreplaceJ_wf
                (by simpa [hgetI] using replaceRow_oldRow_mem hi (by exact hne.symm))
            have hrowJ : (M[j]?.getD #[]) ∈
                RowSpan
                  (replaceRow M i
                    (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) := by
              have hgetJ : M[j]?.getD #[] = M[j] := by
                simp [Array.getElem?_eq_getElem hj]
              exact matrix_row_mem_rowSpan hreplaceI_wf
                (by simpa [hgetJ] using replaceRow_oldRow_mem hj hne)
            by_cases hdeg : degI ≤ degJ
            · simp only [hdeg, if_true]
              by_cases hkj : k = j
              · subst k
                have hcancel : cancelShiftedLeadingTerm (M[j]?.getD #[])
                    (M[i]?.getD #[]) shift ∈
                    RowSpan
                      (replaceRow M j
                        (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) := by
                  exact matrix_row_mem_rowSpan hreplaceJ_wf (replaceRow_newRow_mem hj)
                have hsize : (M[i]?.getD #[]).size = (M[j]?.getD #[]).size := by
                  rw [matrix_getElem?_getD_size_of_wellFormed hM hi,
                    matrix_getElem?_getD_size_of_wellFormed hM hj]
                have htarget : (M[j]?.getD #[]) ∈
                    RowSpan
                      (replaceRow M j
                        (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) :=
                  cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hrowI hsize
                simpa [Array.getElem?_eq_getElem hj] using htarget
              · have hne' : j ≠ k := fun h ↦ hkj h.symm
                exact matrix_row_mem_rowSpan hreplaceJ_wf (replaceRow_oldRow_mem hkM hne')
            · simp only [hdeg, if_false]
              by_cases hki : k = i
              · subst k
                have hcancel : cancelShiftedLeadingTerm (M[i]?.getD #[])
                    (M[j]?.getD #[]) shift ∈
                    RowSpan
                      (replaceRow M i
                        (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) := by
                  exact matrix_row_mem_rowSpan hreplaceI_wf (replaceRow_newRow_mem hi)
                have hsize : (M[j]?.getD #[]).size = (M[i]?.getD #[]).size := by
                  rw [matrix_getElem?_getD_size_of_wellFormed hM hj,
                    matrix_getElem?_getD_size_of_wellFormed hM hi]
                have htarget : (M[i]?.getD #[]) ∈
                    RowSpan
                      (replaceRow M i
                        (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) :=
                  cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hrowJ hsize
                simpa [Array.getElem?_eq_getElem hi] using htarget
              · have hne' : i ≠ k := fun h ↦ hki h.symm
                exact matrix_row_mem_rowSpan hreplaceI_wf (replaceRow_oldRow_mem hkM hne')

theorem muldersStorjohannStep_wellFormed
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    WellFormed (muldersStorjohannStep M shift i j) := by
  simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
  cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      simpa [hI] using hM
  | some degI =>
      cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
      | none =>
          simpa [hI, hJ] using hM
      | some degJ =>
          simp only
          have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
          have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
          split
          · apply replaceRow_wellFormed hM
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
          · apply replaceRow_wellFormed hM
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift

theorem muldersStorjohannReduceWithFuel_shape_preserved
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    MatrixShape (muldersStorjohannReduceWithFuel fuel M shift) = MatrixShape M := by
  induction fuel generalizing M with
  | zero =>
      simp [muldersStorjohannReduceWithFuel]
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · rfl
      · rename_i _ i j hconf
        exact (ih (muldersStorjohannStep M shift i j)
          (muldersStorjohannStep_wellFormed shift hM)).trans
          (muldersStorjohannStep_shape_preserved shift hM)

theorem muldersStorjohannReduceWithFuel_wellFormed
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    WellFormed (muldersStorjohannReduceWithFuel fuel M shift) := by
  induction fuel generalizing M with
  | zero =>
      simpa [muldersStorjohannReduceWithFuel] using hM
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · exact hM
      · rename_i _ i j hconf
        exact ih (muldersStorjohannStep M shift i j)
          (muldersStorjohannStep_wellFormed shift hM)

theorem muldersStorjohannReduce_wellFormed
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    WellFormed (muldersStorjohannReduce M shift) := by
  exact muldersStorjohannReduceWithFuel_wellFormed
    (muldersStorjohannFuel M shift) M shift hM

theorem muldersStorjohannReduceWithFuel_no_conflict_of_measure_lt
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M)
    (hfuel : shiftedMatrixMeasure M shift < fuel) :
    shiftedLeadingConflict? (muldersStorjohannReduceWithFuel fuel M shift) shift = none := by
  induction fuel generalizing M with
  | zero =>
      omega
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      cases hconf : shiftedLeadingConflict? M shift with
      | none =>
          simp [hconf]
      | some pair =>
          rcases pair with ⟨i, j⟩
          have hstepLt :=
            muldersStorjohannStep_shiftedMatrixMeasure_lt hM hconf
          have hstepFuel :
              shiftedMatrixMeasure (muldersStorjohannStep M shift i j) shift < fuel := by
            omega
          exact ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM) hstepFuel

theorem muldersStorjohannReduce_no_conflict
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    shiftedLeadingConflict? (muldersStorjohannReduce M shift) shift = none := by
  exact muldersStorjohannReduceWithFuel_no_conflict_of_measure_lt
    (muldersStorjohannFuel M shift) M shift hM
    (shiftedMatrixMeasure_lt_muldersStorjohannFuel hM)

theorem muldersStorjohannReduceWithFuel_rowSpan_subset
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduceWithFuel fuel M shift) ⊆ RowSpan M := by
  induction fuel generalizing M with
  | zero =>
      intro row hrow
      simpa [muldersStorjohannReduceWithFuel] using hrow
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · intro row hrow
        exact hrow
      · rename_i _ i j hconf
        exact Set.Subset.trans
          (ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM))
          (muldersStorjohannStep_rowSpan_subset shift hM)

theorem muldersStorjohannReduce_rowSpan_subset
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduce M shift) ⊆ RowSpan M := by
  exact muldersStorjohannReduceWithFuel_rowSpan_subset
    (muldersStorjohannFuel M shift) M shift hM

theorem muldersStorjohannReduceWithFuel_rowSpan_superset
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan M ⊆ RowSpan (muldersStorjohannReduceWithFuel fuel M shift) := by
  induction fuel generalizing M with
  | zero =>
      intro row hrow
      simpa [muldersStorjohannReduceWithFuel] using hrow
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · intro row hrow
        exact hrow
      · rename_i _ i j hconf
        rcases shiftedLeadingConflict?_some_bounds hconf with ⟨hi, hj, hij⟩
        have hne : i ≠ j := by omega
        exact Set.Subset.trans
          (muldersStorjohannStep_rowSpan_superset shift hM hi hj hne)
          (ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM))

theorem muldersStorjohannReduce_rowSpan_superset
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan M ⊆ RowSpan (muldersStorjohannReduce M shift) := by
  exact muldersStorjohannReduceWithFuel_rowSpan_superset
    (muldersStorjohannFuel M shift) M shift hM

theorem muldersStorjohannReduce_shape_preserved
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    MatrixShape (muldersStorjohannReduce M shift) = MatrixShape M := by
  exact muldersStorjohannReduceWithFuel_shape_preserved
    (muldersStorjohannFuel M shift) M shift hM

theorem muldersStorjohannReduce_rowSpan_eq
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduce M shift) = RowSpan M := by
  apply Set.Subset.antisymm
  · exact muldersStorjohannReduce_rowSpan_subset M shift hM
  · exact muldersStorjohannReduce_rowSpan_superset M shift hM

theorem muldersStorjohannReduce_weakPopov
    (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M) (_hshift : shift.size = MatrixWidth M) :
    ShiftedWeakPopov (muldersStorjohannReduce M shift) shift := by
  exact shiftedLeadingConflict?_none_weakPopov
    (muldersStorjohannReduce_no_conflict M shift hM)

end PolynomialMatrix

end CompPoly
