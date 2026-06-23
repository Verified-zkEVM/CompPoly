/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.RowOps

/-!
# Mulders-Storjohann Correctness Matrix Row Helpers

Replacement-row, matrix-shape, and row-span transport lemmas.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem replaceRow_size (M : PolynomialMatrix F) (idx : Nat) (row : PolynomialRow F) :
    (replaceRow M idx row).size = M.size := by
  simp [replaceRow, Array.size_setIfInBounds]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem replaceRow_matrixWidth
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hrow : row.size = MatrixWidth M) :
    MatrixWidth (replaceRow M idx row) = MatrixWidth M := by
  unfold MatrixWidth replaceRow
  by_cases hM0 : 0 < M.size
  · rw [Array.getElem?_setIfInBounds]
    by_cases hidx : idx = 0
    · subst idx
      simpa [hM0, MatrixWidth] using hrow
    · simp [hidx]
  · have hsize : M.size = 0 := Nat.eq_zero_of_not_pos hM0
    simp [hsize]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem replaceRow_shape
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hrow : row.size = MatrixWidth M) :
    MatrixShape (replaceRow M idx row) = MatrixShape M := by
  simp [MatrixShape, replaceRow_size, replaceRow_matrixWidth hrow]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem replaceRow_wellFormed
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hM : WellFormed M) (hrow : row.size = MatrixWidth M) :
    WellFormed (replaceRow M idx row) := by
  intro stored hstored
  have hwidth : MatrixWidth (replaceRow M idx row) = MatrixWidth M :=
    replaceRow_matrixWidth hrow
  rw [hwidth]
  rcases List.getElem_of_mem hstored with ⟨k, hk, hget⟩
  have hkReplace : k < (replaceRow M idx row).size := by
    simpa [MatrixRows] using hk
  have hkM : k < M.size := by
    simpa [replaceRow_size] using hkReplace
  have hstored_eq : (replaceRow M idx row)[k] = stored := by
    simpa [MatrixRows, Array.getElem_toList] using hget
  rw [← hstored_eq]
  by_cases hidx : k = idx
  · subst idx
    simpa [replaceRow, Array.getElem_setIfInBounds, hkM] using hrow
  · have hmem : M[k] ∈ MatrixRows M := by
      simp [MatrixRows, Array.getElem_mem_toList hkM]
    have hstoredM : M[k].size = MatrixWidth M := hM M[k] hmem
    have hidx' : idx ≠ k := fun h ↦ hidx h.symm
    simpa [replaceRow, Array.getElem_setIfInBounds, hidx', hkM] using hstoredM

theorem replaceRow_rows_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) {idx : Nat} {newRow row : PolynomialRow F}
    (hnew : newRow ∈ RowSpan M)
    (hrow : row ∈ MatrixRows (replaceRow M idx newRow)) :
    row ∈ RowSpan M := by
  rcases List.getElem_of_mem hrow with ⟨k, hk, hget⟩
  have hkReplace : k < (replaceRow M idx newRow).size := by
    simpa [MatrixRows] using hk
  have hkM : k < M.size := by
    simpa [replaceRow_size] using hkReplace
  have hstored_eq : (replaceRow M idx newRow)[k] = row := by
    simpa [MatrixRows, Array.getElem_toList] using hget
  rw [← hstored_eq]
  by_cases hidx : idx = k
  · subst idx
    simpa [replaceRow, Array.getElem_setIfInBounds, hkM] using hnew
  · have hstoredM : (replaceRow M idx newRow)[k] = M[k] := by
      simp [replaceRow, hidx, hkM]
    rw [hstoredM]
    exact matrix_row_mem_rowSpan hM
      (by simp [MatrixRows, Array.getElem_mem_toList hkM])

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem replaceRow_newRow_mem
    {M : PolynomialMatrix F} {idx : Nat} {newRow : PolynomialRow F}
    (hidx : idx < M.size) :
    newRow ∈ MatrixRows (replaceRow M idx newRow) := by
  have hidxReplace : idx < (replaceRow M idx newRow).size := by
    simpa [replaceRow_size] using hidx
  have hget : (replaceRow M idx newRow)[idx] = newRow := by
    simp [replaceRow]
  have hmem : (replaceRow M idx newRow)[idx] ∈ MatrixRows (replaceRow M idx newRow) := by
    exact Array.getElem_mem_toList hidxReplace
  simpa [hget] using hmem

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem replaceRow_oldRow_mem
    {M : PolynomialMatrix F} {idx k : Nat} {newRow : PolynomialRow F}
    (hk : k < M.size) (hne : idx ≠ k) :
    M[k] ∈ MatrixRows (replaceRow M idx newRow) := by
  have hkReplace : k < (replaceRow M idx newRow).size := by
    simpa [replaceRow_size] using hk
  have hget : (replaceRow M idx newRow)[k] = M[k] := by
    simp [replaceRow, hne, hk]
  rw [← hget]
  simp [MatrixRows, Array.getElem_mem_toList hkReplace]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem matrix_getD_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    (M.getD i #[]).size = MatrixWidth M := by
  have hget : M.getD i #[] = M[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget]
  exact hM M[i] (by simp [MatrixRows, Array.getElem_mem_toList hi])

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem matrix_getElem?_getD_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    (M[i]?.getD #[]).size = MatrixWidth M := by
  simpa [Array.getElem?_eq_getElem hi] using matrix_getD_size_of_wellFormed hM hi

theorem matrix_getD_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    M.getD i #[] ∈ RowSpan M := by
  have hget : M.getD i #[] = M[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget]
  exact matrix_row_mem_rowSpan hM
    (by simp [MatrixRows, Array.getElem_mem_toList hi])

omit [DecidableEq F] in
theorem zeroRow_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) :
    zeroRow (F := F) (MatrixWidth M) ∈ RowSpan M := by
  let coeffs := Array.replicate M.size (0 : CPolynomial F)
  refine ⟨coeffs, by simp [coeffs], ?_⟩
  unfold rowLinearCombination
  have hfold :
      ∀ n, n ≤ M.size →
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) = zeroRow (F := F) (MatrixWidth M) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hnM : n < M.size := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (by omega)]
        have hcoeff : coeffs.getD n 0 = 0 := by
          simp [coeffs, hnM]
        rw [hcoeff, rowScalePolynomial_zero]
        rw [matrix_getD_size_of_wellFormed hM hnM]
        exact rowAdd_zeroRow_zeroRow (MatrixWidth M)
  exact (hfold M.size (Nat.le_refl M.size)).symm

omit [DecidableEq F] in
theorem rowLinearCombination_mem_rowSpan_of_rows_mem
    {A B : PolynomialMatrix F} (hB : WellFormed B)
    (hwidth : MatrixWidth A = MatrixWidth B)
    (hrows : ∀ row, row ∈ MatrixRows A → row ∈ RowSpan B)
    (coeffs : Array (CPolynomial F)) :
    rowLinearCombination coeffs A ∈ RowSpan B := by
  unfold rowLinearCombination
  have hfold :
      ∀ n, n ≤ A.size →
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (A.getD i #[])))
          (zeroRow (MatrixWidth A))) ∈ RowSpan B := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [hwidth]
        exact zeroRow_mem_rowSpan hB
    | succ n ih =>
        intro hn
        have hnA : n < A.size := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        apply rowAdd_mem_rowSpan
        · exact ih (by omega)
        · apply rowScalePolynomial_mem_rowSpan
          have hget : A.getD n #[] = A[n] := by
            simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hnA]
          rw [hget]
          exact hrows A[n] (by simp [MatrixRows, Array.getElem_mem_toList hnA])
  exact hfold A.size (Nat.le_refl A.size)

omit [DecidableEq F] in
theorem rowSpan_subset_of_rows_mem
    {A B : PolynomialMatrix F} (hB : WellFormed B)
    (hwidth : MatrixWidth A = MatrixWidth B)
    (hrows : ∀ row, row ∈ MatrixRows A → row ∈ RowSpan B) :
    RowSpan A ⊆ RowSpan B := by
  intro row hrow
  rcases hrow with ⟨coeffs, _hsize, rfl⟩
  exact rowLinearCombination_mem_rowSpan_of_rows_mem hB hwidth hrows coeffs

theorem cancelShiftedLeadingTerm_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i j : Nat}
    (hi : i < M.size) (hj : j < M.size) (shift : Array Nat) :
    (cancelShiftedLeadingTerm (M.getD i #[]) (M.getD j #[]) shift).size =
      MatrixWidth M := by
  rw [cancelShiftedLeadingTerm_size
      (hsize := (matrix_getD_size_of_wellFormed hM hj).trans
        (matrix_getD_size_of_wellFormed hM hi).symm)]
  exact matrix_getD_size_of_wellFormed hM hi

end PolynomialMatrix

end CompPoly
