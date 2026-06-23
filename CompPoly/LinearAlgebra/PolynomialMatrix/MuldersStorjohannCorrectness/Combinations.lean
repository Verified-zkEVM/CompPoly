/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Measure

/-!
# Mulders-Storjohann Correctness Row Combination Helpers

Row-linear-combination size, coefficient, and support lemmas.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [DecidableEq F] in
theorem rowLinearCombination_range_size
    {M : PolynomialMatrix F} (hM : WellFormed M) (coeffs : Array (CPolynomial F)) :
    ∀ n, n ≤ M.size →
      ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))).size = MatrixWidth M := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [zeroRow]
  | succ n ih =>
      intro hn
      have hnM : n < M.size := by omega
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowAdd_size, ih (by omega), rowScalePolynomial_size,
        matrix_getD_size_of_wellFormed hM hnM, max_self]

omit [DecidableEq F] in
theorem rowLinearCombination_size
    {M : PolynomialMatrix F} (hM : WellFormed M) (coeffs : Array (CPolynomial F)) :
    (rowLinearCombination coeffs M).size = MatrixWidth M := by
  simpa [rowLinearCombination] using
    rowLinearCombination_range_size hM coeffs M.size (Nat.le_refl M.size)

def rowCombinationTermSupport
    (coeffs : Array (CPolynomial F)) (M : PolynomialMatrix F) (shift : Array Nat) :
    Finset Nat :=
  (Finset.range M.size).filter fun i ↦
    coeffs.getD i 0 ≠ 0 ∧
      rowShiftedDegree? (M.getD i #[]) shift ≠ none

def rowCombinationTermDegree
    (coeffs : Array (CPolynomial F)) (M : PolynomialMatrix F) (shift : Array Nat)
    (i : Nat) : Nat :=
  match rowShiftedDegree? (M.getD i #[]) shift with
  | some rowDeg => (coeffs.getD i 0).natDegree + rowDeg
  | none => 0

def rowCombinationTermPosition
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) : Nat :=
  (rowShiftedLeadingPosition? (M.getD i #[]) shift).getD 0

omit [DecidableEq F] in
theorem rowGet_rowLinearCombination_range_coeff
    {M : PolynomialMatrix F} (coeffs : Array (CPolynomial F))
    (j k : Nat) :
    ∀ n,
      (rowGet
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) j).coeff k =
        ∑ i ∈ Finset.range n,
          ((coeffs.getD i 0) * rowGet (M.getD i #[]) j).coeff k := by
  intro n
  induction n with
  | zero =>
      simp only [List.range_zero, List.foldl_nil, Finset.sum_range_zero]
      rw [rowGet_zeroRow]
      exact CPolynomial.coeff_zero k
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowGet_rowAdd, CPolynomial.coeff_add,
        rowGet_rowScalePolynomial, ih, Finset.sum_range_succ]

omit [DecidableEq F] in
theorem rowGet_rowLinearCombination_coeff
    {M : PolynomialMatrix F} (coeffs : Array (CPolynomial F))
    (j k : Nat) :
    (rowGet (rowLinearCombination coeffs M) j).coeff k =
      ∑ i ∈ Finset.range M.size,
        ((coeffs.getD i 0) * rowGet (M.getD i #[]) j).coeff k := by
  simpa [rowLinearCombination] using
    rowGet_rowLinearCombination_range_coeff (M := M) coeffs j k M.size

omit [DecidableEq F] in
theorem rowLinearCombination_range_eq_zeroRow_of_forall_zero_or_row_zero
    {M : PolynomialMatrix F} (hM : WellFormed M)
    (coeffs : Array (CPolynomial F))
    (hzero : ∀ i, i < M.size →
      coeffs.getD i 0 = 0 ∨ RowIsZero (M.getD i #[])) :
    ∀ n, n ≤ M.size →
      (List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M)) =
        zeroRow (MatrixWidth M) := by
  intro n hn
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnM : n < M.size := by omega
      have hrowSize :
          (M.getD n #[]).size = MatrixWidth M :=
        matrix_getD_size_of_wellFormed hM hnM
      have hterm :
          rowScalePolynomial (coeffs.getD n 0) (M.getD n #[]) =
            zeroRow (F := F) (MatrixWidth M) := by
        rcases hzero n hnM with hcoeff | hrowZero
        · rw [hcoeff, rowScalePolynomial_zero, hrowSize]
        · rw [rowScalePolynomial_eq_zeroRow_of_rowIsZero
            (coeffs.getD n 0) hrowZero, hrowSize]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega), hterm, rowAdd_zeroRow_zeroRow]

omit [DecidableEq F] in
theorem rowLinearCombination_eq_zeroRow_of_forall_zero_or_row_zero
    {M : PolynomialMatrix F} (hM : WellFormed M)
    (coeffs : Array (CPolynomial F))
    (hzero : ∀ i, i < M.size →
      coeffs.getD i 0 = 0 ∨ RowIsZero (M.getD i #[])) :
    rowLinearCombination coeffs M = zeroRow (F := F) (MatrixWidth M) := by
  simpa [rowLinearCombination] using
    rowLinearCombination_range_eq_zeroRow_of_forall_zero_or_row_zero
      hM coeffs hzero M.size (Nat.le_refl M.size)

theorem rowCombinationTermSupport_nonempty_of_combination_degree_some
    {M : PolynomialMatrix F} {shift : Array Nat}
    (hM : WellFormed M) {coeffs : Array (CPolynomial F)} {rowDeg : Nat}
    (hdeg : rowShiftedDegree? (rowLinearCombination coeffs M) shift = some rowDeg) :
    (rowCombinationTermSupport coeffs M shift).Nonempty := by
  by_contra hnonempty
  have hzero : ∀ i, i < M.size →
      coeffs.getD i 0 = 0 ∨ RowIsZero (M.getD i #[]) := by
    intro i hi
    have hiNot : i ∉ rowCombinationTermSupport coeffs M shift := by
      intro hiMem
      exact hnonempty ⟨i, hiMem⟩
    by_cases hcoeff : coeffs.getD i 0 = 0
    · exact Or.inl hcoeff
    · right
      have hdegNone : rowShiftedDegree? (M.getD i #[]) shift = none := by
        by_contra hrowDeg
        exact hiNot
          (Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hi, hcoeff, hrowDeg⟩)
      exact (rowShiftedDegree?_eq_none_iff (row := M.getD i #[]) (shift := shift)).1 hdegNone
  have hcombZero :=
    rowLinearCombination_eq_zeroRow_of_forall_zero_or_row_zero hM coeffs hzero
  have hnone :
      rowShiftedDegree? (rowLinearCombination coeffs M) shift = none := by
    rw [hcombZero]
    exact (rowShiftedDegree?_eq_none_iff
      (row := zeroRow (F := F) (MatrixWidth M)) (shift := shift)).2
        (zeroRow_rowIsZero (F := F) (MatrixWidth M))
  rw [hdeg] at hnone
  contradiction

end PolynomialMatrix

end CompPoly
