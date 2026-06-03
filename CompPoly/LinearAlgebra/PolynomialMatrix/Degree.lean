/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Basic

/-!
# Degree Helpers for Polynomial Rows
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*}

/-- Optional degree of a univariate polynomial, with `none` for zero. -/
def polynomialDegree? [Zero F] [BEq F] (p : CPolynomial F) : Option Nat :=
  if p == 0 then none else some p.natDegree

/-- A row is zero when all entries are zero. -/
def RowIsZero [Zero F] [BEq F] (row : PolynomialRow F) : Prop :=
  ∀ p, p ∈ row.toList → p = 0

/-- Executable zero-row predicate. -/
def rowIsZero [Zero F] [BEq F] (row : PolynomialRow F) : Bool :=
  row.all fun p ↦ p == 0

/-- Boolean and propositional zero-row predicates agree. -/
theorem rowIsZero_iff [Zero F] [BEq F] [LawfulBEq F]
    {row : PolynomialRow F} :
    rowIsZero row = true ↔ RowIsZero row := by
  rw [rowIsZero]
  simp [RowIsZero]
  constructor
  · intro h p hp
    have hp' : p ∈ row.toList := by
      simpa only [Array.mem_def] using hp
    rcases List.getElem_of_mem hp' with ⟨i, hi, hget⟩
    rw [← hget]
    simpa [Array.getElem_toList] using h i (by simpa using hi)
  · intro h i hi
    have hmem : row[i] ∈ row.toList := Array.getElem_mem_toList hi
    exact h row[i] (by simpa only [Array.mem_def] using hmem)

/-- Nonzero rows have an indexed nonzero entry. -/
theorem exists_nonzero_entry_of_rowIsZero_false [Zero F] [BEq F] [LawfulBEq F]
    {row : PolynomialRow F} (hrow : rowIsZero row = false) :
    ∃ j, j < row.size ∧ row.getD j 0 ≠ 0 := by
  have hnot : ¬ RowIsZero row := by
    intro hz
    have htrue := (rowIsZero_iff (row := row)).2 hz
    simp [htrue] at hrow
  rw [RowIsZero] at hnot
  push Not at hnot
  rcases hnot with ⟨p, hp, hpne⟩
  rcases List.getElem_of_mem hp with ⟨j, hj, hget⟩
  refine ⟨j, by simpa using hj, ?_⟩
  have hgetD : row.getD j 0 = p := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hj)]
    simpa [Array.getElem_toList] using hget
  simpa [hgetD] using hpne

end PolynomialMatrix

end CompPoly
