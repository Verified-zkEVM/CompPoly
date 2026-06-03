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
  sorry

/-- Nonzero rows have an indexed nonzero entry. -/
theorem exists_nonzero_entry_of_rowIsZero_false [Zero F] [BEq F] [LawfulBEq F]
    {row : PolynomialRow F} (hrow : rowIsZero row = false) :
    ∃ j, j < row.size ∧ row.getD j 0 ≠ 0 := by
  sorry

end PolynomialMatrix

end CompPoly
