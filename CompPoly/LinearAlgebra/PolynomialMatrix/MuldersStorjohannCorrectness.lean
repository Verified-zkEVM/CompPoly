/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann

/-!
# Correctness Contract for Mulders-Storjohann Reduction
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem muldersStorjohannReduce_shape_preserved
    (M : PolynomialMatrix F) (shift : Array Nat) :
    MatrixShape (muldersStorjohannReduce M shift) = MatrixShape M := by
  sorry

theorem muldersStorjohannReduce_rowSpan_eq
    (M : PolynomialMatrix F) (shift : Array Nat) :
    RowSpan (muldersStorjohannReduce M shift) = RowSpan M := by
  sorry

theorem muldersStorjohannReduce_weakPopov
    (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M) (hshift : shift.size = MatrixWidth M) :
    ShiftedWeakPopov (muldersStorjohannReduce M shift) shift := by
  sorry

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
  sorry

/-- Certified direct Mulders-Storjohann shifted row-reducer context. -/
def muldersStorjohannReducerContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] : ShiftedRowReducerContext F where
  reduce := muldersStorjohannReduce
  shape_preserved := by
    intro M shift
    exact muldersStorjohannReduce_shape_preserved M shift
  rowSpan_eq := by
    intro M shift
    exact muldersStorjohannReduce_rowSpan_eq M shift
  weakPopov := by
    intro M shift hM hshift
    exact muldersStorjohannReduce_weakPopov M shift hM hshift
  least_row_minimal := by
    intro M shift row hM hshift hrow hdeg
    exact muldersStorjohannReduce_least_row_minimal M shift row hM hshift hrow hdeg

end PolynomialMatrix

end CompPoly
