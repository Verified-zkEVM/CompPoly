/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.RowSpan

/-!
# Shifted Row Reduction Contexts
-/

namespace CompPoly

namespace PolynomialMatrix

/-- Executable shifted row-reduction backend over `F[X]`. -/
structure ShiftedRowReducerContext
    (F : Type*) [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] where
  reduce : PolynomialMatrix F → Array Nat → PolynomialMatrix F
  shape_preserved :
    ∀ M shift, MatrixShape (reduce M shift) = MatrixShape M
  rowSpan_eq :
    ∀ M shift, RowSpan (reduce M shift) = RowSpan M
  weakPopov :
    ∀ M shift,
      WellFormed M →
      shift.size = MatrixWidth M →
        ShiftedWeakPopov (reduce M shift) shift
  least_row_minimal :
    ∀ M shift row,
      WellFormed M →
      shift.size = MatrixWidth M →
      row ∈ RowSpan M →
      rowShiftedDegree? row shift ≠ none →
        ∃ outRow outDeg rowDeg,
          outRow ∈ MatrixRows (reduce M shift) ∧
          rowShiftedDegree? outRow shift = some outDeg ∧
          rowShiftedDegree? row shift = some rowDeg ∧
          outDeg ≤ rowDeg

end PolynomialMatrix

end CompPoly
