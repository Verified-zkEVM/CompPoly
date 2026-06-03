/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.Basic
import CompPoly.LinearAlgebra.PolynomialMatrix.Shifted

/-!
# Coefficient Rows for Bivariate Polynomials

Conversions between finite `Y`-coefficient rows and `CBivariate`.
-/

namespace CompPoly

namespace CBivariate

variable {F : Type*}

/-- Interpret a polynomial row `[q_0, ..., q_l]` as `∑ q_j(X) Y^j`. -/
def ofCoeffRow [Zero F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) : CBivariate F :=
  CPolynomial.ofArray row

/-- Truncate a bivariate polynomial to its first `width` `Y`-coefficient rows. -/
def toCoeffRow [Zero F] (width : Nat) (Q : CBivariate F) :
    PolynomialRow F :=
  (List.range width).map (fun j ↦ CPolynomial.coeff Q j) |>.toArray

/-- Lee-style shift array for `(1, w)` weighted degree. -/
def weightedDegreeShift (w width : Nat) : Array Nat :=
  (List.range width).map (fun j ↦ j * w) |>.toArray

/-- Coefficient-row conversion preserves finite `Y` coefficients below row width. -/
theorem coeff_ofCoeffRow_of_lt [Zero F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) {i j : Nat} (hj : j < row.size) :
    CBivariate.coeff (ofCoeffRow row) i j = CPolynomial.coeff (row.getD j 0) i := by
  sorry

/-- Coefficients past the row width vanish after row-to-bivariate conversion. -/
theorem coeff_ofCoeffRow_of_size_le [Zero F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) {i j : Nat} (hj : row.size ≤ j) :
    CBivariate.coeff (ofCoeffRow row) i j = 0 := by
  sorry

/-- Row shifted degree for the Lee shift matches weighted degree of the bivariate view. -/
theorem rowShiftedDegree?_eq_natWeightedDegree_ofCoeffRow
    [Field F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (w d : Nat)
    (hdeg :
      PolynomialMatrix.rowShiftedDegree? row (weightedDegreeShift w row.size) = some d) :
    CBivariate.natWeightedDegree (ofCoeffRow row) 1 w = d := by
  sorry

/-- Weighted-degree bounded rows convert to weighted-degree bounded bivariates. -/
theorem natWeightedDegree_ofCoeffRow_le_of_rowShiftedDegree?_le
    [Field F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (w bound d : Nat)
    (hdeg :
      PolynomialMatrix.rowShiftedDegree? row (weightedDegreeShift w row.size) = some d)
    (hle : d ≤ bound) :
    CBivariate.natWeightedDegree (ofCoeffRow row) 1 w ≤ bound := by
  rw [rowShiftedDegree?_eq_natWeightedDegree_ofCoeffRow row w d hdeg]
  exact hle

end CBivariate

end CompPoly
