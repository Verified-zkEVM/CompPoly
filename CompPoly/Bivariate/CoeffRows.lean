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

/-- Truncated coefficient rows have the requested width. -/
theorem toCoeffRow_size [Zero F] (width : Nat) (Q : CBivariate F) :
    (toCoeffRow width Q).size = width := by
  simp [toCoeffRow]

/-- Lee-style shift array for `(1, w)` weighted degree. -/
def weightedDegreeShift (w width : Nat) : Array Nat :=
  (List.range width).map (fun j ↦ j * w) |>.toArray

/-- Coefficient-row conversion preserves finite `Y` coefficients below row width. -/
theorem coeff_ofCoeffRow_of_lt [Zero F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) {i j : Nat} (hj : j < row.size) :
    CBivariate.coeff (ofCoeffRow row) i j = CPolynomial.coeff (row.getD j 0) i := by
  have _ := hj
  rw [ofCoeffRow, CBivariate.coeff]
  unfold CPolynomial.ofArray CPolynomial.coeff
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]

/-- Coefficients past the row width vanish after row-to-bivariate conversion. -/
theorem coeff_ofCoeffRow_of_size_le [Zero F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) {i j : Nat} (hj : row.size ≤ j) :
    CBivariate.coeff (ofCoeffRow row) i j = 0 := by
  rw [ofCoeffRow, CBivariate.coeff]
  unfold CPolynomial.ofArray CPolynomial.coeff
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  change CPolynomial.coeff (CPolynomial.Raw.coeff row j) i = 0
  simpa [CPolynomial.Raw.coeff, hj] using CPolynomial.coeff_zero (R := F) i

/-- Row shifted degree for the Lee shift matches weighted degree of the bivariate view. -/
theorem rowShiftedDegree?_eq_natWeightedDegree_ofCoeffRow
    [Field F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (w d : Nat)
    (hdeg :
      PolynomialMatrix.rowShiftedDegree? row (weightedDegreeShift w row.size) = some d) :
    CBivariate.natWeightedDegree (ofCoeffRow row) 1 w = d := by
  have hshift :
      ∀ j, j < row.size → (weightedDegreeShift w row.size).getD j 0 = j * w := by
    intro j hj
    simp [weightedDegreeShift, Array.getD_eq_getD_getElem?, hj]
  apply le_antisymm
  · rw [CBivariate.natWeightedDegree_le_iff]
    intro j hj
    have hcoeff_ne :
        CPolynomial.coeff (ofCoeffRow row) j ≠ 0 := by
      exact (CPolynomial.mem_support_iff (ofCoeffRow row) j).mp hj
    have hjlt : j < row.size := by
      by_contra hnot
      have hge : row.size ≤ j := Nat.le_of_not_gt hnot
      have hcoeff_zero : CPolynomial.coeff (ofCoeffRow row) j = 0 := by
        rw [CPolynomial.eq_zero_iff_coeff_zero]
        intro i
        exact coeff_ofCoeffRow_of_size_le row (i := i) hge
      exact hcoeff_ne hcoeff_zero
    have houter :
        CPolynomial.coeff (ofCoeffRow row) j = row.getD j 0 := by
      rw [ofCoeffRow]
      unfold CPolynomial.ofArray CPolynomial.coeff
      rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
    have hrow_ne : row.getD j 0 ≠ 0 := by
      intro hzero
      exact hcoeff_ne (by simp [houter, hzero])
    have hentry :
        PolynomialMatrix.shiftedEntryDegree? row (weightedDegreeShift w row.size) j =
          some ((row.getD j 0).natDegree +
            (weightedDegreeShift w row.size).getD j 0) := by
      simp [PolynomialMatrix.shiftedEntryDegree?, PolynomialMatrix.rowGet]
      simpa [PolynomialMatrix.rowGet] using hrow_ne
    have hle :=
      PolynomialMatrix.shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some
        hdeg hjlt hentry
    simpa [houter, hshift j hjlt, Nat.mul_comm] using hle
  · obtain ⟨j, hj, hentry⟩ :=
      PolynomialMatrix.exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hdeg
    have houter :
        CPolynomial.coeff (ofCoeffRow row) j = row.getD j 0 := by
      rw [ofCoeffRow]
      unfold CPolynomial.ofArray CPolynomial.coeff
      rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
    have hrow_ne : row.getD j 0 ≠ 0 := by
      intro hzero
      have hnone :
          PolynomialMatrix.shiftedEntryDegree? row (weightedDegreeShift w row.size) j =
            none := by
        simp [PolynomialMatrix.shiftedEntryDegree?, PolynomialMatrix.rowGet, hzero]
      rw [hentry] at hnone
      contradiction
    have hsupport : j ∈ CPolynomial.support (ofCoeffRow row) := by
      rw [CPolynomial.mem_support_iff]
      simpa [houter] using hrow_ne
    have hd :
        d = (row.getD j 0).natDegree +
            (weightedDegreeShift w row.size).getD j 0 := by
      have hsimp :
          row[j]?.getD 0 ≠ 0 ∧
            d = (row[j]?.getD 0).natDegree +
              (weightedDegreeShift w row.size)[j]?.getD 0 := by
        simpa [PolynomialMatrix.shiftedEntryDegree?, PolynomialMatrix.rowGet] using hentry.symm
      simpa [Array.getD_eq_getD_getElem?] using hsimp.2
    calc
      d = (row.getD j 0).natDegree +
            (weightedDegreeShift w row.size).getD j 0 := hd
      _ = 1 * (CPolynomial.coeff (ofCoeffRow row) j).natDegree + w * j := by
        simp [houter, hshift j hj, Nat.mul_comm]
      _ ≤ (CPolynomial.support (ofCoeffRow row)).sup
            (fun j ↦ 1 * (CPolynomial.coeff (ofCoeffRow row) j).natDegree + w * j) := by
        exact Finset.le_sup
          (s := CPolynomial.support (ofCoeffRow row))
          (f := fun j ↦ 1 * (CPolynomial.coeff (ofCoeffRow row) j).natDegree + w * j)
          hsupport
      _ = CBivariate.natWeightedDegree (ofCoeffRow row) 1 w := by
        rfl

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
