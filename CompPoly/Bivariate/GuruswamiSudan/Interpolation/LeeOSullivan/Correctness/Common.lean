/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Algorithm

/-!
# Lee-O'Sullivan Correctness Common Helpers

Basic facts shared by Lee-O'Sullivan soundness and completeness proofs.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

omit [Field F] [Nontrivial F] [DecidableEq F] in
/-- Executable distinct-`x` check agrees with the semantic predicate. -/
theorem distinctXCoordinatesBool_iff {points : Array (F × F)} :
    distinctXCoordinatesBool points = true ↔ DistinctXCoordinates points := by
  unfold distinctXCoordinatesBool DistinctXCoordinates
  generalize points.toList = xs
  induction xs with
  | nil =>
      simp [distinctXCoordinatesListBool]
  | cons point rest ih =>
      simp [distinctXCoordinatesListBool, ih]
      intro _
      constructor
      · intro h x hx
        exact h point.1 x hx rfl
      · intro h a b hab ha
        subst a
        exact h b hab

omit [Nontrivial F] in
/-- The coefficient-form `R` used by Lee evaluates to the packed values at distinct nodes. -/
theorem leeCoefficientForm_eval_point
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    {points : Array (F × F)} (hdistinct : DistinctXCoordinates points)
    {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1
      (CPolynomial.interpolateCoefficientForm V E points) =
      point.2 := by
  exact CPolynomial.interpolateCoefficientForm_eval_point V E hdistinct hpoint

omit [Nontrivial F] [DecidableEq F] in
/-- The vanishing `G` used by Lee vanishes on every listed `x`. -/
theorem leeVanishing_eval_point
    (V : CPolynomial.VanishingPolynomialContext F)
    {points : Array (F × F)} {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1 (V.vanishingPolynomial (points.map fun p ↦ p.1)) = 0 := by
  rw [V.correct]
  apply CPolynomial.eval_vanishingPolynomialArray_eq_zero_of_mem
  rw [Array.toList_map]
  exact List.mem_map.mpr ⟨point, hpoint, rfl⟩

/-- Lee basis rows have exactly `ell + 1` rows. -/
theorem leeOSullivanBasisRows_size
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    (leeOSullivanBasisRows V E points params).size = leeOSullivanWidth params := by
  simp [leeOSullivanBasisRows, leeOSullivanBasisRowsWithRG, leeOSullivanWidth]

/-- Lee basis rows built from fixed `R` and `G` are rectangular. -/
theorem leeOSullivanBasisRowsWithRG_wellFormed
    (R G : CPolynomial F) (params : GSInterpParams) :
    WellFormed (leeOSullivanBasisRowsWithRG R G params) := by
  intro row hrow
  simp [leeOSullivanBasisRowsWithRG, MatrixRows] at hrow
  rcases hrow with ⟨i, hi, rfl⟩
  have hwidth :
      MatrixWidth (leeOSullivanBasisRowsWithRG R G params) =
        leeOSullivanWidth params := by
    simp [leeOSullivanBasisRowsWithRG, MatrixWidth, leeOSullivanWidth,
      CBivariate.toCoeffRow]
  rw [hwidth]
  exact CBivariate.toCoeffRow_size (leeOSullivanWidth params)
    (leeOSullivanBasisPolynomial R G params i)

/-- The executable Lee basis matrix has width `ell + 1`. -/
theorem leeOSullivanBasisRowsWithRG_width
    (R G : CPolynomial F) (params : GSInterpParams) :
    MatrixWidth (leeOSullivanBasisRowsWithRG R G params) =
      leeOSullivanWidth params := by
  simp [leeOSullivanBasisRowsWithRG, MatrixWidth, leeOSullivanWidth,
    CBivariate.toCoeffRow]

/-- Lee basis rows built from packed points are rectangular. -/
theorem leeOSullivanBasisRows_wellFormed
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    WellFormed (leeOSullivanBasisRows V E points params) := by
  simp [leeOSullivanBasisRows]
  exact leeOSullivanBasisRowsWithRG_wellFormed _ _ params

/-- The Lee basis as bivariate polynomials, parallel to the executable row matrix. -/
def leeOSullivanBasisPolynomials
    (R G : CPolynomial F) (params : GSInterpParams) : Array (CBivariate F) :=
  (List.range (leeOSullivanWidth params)).map
    (fun i ↦ leeOSullivanBasisPolynomial R G params i) |>.toArray

/-- The bivariate Lee basis has the same length as the row basis. -/
theorem leeOSullivanBasisPolynomials_size
    (R G : CPolynomial F) (params : GSInterpParams) :
    (leeOSullivanBasisPolynomials (F := F) R G params).size =
      leeOSullivanWidth params := by
  simp [leeOSullivanBasisPolynomials]

/-- In-bounds reads from the bivariate Lee basis return the corresponding basis polynomial. -/
theorem leeOSullivanBasisPolynomials_getD_of_lt
    (R G : CPolynomial F) (params : GSInterpParams) {i : Nat}
    (hi : i < leeOSullivanWidth params) :
    (leeOSullivanBasisPolynomials (F := F) R G params).getD i 0 =
      leeOSullivanBasisPolynomial R G params i := by
  simp [leeOSullivanBasisPolynomials, Array.getD_eq_getD_getElem?, hi]

/-- In-bounds row entries of the executable Lee basis are the `Y` coefficients
of the corresponding bivariate basis polynomial. -/
theorem rowGet_leeOSullivanBasisRowsWithRG_getD
    (R G : CPolynomial F) (params : GSInterpParams) {i j : Nat}
    (hi : i < leeOSullivanWidth params) (hj : j < leeOSullivanWidth params) :
    rowGet
        ((leeOSullivanBasisRowsWithRG R G params).getD i #[]) j =
      CPolynomial.coeff (leeOSullivanBasisPolynomial R G params i) j := by
  have hrow :
      (leeOSullivanBasisRowsWithRG R G params).getD i #[] =
        CBivariate.toCoeffRow (leeOSullivanWidth params)
          (leeOSullivanBasisPolynomial R G params i) := by
    simp [leeOSullivanBasisRowsWithRG, Array.getD_eq_getD_getElem?, hi]
  rw [hrow]
  simp [rowGet, CBivariate.toCoeffRow, Array.getD_eq_getD_getElem?, hj]

end LeeOSullivan

end GuruswamiSudan

end CompPoly
