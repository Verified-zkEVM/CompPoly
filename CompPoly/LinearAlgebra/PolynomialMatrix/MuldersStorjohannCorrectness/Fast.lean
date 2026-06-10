/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Minimal

/-!
# Fast Mulders-Storjohann Reduction Agrees With the Direct Definition

The fast reducer caches shifted leading positions once per conflict scan and
cancels leading terms through the fused `rowSubScaledShift` update. This file
proves it extensionally equal to `muldersStorjohannReduce`, so every
correctness result transfers, and packages it as a certified
`ShiftedRowReducerContext`.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ### Row-level cancellation -/

omit [DecidableEq F] in
theorem rowSubScaledShift_size (a : PolynomialRow F) (c : F) (d : Nat)
    (b : PolynomialRow F) :
    (rowSubScaledShift a c d b).size = max a.size b.size := by
  simp [rowSubScaledShift]

theorem rowGet_rowSubScaledShift (a : PolynomialRow F) (c : F) (d : Nat)
    (b : PolynomialRow F) (j : Nat) :
    rowGet (rowSubScaledShift a c d b) j =
      CPolynomial.subMulMonomial (rowGet a j) c d (rowGet b j) := by
  by_cases hj : j < (rowSubScaledShift a c d b).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowSubScaledShift]
  · have hle : (rowSubScaledShift a c d b).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    rw [rowSubScaledShift_size] at hle
    have hja : a.size ≤ j := by omega
    have hjb : b.size ≤ j := by omega
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hja,
      Option.getD_none, rowGet, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none hjb, Option.getD_none,
      CPolynomial.subMulMonomial_eq]
    simp

theorem rowSubScaledShift_eq (a : PolynomialRow F) (c : F) (d : Nat)
    (b : PolynomialRow F) :
    rowSubScaledShift a c d b = rowSub a (rowScaleMonomial c d b) := by
  apply Array.ext
  · rw [rowSubScaledShift_size, rowSub_size, rowScaleMonomial_size]
  · intro j hj hj'
    have hlhs : (rowSubScaledShift a c d b)[j] =
        rowGet (rowSubScaledShift a c d b) j := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj,
        Option.getD_some]
    have hrhs : (rowSub a (rowScaleMonomial c d b))[j] =
        rowGet (rowSub a (rowScaleMonomial c d b)) j := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj',
        Option.getD_some]
    rw [hlhs, hrhs, rowGet_rowSubScaledShift, rowGet_rowSub,
      rowGet_rowScaleMonomial, CPolynomial.subMulMonomial_eq]

theorem cancelShiftedLeadingTermFast_eq (target reducer : PolynomialRow F)
    (shift : Array Nat) :
    cancelShiftedLeadingTermFast target reducer shift =
      cancelShiftedLeadingTerm target reducer shift := by
  unfold cancelShiftedLeadingTermFast cancelShiftedLeadingTerm
  simp only [rowSubScaledShift_eq]

/-! ### Cached conflict scan -/

omit [Field F] [LawfulBEq F] [DecidableEq F] in
theorem rowLeadingPositions_size [Zero F] (M : PolynomialMatrix F)
    (shift : Array Nat) :
    (rowLeadingPositions M shift).size = M.size := by
  simp [rowLeadingPositions]

omit [LawfulBEq F] [DecidableEq F] in
theorem rowLeadingPositions_getD (M : PolynomialMatrix F) (shift : Array Nat)
    {i : Nat} (hi : i < M.size) :
    (rowLeadingPositions M shift).getD i none =
      rowShiftedLeadingPosition? (M.getD i #[]) shift := by
  have hM : M.getD i #[] = M[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Option.getD_some]
  have hpos : i < (rowLeadingPositions M shift).size := by
    rw [rowLeadingPositions_size]; exact hi
  rw [hM, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpos]
  simp [rowLeadingPositions]

omit [LawfulBEq F] [DecidableEq F] in
theorem cachedLeadingConflictInRowStep?_eq (M : PolynomialMatrix F)
    (shift : Array Nat) {i j : Nat} (hi : i < M.size) (hj : j < M.size)
    (found : Option (Nat × Nat)) :
    cachedLeadingConflictInRowStep? (rowLeadingPositions M shift) i found j =
      shiftedLeadingConflictInRowStep? M shift i found j := by
  unfold cachedLeadingConflictInRowStep? shiftedLeadingConflictInRowStep?
  rw [rowLeadingPositions_getD M shift hi, rowLeadingPositions_getD M shift hj]

omit [LawfulBEq F] [DecidableEq F] in
theorem cachedLeadingConflictInRow?_eq (M : PolynomialMatrix F)
    (shift : Array Nat) {i : Nat} (hi : i < M.size)
    (found : Option (Nat × Nat)) :
    cachedLeadingConflictInRow? (rowLeadingPositions M shift) i found =
      shiftedLeadingConflictInRow? M shift i found := by
  unfold cachedLeadingConflictInRow? shiftedLeadingConflictInRow?
  rw [rowLeadingPositions_size]
  apply List.foldl_ext
  intro acc j hjmem
  have hjlt : j < M.size := by
    have hj := List.mem_range'_1.mp hjmem
    omega
  exact cachedLeadingConflictInRowStep?_eq M shift hi hjlt acc

omit [LawfulBEq F] [DecidableEq F] in
theorem cachedLeadingConflict?_eq (M : PolynomialMatrix F) (shift : Array Nat) :
    cachedLeadingConflict? (rowLeadingPositions M shift) =
      shiftedLeadingConflict? M shift := by
  unfold cachedLeadingConflict? shiftedLeadingConflict?
    shiftedLeadingConflictFrom? shiftedLeadingConflictFromStep?
  rw [rowLeadingPositions_size]
  apply List.foldl_ext
  intro acc i himem
  have hilt : i < M.size := by
    have hi := List.mem_range'_1.mp himem
    omega
  exact cachedLeadingConflictInRow?_eq M shift hilt acc

/-! ### Step, loop, and reducer -/

theorem muldersStorjohannStepFast_eq (M : PolynomialMatrix F)
    (shift : Array Nat) (i j : Nat) :
    muldersStorjohannStepFast M shift i j = muldersStorjohannStep M shift i j := by
  unfold muldersStorjohannStepFast muldersStorjohannStep
  simp only [cancelShiftedLeadingTermFast_eq]

theorem muldersStorjohannReduceWithFuelFast_eq :
    ∀ (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat),
      muldersStorjohannReduceWithFuelFast fuel M shift =
        muldersStorjohannReduceWithFuel fuel M shift := by
  intro fuel
  induction fuel with
  | zero =>
      intro M shift
      rfl
  | succ fuel ih =>
      intro M shift
      unfold muldersStorjohannReduceWithFuelFast muldersStorjohannReduceWithFuel
      rw [cachedLeadingConflict?_eq]
      cases shiftedLeadingConflict? M shift with
      | none => rfl
      | some pair =>
          simp only [muldersStorjohannStepFast_eq, ih]

theorem muldersStorjohannReduceFast_eq (M : PolynomialMatrix F)
    (shift : Array Nat) :
    muldersStorjohannReduceFast M shift = muldersStorjohannReduce M shift := by
  unfold muldersStorjohannReduceFast muldersStorjohannReduce
  exact muldersStorjohannReduceWithFuelFast_eq _ M shift

/-! ### Certified context -/

/-- Certified fast Mulders-Storjohann shifted row-reducer context. The
implementation caches leading positions per scan and uses fused row
cancellation; correctness transfers along `muldersStorjohannReduceFast_eq`. -/
def muldersStorjohannFastReducerContext (F : Type*) [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] : ShiftedRowReducerContext F where
  reduce := muldersStorjohannReduceFast
  shape_preserved := by
    intro M shift hM
    rw [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_shape_preserved M shift hM
  rowSpan_eq := by
    intro M shift hM
    rw [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_rowSpan_eq M shift hM
  weakPopov := by
    intro M shift hM hshift
    rw [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_weakPopov M shift hM hshift
  least_row_minimal := by
    intro M shift row hM hshift hrow hdeg
    simp only [muldersStorjohannReduceFast_eq]
    exact muldersStorjohannReduce_least_row_minimal M shift row hM hshift hrow hdeg

end PolynomialMatrix

end CompPoly
