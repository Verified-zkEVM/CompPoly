/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeafSoundness
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.XAdicSoundness
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.MatrixRows
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Measure

/-!
# Kernel-Leaf Reduction Row-Span Soundness

The shifted pivot-table reduction preserves the generated row module: the
fuel bound dominates the shifted row measure, every displaced row re-enters
the table as a reduced combination, and the incremental reduction loop keeps
every input row inside the span of its output.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Kernel-leaf reduction row-span soundness

The pivot-table reduction only ever replaces rows by row operations that are
invertible inside the generated row module, so no original row leaves the row
span.  The proofs below make this precise: leading-term cancellation is the
Mulders-Storjohann cancellation in disguise, the pivot-table insertion loop is
tracked through a fuel-indexed measure argument, and the incremental reducer
chains the per-call result through row-span transitivity. -/

/-- Coefficient-shift scaling agrees with monomial multiplication. -/
private theorem polynomialScaleCoeffX_eq_monomial_mul [DecidableEq F]
    (c : F) (d : Nat) (p : CPolynomial F) :
    polynomialScaleCoeffX c d p = CPolynomial.monomial d c * p := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_monomial_mul, CPolynomial.coeff_toPoly,
    polynomialScaleCoeffX_toPoly, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.X_pow_mul, Polynomial.coeff_mul_X_pow']
  split_ifs with h
  · rw [CPolynomial.coeff_toPoly]
  · rw [mul_zero]

/-- Coefficient-shift row scaling agrees with monomial row scaling. -/
private theorem rowScaleCoeffX_eq_rowScaleMonomial [DecidableEq F]
    (c : F) (d : Nat) (row : PolynomialRow F) :
    rowScaleCoeffX c d row = rowScaleMonomial c d row := by
  rw [rowScaleCoeffX, rowScaleMonomial, rowScalePolynomial]
  exact Array.map_congr_left fun p _hp ↦ polynomialScaleCoeffX_eq_monomial_mul c d p

/-- The kernel-leaf cancellation is the Mulders-Storjohann cancellation. -/
private theorem cancelKernelLeafLeadingTerm_eq_cancelShifted [DecidableEq F]
    (target reducer : PolynomialRow F) (shift : Array Nat) :
    cancelKernelLeafLeadingTerm target reducer shift =
      cancelShiftedLeadingTerm target reducer shift := by
  rw [cancelKernelLeafLeadingTerm, cancelShiftedLeadingTerm]
  cases rowShiftedLeadingTerm? target shift with
  | none => rfl
  | some t =>
      cases rowShiftedLeadingTerm? reducer shift with
      | none => rfl
      | some r => simp only [rowScaleCoeffX_eq_rowScaleMonomial]

/-- Kernel-leaf cancellation preserves the row width. -/
private theorem cancelKernelLeafLeadingTerm_size
    {target reducer : PolynomialRow F} {shift : Array Nat}
    (hsize : reducer.size = target.size) :
    (cancelKernelLeafLeadingTerm target reducer shift).size = target.size := by
  rw [cancelKernelLeafLeadingTerm]
  split
  · split
    · split
      · rfl
      · rw [rowSub_size, rowScaleCoeffX_size, hsize, Nat.max_self]
    · rfl
  · rfl

/-- Kernel-leaf cancellation stays inside a row span. -/
private theorem cancelKernelLeafLeadingTerm_mem_rowSpan [DecidableEq F]
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F}
    {shift : Array Nat}
    (htarget : target ∈ RowSpan M) (hreducer : reducer ∈ RowSpan M) :
    cancelKernelLeafLeadingTerm target reducer shift ∈ RowSpan M := by
  rw [cancelKernelLeafLeadingTerm_eq_cancelShifted]
  exact cancelShiftedLeadingTerm_mem_rowSpan htarget hreducer

/-- Kernel-leaf cancellation can be undone inside a row span. -/
private theorem cancelKernelLeafLeadingTerm_target_mem_rowSpan [DecidableEq F]
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F}
    {shift : Array Nat}
    (hcancel : cancelKernelLeafLeadingTerm target reducer shift ∈ RowSpan M)
    (hreducer : reducer ∈ RowSpan M)
    (hsize : reducer.size = target.size) :
    target ∈ RowSpan M := by
  rw [cancelKernelLeafLeadingTerm_eq_cancelShifted] at hcancel
  exact cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hreducer hsize

/-- Kernel-leaf cancellation strictly decreases the shifted row measure. -/
private theorem cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt [DecidableEq F]
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hsize : reducer.size = target.size) :
    shiftedRowMeasure (cancelKernelLeafLeadingTerm target reducer shift) shift <
      shiftedRowMeasure target shift := by
  rw [cancelKernelLeafLeadingTerm_eq_cancelShifted]
  exact cancelShiftedLeadingTerm_shiftedRowMeasure_lt ht hr hpos hle hsize

omit [LawfulBEq F] in
/-- A zero row is the zero row of its width. -/
theorem rowIsZero_eq_zeroRow {row : PolynomialRow F}
    (h : RowIsZero row) : row = zeroRow row.size := by
  apply Array.ext
  · simp [zeroRow]
  · intro j hj hj'
    have hzero : row[j] = 0 := h row[j] (Array.getElem_mem_toList hj)
    simp [zeroRow, hzero]

/-- Rows without a shifted leading term are zero rows. -/
private theorem rowIsZero_of_rowShiftedLeadingTerm?_eq_none
    {row : PolynomialRow F} {shift : Array Nat}
    (h : rowShiftedLeadingTerm? row shift = none) : RowIsZero row := by
  cases hdeg : rowShiftedDegree? row shift with
  | none => exact rowShiftedDegree?_eq_none_iff.1 hdeg
  | some d =>
      rcases rowShiftedLeadingPosition?_some_of_degree hdeg with ⟨pos, hpos⟩
      rcases rowShiftedLeadingTerm?_some_of_position hpos with ⟨term, hterm, _⟩
      rw [hterm] at h
      cases h

/-- Rows with a shifted leading position are nonzero. -/
private theorem not_rowIsZero_of_rowShiftedLeadingPosition?_eq_some
    {row : PolynomialRow F} {shift : Array Nat} {p : Nat}
    (h : rowShiftedLeadingPosition? row shift = some p) : ¬ RowIsZero row := by
  intro hz
  have hdeg : rowShiftedDegree? row shift = none :=
    rowShiftedDegree?_eq_none_iff.2 hz
  rw [rowShiftedLeadingPosition?, hdeg] at h
  cases h

/-- A `some` slot index of an option array is in bounds. -/
private theorem pivot_getD_some_lt_size {α : Type*}
    {pivots : Array (Option α)} {p : Nat} {r : α}
    (h : pivots.getD p none = some r) : p < pivots.size := by
  by_contra hge
  rw [array_getD_of_le' pivots none (Nat.le_of_not_lt hge)] at h
  cases h

omit [BEq F] [LawfulBEq F] in
/-- Every `some` slot of a pivot table appears among its pivot rows. -/
private theorem mem_pivotRows_of_getD
    {pivots : Array (Option (PolynomialRow F))} {p : Nat}
    {r : PolynomialRow F} (h : pivots.getD p none = some r) :
    r ∈ MatrixRows (pivotRows pivots) := by
  have hp : p < pivots.size := pivot_getD_some_lt_size h
  rw [MatrixRows, pivotRows, List.toList_toArray]
  refine List.mem_filterMap.mpr ⟨some r, ?_, rfl⟩
  rw [array_getD_of_lt' pivots none hp] at h
  rw [← h]
  exact Array.getElem_mem_toList hp

omit [BEq F] [LawfulBEq F] in
/-- Matrices with a member row are nonempty. -/
theorem size_pos_of_mem_matrixRows {M : PolynomialMatrix F}
    {r : PolynomialRow F} (h : r ∈ MatrixRows M) : 0 < M.size := by
  rw [MatrixRows] at h
  have hne := List.ne_nil_of_mem h
  rw [← Array.length_toList]
  exact List.length_pos_of_ne_nil hne

omit [BEq F] [LawfulBEq F] in
/-- Uniform row widths make a matrix well formed. -/
theorem wellFormed_of_sizes {M : PolynomialMatrix F} {n : Nat}
    (h : ∀ r ∈ MatrixRows M, r.size = n) : WellFormed M := by
  intro r hr
  rw [matrixWidth_eq_of_first_row (size_pos_of_mem_matrixRows hr) h]
  exact h r hr

omit [BEq F] [LawfulBEq F] in
/-- Pivot rows inherit a uniform slot width. -/
private theorem pivotRows_sizes {n : Nat}
    {pivots : Array (Option (PolynomialRow F))}
    (hsz : ∀ p r, pivots.getD p none = some r → r.size = n) :
    ∀ r ∈ MatrixRows (pivotRows pivots), r.size = n := by
  intro r hr
  exact pivotRows_invariant (fun row ↦ row.size = n) hsz hr

/-- Stored pivot rows lie in the pivot-row span. -/
private theorem stored_mem_rowSpan_pivotRows [DecidableEq F] {n : Nat}
    {pivots : Array (Option (PolynomialRow F))}
    (hsz : ∀ p r, pivots.getD p none = some r → r.size = n)
    {p : Nat} {r : PolynomialRow F} (hget : pivots.getD p none = some r) :
    r ∈ RowSpan (pivotRows pivots) :=
  matrix_row_mem_rowSpan (wellFormed_of_sizes (pivotRows_sizes hsz))
    (mem_pivotRows_of_getD hget)

/-- The width-`n` zero row lies in any nonempty pivot-row span of width `n`. -/
private theorem zeroRow_mem_rowSpan_pivotRows [DecidableEq F] {n : Nat}
    {pivots : Array (Option (PolynomialRow F))}
    (hsz : ∀ p r, pivots.getD p none = some r → r.size = n)
    {q : Nat} {s : PolynomialRow F} (hentry : pivots.getD q none = some s) :
    zeroRow (F := F) n ∈ RowSpan (pivotRows pivots) := by
  have hmem := mem_pivotRows_of_getD hentry
  have hwidth : MatrixWidth (pivotRows pivots) = n :=
    matrixWidth_eq_of_first_row (size_pos_of_mem_matrixRows hmem)
      (pivotRows_sizes hsz)
  have hzero := zeroRow_mem_rowSpan (wellFormed_of_sizes (pivotRows_sizes hsz))
  rwa [hwidth] at hzero

/-- Measure contribution of one pivot-table slot. -/
private def pivotEntryMeasure [DecidableEq F] (shift : Array Nat) :
    Option (PolynomialRow F) → Nat
  | none => 0
  | some r => shiftedRowMeasure r shift

/-- Total shifted measure of all stored pivot-table rows. -/
private def pivotTableMeasure [DecidableEq F]
    (pivots : Array (Option (PolynomialRow F))) (shift : Array Nat) : Nat :=
  (List.range pivots.size).foldl
    (fun acc p ↦ acc + pivotEntryMeasure shift (pivots.getD p none)) 0

private theorem foldRange_add_eq_zero (n : Nat) {f : Nat → Nat}
    (h : ∀ k, k < n → f k = 0) :
    (List.range n).foldl (fun acc k ↦ acc + f k) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (fun k hk ↦ h k (by omega)), h n (by omega)]

private theorem foldRange_add_update (n : Nat) (f : Nat → Nat) {p : Nat}
    (hp : p < n) (v : Nat) :
    (List.range n).foldl (fun acc k ↦ acc + (if k = p then v else f k)) 0 +
        f p =
      (List.range n).foldl (fun acc k ↦ acc + f k) 0 + v := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hpn : p = n
      · subst hpn
        have hpref :
            (List.range p).foldl
                (fun acc k ↦ acc + (if k = p then v else f k)) 0 =
              (List.range p).foldl (fun acc k ↦ acc + f k) 0 := by
          apply foldRange_add_eq_of_pointwise
          intro k hk
          rw [if_neg (by omega)]
        rw [hpref, if_pos rfl]
        omega
      · have hstep := ih (by omega)
        rw [if_neg (fun h ↦ hpn h.symm)]
        omega

omit [LawfulBEq F] in
/-- The empty pivot table has measure zero. -/
private theorem pivotTableMeasure_replicate [DecidableEq F]
    (w : Nat) (shift : Array Nat) :
    pivotTableMeasure
      (Array.replicate w (none : Option (PolynomialRow F))) shift = 0 := by
  rw [pivotTableMeasure, Array.size_replicate]
  apply foldRange_add_eq_zero
  intro k hk
  rw [array_getD_of_lt' _ _ (by simpa using hk), Array.getElem_replicate]
  rfl

omit [LawfulBEq F] in
/-- Pivot-table measure of an in-bounds slot update. -/
private theorem pivotTableMeasure_setIfInBounds [DecidableEq F]
    (pivots : Array (Option (PolynomialRow F))) (shift : Array Nat)
    {p : Nat} (hp : p < pivots.size) (row : PolynomialRow F) :
    pivotTableMeasure (pivots.setIfInBounds p (some row)) shift +
        pivotEntryMeasure shift (pivots.getD p none) =
      pivotTableMeasure pivots shift + shiftedRowMeasure row shift := by
  rw [pivotTableMeasure, pivotTableMeasure, Array.size_setIfInBounds]
  have hpoint :
      (List.range pivots.size).foldl
          (fun acc k ↦ acc +
            pivotEntryMeasure shift
              ((pivots.setIfInBounds p (some row)).getD k none)) 0 =
        (List.range pivots.size).foldl
          (fun acc k ↦ acc +
            (if k = p then shiftedRowMeasure row shift
              else pivotEntryMeasure shift (pivots.getD k none))) 0 := by
    apply foldRange_add_eq_of_pointwise
    intro k hk
    rw [array_getD_setIfInBounds]
    by_cases hkp : k = p
    · subst hkp
      rw [if_pos ⟨rfl, hp⟩, if_pos rfl]
      rfl
    · rw [if_neg (fun hcon ↦ hkp hcon.1.symm), if_neg hkp]
  rw [hpoint]
  exact foldRange_add_update pivots.size _ hp (shiftedRowMeasure row shift)

/-- Pivot-table insertion preserves the table size. -/
private theorem insertKernelLeafPivotRowWithFuel_size :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      (insertKernelLeafPivotRowWithFuel fuel pivots shift row).size =
        pivots.size := by
  intro fuel
  induction fuel with
  | zero => intro pivots shift row; rfl
  | succ fuel ih =>
      intro pivots shift row
      rw [insertKernelLeafPivotRowWithFuel]
      split
      · rfl
      · split
        · exact Array.size_setIfInBounds
        · split
          · exact Array.size_setIfInBounds
          · split
            · simp only []
              rw [ih, Array.size_setIfInBounds]
            · simp only []
              rw [ih]

omit [LawfulBEq F] in
private theorem pivotEntryMeasure_none [DecidableEq F] (shift : Array Nat) :
    pivotEntryMeasure (F := F) shift none = 0 := rfl

omit [LawfulBEq F] in
private theorem pivotEntryMeasure_some [DecidableEq F] (shift : Array Nat)
    (r : PolynomialRow F) :
    pivotEntryMeasure shift (some r) = shiftedRowMeasure r shift := rfl

/-- Pivot-table insertion preserves slot widths and slot leading positions. -/
private theorem insertKernelLeafPivotRowWithFuel_pivotInv {n : Nat} :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      row.size = n →
      (∀ p r, pivots.getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p) →
      ∀ p r,
        (insertKernelLeafPivotRowWithFuel fuel pivots shift row).getD p none =
          some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row _hrow hinv p r hget
      exact hinv p r hget
  | succ fuel ih =>
      intro pivots shift row hrow hinv p r hget
      have hset : ∀ (position : Nat) (newRow : PolynomialRow F),
          newRow.size = n →
          rowShiftedLeadingPosition? newRow shift = some position →
          ∀ p' r',
            (pivots.setIfInBounds position (some newRow)).getD p' none =
              some r' →
            r'.size = n ∧ rowShiftedLeadingPosition? r' shift = some p' := by
        intro position newRow hsize hpos p' r' hget'
        rw [array_getD_setIfInBounds] at hget'
        by_cases hp' : position = p' ∧ position < pivots.size
        · rw [if_pos hp'] at hget'
          cases hget'
          exact ⟨hsize, hp'.1 ▸ hpos⟩
        · rw [if_neg hp'] at hget'
          exact hinv p' r' hget'
      rw [insertKernelLeafPivotRowWithFuel] at hget
      cases hterm : rowShiftedLeadingTerm? row shift with
      | none =>
          simp only [hterm] at hget
          exact hinv p r hget
      | some target =>
          simp only [hterm] at hget
          have hrowpos : rowShiftedLeadingPosition? row shift =
              some target.position :=
            (rowShiftedLeadingTerm?_some_data hterm).2.1
          cases hpiv : pivots.getD target.position none with
          | none =>
              simp only [hpiv] at hget
              exact hset target.position row hrow hrowpos p r hget
          | some pivot =>
              simp only [hpiv] at hget
              cases hpterm : rowShiftedLeadingTerm? pivot shift with
              | none =>
                  simp only [hpterm] at hget
                  exact hset target.position row hrow hrowpos p r hget
              | some reducer =>
                  simp only [hpterm] at hget
                  have hpivn : pivot.size = n :=
                    (hinv target.position pivot hpiv).1
                  split at hget
                  · refine ih (pivots.setIfInBounds target.position (some row))
                      shift (cancelKernelLeafLeadingTerm pivot row shift) ?_ ?_
                      p r hget
                    · rw [cancelKernelLeafLeadingTerm_size (by omega)]
                      exact hpivn
                    · exact hset target.position row hrow hrowpos
                  · refine ih pivots shift
                      (cancelKernelLeafLeadingTerm row pivot shift) ?_ hinv
                      p r hget
                    rw [cancelKernelLeafLeadingTerm_size (by omega)]
                    exact hrow

/-- Pivot-table insertion never erases an occupied slot. -/
private theorem insertKernelLeafPivotRowWithFuel_persist :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F) {q : Nat}
      {s : PolynomialRow F},
      pivots.getD q none = some s →
      ∃ s',
        (insertKernelLeafPivotRowWithFuel fuel pivots shift row).getD q none =
          some s' := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row q s hq
      exact ⟨s, hq⟩
  | succ fuel ih =>
      intro pivots shift row q s hq
      have hset : ∀ (position : Nat) (newRow : PolynomialRow F),
          ∃ s',
            (pivots.setIfInBounds position (some newRow)).getD q none =
              some s' := by
        intro position newRow
        rw [array_getD_setIfInBounds]
        by_cases hpq : position = q ∧ position < pivots.size
        · rw [if_pos hpq]
          exact ⟨newRow, rfl⟩
        · rw [if_neg hpq]
          exact ⟨s, hq⟩
      rw [insertKernelLeafPivotRowWithFuel]
      split
      · exact ⟨s, hq⟩
      · split
        · exact hset _ row
        · split
          · exact hset _ row
          · split
            · simp only []
              rcases hset _ row with ⟨s', hs'⟩
              exact ih _ shift _ hs'
            · simp only []
              exact ih _ shift _ hq

/-- Pivot-table insertion grows the table measure by at most the measure of
the inserted row. -/
private theorem insertKernelLeafPivotRowWithFuel_measure_le [DecidableEq F]
    {n : Nat} :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      pivots.size = n →
      row.size = n →
      (∀ p r, pivots.getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p) →
      pivotTableMeasure (insertKernelLeafPivotRowWithFuel fuel pivots shift row)
          shift ≤
        shiftedRowMeasure row shift + pivotTableMeasure pivots shift := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row _ _ _
      exact Nat.le_add_left _ _
  | succ fuel ih =>
      intro pivots shift row hpsize hrow hinv
      rw [insertKernelLeafPivotRowWithFuel]
      split
      · exact Nat.le_add_left _ _
      · rename_i target hterm
        have hrowpos : rowShiftedLeadingPosition? row shift =
            some target.position :=
          (rowShiftedLeadingTerm?_some_data hterm).2.1
        have hb : target.position < pivots.size := by
          have := rowShiftedLeadingPosition?_lt hrowpos
          omega
        split
        · rename_i hpiv
          have hmeas := pivotTableMeasure_setIfInBounds pivots shift hb row
          rw [hpiv, pivotEntryMeasure_none] at hmeas
          omega
        · rename_i pivot hpiv
          have hpivn : pivot.size = n := (hinv target.position pivot hpiv).1
          have hpivpos : rowShiftedLeadingPosition? pivot shift =
              some target.position := (hinv target.position pivot hpiv).2
          split
          · rename_i hpterm
            rcases rowShiftedLeadingTerm?_some_of_position hpivpos with
              ⟨term, hterm', _⟩
            rw [hterm'] at hpterm
            cases hpterm
          · rename_i reducer hpterm
            have hredpos : target.position = reducer.position := by
              have hd := (rowShiftedLeadingTerm?_some_data hpterm).2.1
              rw [hpivpos] at hd
              exact Option.some.inj hd
            split
            · rename_i hlt
              simp only []
              have hsetinv : ∀ p r,
                  (pivots.setIfInBounds target.position (some row)).getD p
                      none = some r →
                  r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
                intro p r hget'
                rw [array_getD_setIfInBounds] at hget'
                by_cases hp' : target.position = p ∧
                    target.position < pivots.size
                · rw [if_pos hp'] at hget'
                  cases hget'
                  exact ⟨hrow, hp'.1 ▸ hrowpos⟩
                · rw [if_neg hp'] at hget'
                  exact hinv p r hget'
              have hredsize :
                  (cancelKernelLeafLeadingTerm pivot row shift).size = n := by
                rw [cancelKernelLeafLeadingTerm_size (by omega)]
                exact hpivn
              have hih := ih (pivots.setIfInBounds target.position (some row))
                shift (cancelKernelLeafLeadingTerm pivot row shift)
                (by rw [Array.size_setIfInBounds]; exact hpsize) hredsize
                hsetinv
              have hmeas := pivotTableMeasure_setIfInBounds pivots shift hb row
              rw [hpiv, pivotEntryMeasure_some] at hmeas
              have hdec :
                  shiftedRowMeasure (cancelKernelLeafLeadingTerm pivot row
                    shift) shift < shiftedRowMeasure pivot shift :=
                cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt hpterm hterm
                  hredpos.symm (Nat.le_of_lt hlt) (by omega)
              omega
            · rename_i hlt
              simp only []
              have hredsize :
                  (cancelKernelLeafLeadingTerm row pivot shift).size = n := by
                rw [cancelKernelLeafLeadingTerm_size (by omega)]
                exact hrow
              have hih := ih pivots shift
                (cancelKernelLeafLeadingTerm row pivot shift) hpsize hredsize
                hinv
              have hdec :
                  shiftedRowMeasure (cancelKernelLeafLeadingTerm row pivot
                    shift) shift < shiftedRowMeasure row shift :=
                cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt hterm hpterm
                  hredpos (Nat.le_of_not_lt hlt) (by omega)
              omega

/-- Pivot-table insertion keeps the carried row and every stored row inside
the row span of the resulting pivot rows.  The fuel hypothesis is the exact
measure bound consumed by the recursion. -/
private theorem insertKernelLeafPivotRowWithFuel_rowSpan [DecidableEq F]
    {n : Nat} :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      pivots.size = n →
      row.size = n →
      (∀ p r, pivots.getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p) →
      shiftedRowMeasure row shift + pivotTableMeasure pivots shift < fuel →
      (∀ p r, pivots.getD p none = some r →
        r ∈ RowSpan
          (pivotRows
            (insertKernelLeafPivotRowWithFuel fuel pivots shift row))) ∧
      ((¬ RowIsZero row ∨ ∃ q s, pivots.getD q none = some s) →
        row ∈ RowSpan
          (pivotRows
            (insertKernelLeafPivotRowWithFuel fuel pivots shift row))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row _ _ _ hfuel
      exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
      intro pivots shift row hpsize hrow hinv hfuel
      rw [insertKernelLeafPivotRowWithFuel]
      split
      · rename_i hterm
        refine ⟨fun p r hget ↦
          stored_mem_rowSpan_pivotRows (fun p r h ↦ (hinv p r h).1) hget, ?_⟩
        intro hcase
        have hz : RowIsZero row :=
          rowIsZero_of_rowShiftedLeadingTerm?_eq_none hterm
        rcases hcase with hnz | ⟨q, s, hqs⟩
        · exact absurd hz hnz
        · have hrow0 : row = zeroRow n := by
            rw [← hrow]
            exact rowIsZero_eq_zeroRow hz
          rw [hrow0]
          exact zeroRow_mem_rowSpan_pivotRows (fun p r h ↦ (hinv p r h).1) hqs
      · rename_i target hterm
        have hrowpos : rowShiftedLeadingPosition? row shift =
            some target.position :=
          (rowShiftedLeadingTerm?_some_data hterm).2.1
        have hb : target.position < pivots.size := by
          have := rowShiftedLeadingPosition?_lt hrowpos
          omega
        have hsetinv : ∀ p r,
            (pivots.setIfInBounds target.position (some row)).getD p none =
              some r →
            r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
          intro p r hget'
          rw [array_getD_setIfInBounds] at hget'
          by_cases hp' : target.position = p ∧ target.position < pivots.size
          · rw [if_pos hp'] at hget'
            cases hget'
            exact ⟨hrow, hp'.1 ▸ hrowpos⟩
          · rw [if_neg hp'] at hget'
            exact hinv p r hget'
        have hgetrow :
            (pivots.setIfInBounds target.position (some row)).getD
              target.position none = some row := by
          rw [array_getD_setIfInBounds, if_pos ⟨rfl, hb⟩]
        split
        · rename_i hpiv
          refine ⟨?_, fun _ ↦
            stored_mem_rowSpan_pivotRows (fun p r h ↦ (hsetinv p r h).1)
              hgetrow⟩
          intro p r hget
          have hpne : ¬ (target.position = p ∧
              target.position < pivots.size) := by
            rintro ⟨hpe, -⟩
            rw [← hpe, hpiv] at hget
            cases hget
          have hget' :
              (pivots.setIfInBounds target.position (some row)).getD p none =
                some r := by
            rw [array_getD_setIfInBounds, if_neg hpne]
            exact hget
          exact stored_mem_rowSpan_pivotRows (fun p r h ↦ (hsetinv p r h).1)
            hget'
        · rename_i pivot hpiv
          have hpivn : pivot.size = n := (hinv target.position pivot hpiv).1
          have hpivpos : rowShiftedLeadingPosition? pivot shift =
              some target.position := (hinv target.position pivot hpiv).2
          split
          · rename_i hpterm
            rcases rowShiftedLeadingTerm?_some_of_position hpivpos with
              ⟨term, hterm', _⟩
            rw [hterm'] at hpterm
            cases hpterm
          · rename_i reducer hpterm
            have hredpos : target.position = reducer.position := by
              have hd := (rowShiftedLeadingTerm?_some_data hpterm).2.1
              rw [hpivpos] at hd
              exact Option.some.inj hd
            split
            · rename_i hlt
              simp only []
              have hredsize :
                  (cancelKernelLeafLeadingTerm pivot row shift).size = n := by
                rw [cancelKernelLeafLeadingTerm_size (by omega)]
                exact hpivn
              have hmeas := pivotTableMeasure_setIfInBounds pivots shift hb row
              rw [hpiv, pivotEntryMeasure_some] at hmeas
              have hdec :
                  shiftedRowMeasure (cancelKernelLeafLeadingTerm pivot row
                    shift) shift < shiftedRowMeasure pivot shift :=
                cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt hpterm hterm
                  hredpos.symm (Nat.le_of_lt hlt) (by omega)
              have hIH := ih (pivots.setIfInBounds target.position (some row))
                shift (cancelKernelLeafLeadingTerm pivot row shift)
                (by rw [Array.size_setIfInBounds]; exact hpsize) hredsize
                hsetinv (by omega)
              have hrowspan := hIH.1 target.position row hgetrow
              have hredspan := hIH.2
                (Or.inr ⟨target.position, row, hgetrow⟩)
              have hpivspan :=
                cancelKernelLeafLeadingTerm_target_mem_rowSpan hredspan
                  hrowspan (by omega)
              refine ⟨?_, fun _ ↦ hrowspan⟩
              intro p r hget
              by_cases hp : p = target.position
              · subst hp
                rw [hpiv] at hget
                cases hget
                exact hpivspan
              · have hpne : ¬ (target.position = p ∧
                    target.position < pivots.size) := by
                  rintro ⟨hpe, -⟩
                  exact hp hpe.symm
                have hget' :
                    (pivots.setIfInBounds target.position (some row)).getD p
                      none = some r := by
                  rw [array_getD_setIfInBounds, if_neg hpne]
                  exact hget
                exact hIH.1 p r hget'
            · rename_i hlt
              simp only []
              have hredsize :
                  (cancelKernelLeafLeadingTerm row pivot shift).size = n := by
                rw [cancelKernelLeafLeadingTerm_size (by omega)]
                exact hrow
              have hdec :
                  shiftedRowMeasure (cancelKernelLeafLeadingTerm row pivot
                    shift) shift < shiftedRowMeasure row shift :=
                cancelKernelLeafLeadingTerm_shiftedRowMeasure_lt hterm hpterm
                  hredpos (Nat.le_of_not_lt hlt) (by omega)
              have hIH := ih pivots shift
                (cancelKernelLeafLeadingTerm row pivot shift) hpsize hredsize
                hinv (by omega)
              have hpivspan := hIH.1 target.position pivot hpiv
              have hredspan := hIH.2
                (Or.inr ⟨target.position, pivot, hpiv⟩)
              have hrowspan :=
                cancelKernelLeafLeadingTerm_target_mem_rowSpan hredspan
                  hpivspan (by omega)
              exact ⟨fun p r hget ↦ hIH.1 p r hget, fun _ ↦ hrowspan⟩

/-- The row span of the empty matrix only contains the empty row. -/
theorem eq_empty_of_mem_rowSpan_empty {x : PolynomialRow F}
    (hx : x ∈ RowSpan (#[] : PolynomialMatrix F)) : x = #[] := by
  rcases hx with ⟨coeffs, _, rfl⟩
  rfl

/-- A nonempty pivot-row span certifies a stored slot. -/
private theorem exists_entry_of_mem_rowSpan_pivotRows
    {pivots : Array (Option (PolynomialRow F))} {x : PolynomialRow F}
    (hx : x ∈ RowSpan (pivotRows pivots)) (hxne : x ≠ #[]) :
    ∃ q s, pivots.getD q none = some s := by
  by_cases h : (pivotRows pivots).size = 0
  · have hempty : pivotRows pivots = #[] := Array.eq_empty_of_size_eq_zero h
    rw [hempty] at hx
    exact absurd (eq_empty_of_mem_rowSpan_empty hx) hxne
  · have h0 : 0 < (pivotRows pivots).size := Nat.pos_of_ne_zero h
    have hmem : (pivotRows pivots)[0] ∈ MatrixRows (pivotRows pivots) := by
      rw [MatrixRows]
      exact Array.getElem_mem_toList h0
    exact pivotRows_invariant (fun _ ↦ ∃ q s, pivots.getD q none = some s)
      (fun q s hqs ↦ ⟨q, s, hqs⟩) hmem

/-- Lift membership in one pivot-row span to a later pivot-row span when every
stored row of the first table stays in the later span. -/
private theorem rowSpan_pivotRows_trans [DecidableEq F] {n : Nat}
    {pivots tableT : Array (Option (PolynomialRow F))}
    (hsz : ∀ p r, pivots.getD p none = some r → r.size = n)
    (hszT : ∀ p r, tableT.getD p none = some r → r.size = n)
    (hmono : ∀ p r, pivots.getD p none = some r →
      r ∈ RowSpan (pivotRows tableT))
    (hpersist : ∀ q s, pivots.getD q none = some s →
      ∃ s', tableT.getD q none = some s')
    {x : PolynomialRow F} (hxnz : ¬ RowIsZero x)
    (hx : x ∈ RowSpan (pivotRows pivots)) :
    x ∈ RowSpan (pivotRows tableT) := by
  have hxne : x ≠ #[] := by
    intro h
    apply hxnz
    rw [h]
    intro p hp
    simp at hp
  rcases exists_entry_of_mem_rowSpan_pivotRows hx hxne with ⟨q, s, hqs⟩
  rcases hpersist q s hqs with ⟨s', hqs'⟩
  have hw1 : MatrixWidth (pivotRows pivots) = n :=
    matrixWidth_eq_of_first_row
      (size_pos_of_mem_matrixRows (mem_pivotRows_of_getD hqs))
      (pivotRows_sizes hsz)
  have hw2 : MatrixWidth (pivotRows tableT) = n :=
    matrixWidth_eq_of_first_row
      (size_pos_of_mem_matrixRows (mem_pivotRows_of_getD hqs'))
      (pivotRows_sizes hszT)
  rcases hx with ⟨coeffs, _, rfl⟩
  exact rowLinearCombination_mem_rowSpan_of_rows_mem
    (wellFormed_of_sizes (pivotRows_sizes hszT)) (hw1.trans hw2.symm)
    (fun r hr ↦ pivotRows_invariant _ hmono hr) coeffs

/-- Folded pivot-table insertion preserves the table invariant. -/
theorem insertKernelLeaf_foldl_pivotInv {n : Nat} :
    ∀ (l : List (PolynomialRow F)) (fuel : Nat)
      (pivots : Array (Option (PolynomialRow F))) (shift : Array Nat),
      (∀ r ∈ l, r.size = n) →
      (∀ p r, pivots.getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p) →
      ∀ p r,
        (l.foldl (fun pv r ↦ insertKernelLeafPivotRowWithFuel fuel pv shift r)
          pivots).getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
  intro l
  induction l with
  | nil =>
      intro fuel pivots shift _ hinv p r hget
      exact hinv p r hget
  | cons head tail ihl =>
      intro fuel pivots shift hl hinv p r hget
      rw [List.foldl_cons] at hget
      exact ihl fuel _ shift (fun r hr ↦ hl r (List.mem_cons_of_mem head hr))
        (insertKernelLeafPivotRowWithFuel_pivotInv fuel pivots shift head
          (hl head List.mem_cons_self) hinv) p r hget

/-- Folded pivot-table insertion never erases an occupied slot. -/
private theorem insertKernelLeaf_foldl_persist :
    ∀ (l : List (PolynomialRow F)) (fuel : Nat)
      (pivots : Array (Option (PolynomialRow F))) (shift : Array Nat)
      {q : Nat} {s : PolynomialRow F},
      pivots.getD q none = some s →
      ∃ s',
        (l.foldl (fun pv r ↦ insertKernelLeafPivotRowWithFuel fuel pv shift r)
          pivots).getD q none = some s' := by
  intro l
  induction l with
  | nil =>
      intro fuel pivots shift q s hq
      exact ⟨s, hq⟩
  | cons head tail ihl =>
      intro fuel pivots shift q s hq
      rw [List.foldl_cons]
      rcases insertKernelLeafPivotRowWithFuel_persist fuel pivots shift head hq
        with ⟨s', hs'⟩
      exact ihl fuel _ shift hs'

/-- Folded pivot-table insertion keeps every inserted nonzero row and every
initially stored row inside the row span of the final pivot rows. -/
private theorem insertKernelLeaf_foldl_rowSpan [DecidableEq F] {n : Nat} :
    ∀ (l : List (PolynomialRow F)) (fuel : Nat)
      (pivots : Array (Option (PolynomialRow F))) (shift : Array Nat),
      pivots.size = n →
      (∀ r ∈ l, r.size = n) →
      (∀ p r, pivots.getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p) →
      pivotTableMeasure pivots shift +
          (l.map (fun r ↦ shiftedRowMeasure r shift)).sum < fuel →
      (∀ p r, pivots.getD p none = some r →
        r ∈ RowSpan (pivotRows
          (l.foldl (fun pv r ↦ insertKernelLeafPivotRowWithFuel fuel pv shift r)
            pivots))) ∧
      (∀ r ∈ l, ¬ RowIsZero r →
        r ∈ RowSpan (pivotRows
          (l.foldl (fun pv r ↦ insertKernelLeafPivotRowWithFuel fuel pv shift r)
            pivots))) := by
  intro l
  induction l with
  | nil =>
      intro fuel pivots shift _ _ hinv _
      refine ⟨fun p r hget ↦
        stored_mem_rowSpan_pivotRows (fun p r h ↦ (hinv p r h).1) hget, ?_⟩
      intro r hr
      simp at hr
  | cons head tail ihl =>
      intro fuel pivots shift hpsize hl hinv hfuel
      rw [List.map_cons, List.sum_cons] at hfuel
      have hheadsize : head.size = n := hl head List.mem_cons_self
      have htailsizes : ∀ r ∈ tail, r.size = n :=
        fun r hr ↦ hl r (List.mem_cons_of_mem head hr)
      rw [List.foldl_cons]
      set pivots₁ := insertKernelLeafPivotRowWithFuel fuel pivots shift head
        with hp₁
      have hsize₁ : pivots₁.size = n := by
        rw [hp₁, insertKernelLeafPivotRowWithFuel_size]
        exact hpsize
      have hinv₁ : ∀ p r, pivots₁.getD p none = some r →
          r.size = n ∧ rowShiftedLeadingPosition? r shift = some p :=
        insertKernelLeafPivotRowWithFuel_pivotInv fuel pivots shift head
          hheadsize hinv
      have hm₁ : pivotTableMeasure pivots₁ shift ≤
          shiftedRowMeasure head shift + pivotTableMeasure pivots shift :=
        insertKernelLeafPivotRowWithFuel_measure_le fuel pivots shift head
          hpsize hheadsize hinv
      have hC := insertKernelLeafPivotRowWithFuel_rowSpan fuel pivots shift
        head hpsize hheadsize hinv (by omega)
      have hIH := ihl fuel pivots₁ shift hsize₁ htailsizes hinv₁ (by omega)
      have htrans : ∀ {x : PolynomialRow F}, ¬ RowIsZero x →
          x ∈ RowSpan (pivotRows pivots₁) →
          x ∈ RowSpan (pivotRows
            (tail.foldl
              (fun pv r ↦ insertKernelLeafPivotRowWithFuel fuel pv shift r)
              pivots₁)) := by
        intro x hxnz hx
        exact rowSpan_pivotRows_trans (fun p r h ↦ (hinv₁ p r h).1)
          (fun p r h ↦
            (insertKernelLeaf_foldl_pivotInv tail fuel pivots₁ shift
              htailsizes hinv₁ p r h).1)
          hIH.1
          (fun q s hqs ↦
            insertKernelLeaf_foldl_persist tail fuel pivots₁ shift hqs)
          hxnz hx
      constructor
      · intro p r hget
        have hrnz : ¬ RowIsZero r :=
          not_rowIsZero_of_rowShiftedLeadingPosition?_eq_some (hinv p r hget).2
        exact htrans hrnz (hC.1 p r hget)
      · intro r hr hrnz
        rcases List.mem_cons.mp hr with heq | hrtail
        · subst heq
          exact htrans hrnz (hC.2 (Or.inl hrnz))
        · exact hIH.2 r hrtail hrnz

/-- The max-degree fold step used by `reduceKernelLeafFuel`. -/
private def kernelLeafDegreeStep (rows : PolynomialMatrix F)
    (shift : Array Nat) (acc : Nat) (i : Nat) : Nat :=
  match rowShiftedDegree? (rows.getD i #[]) shift with
  | none => acc
  | some degree => max acc degree

omit [LawfulBEq F] in
private theorem reduceKernelLeafFuel_eq (rows : PolynomialMatrix F)
    (shift : Array Nat) :
    reduceKernelLeafFuel rows shift =
      (rows.size + 1) * (MatrixWidth rows + 1) *
        ((List.range rows.size).foldl (kernelLeafDegreeStep rows shift) 0 +
          1) := rfl

omit [LawfulBEq F] in
private theorem kernelLeafDegreeStep_fold_le_acc (rows : PolynomialMatrix F)
    (shift : Array Nat) :
    ∀ (xs : List Nat) (acc : Nat),
      acc ≤ xs.foldl (kernelLeafDegreeStep rows shift) acc := by
  intro xs
  induction xs with
  | nil => intro acc; exact Nat.le_refl acc
  | cons x xs ihx =>
      intro acc
      rw [List.foldl_cons]
      cases hx : rowShiftedDegree? (rows.getD x #[]) shift with
      | none =>
          have hstep : kernelLeafDegreeStep rows shift acc x = acc := by
            simp only [kernelLeafDegreeStep, hx]
          rw [hstep]
          exact ihx acc
      | some d =>
          have hstep : kernelLeafDegreeStep rows shift acc x = max acc d := by
            simp only [kernelLeafDegreeStep, hx]
          rw [hstep]
          exact Nat.le_trans (Nat.le_max_left acc d) (ihx (max acc d))

omit [LawfulBEq F] in
private theorem kernelLeafDegreeStep_fold_bound (rows : PolynomialMatrix F)
    (shift : Array Nat) :
    ∀ (xs : List Nat) (acc : Nat) {i d : Nat},
      i ∈ xs →
      rowShiftedDegree? (rows.getD i #[]) shift = some d →
      d ≤ xs.foldl (kernelLeafDegreeStep rows shift) acc := by
  intro xs
  induction xs with
  | nil =>
      intro acc i d hi _
      cases hi
  | cons x xs ihx =>
      intro acc i d hi hdeg
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with heq | hi'
      · have hdeg' : rowShiftedDegree? (rows.getD x #[]) shift = some d :=
          heq ▸ hdeg
        have hstep : kernelLeafDegreeStep rows shift acc x = max acc d := by
          simp only [kernelLeafDegreeStep, hdeg']
        rw [hstep]
        exact Nat.le_trans (Nat.le_max_right acc d)
          (kernelLeafDegreeStep_fold_le_acc rows shift xs (max acc d))
      · exact ihx _ hi' hdeg

omit [LawfulBEq F] in
/-- Total shifted measure of all matrix rows is below the kernel-leaf fuel. -/
private theorem sum_shiftedRowMeasure_lt_reduceKernelLeafFuel [DecidableEq F]
    {rows : PolynomialMatrix F} {shift : Array Nat} {n : Nat}
    (hsizes : ∀ r ∈ MatrixRows rows, r.size = n)
    (hw : MatrixWidth rows = n) :
    (rows.toList.map (fun r ↦ shiftedRowMeasure r shift)).sum <
      reduceKernelLeafFuel rows shift := by
  set D := (List.range rows.size).foldl (kernelLeafDegreeStep rows shift) 0
    with hD
  have hbound : ∀ r ∈ rows.toList,
      shiftedRowMeasure r shift ≤ (D + 1) * (n + 1) := by
    intro r hr
    rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
    have hi' : i < rows.size := by simpa using hi
    have hgetD : rows.getD i #[] = r := by
      rw [array_getD_of_lt' _ _ hi',
        show rows[i] = rows.toList[i] from (Array.getElem_toList hi').symm]
      exact hget
    have hrsize : r.size = n := hsizes r hr
    have hmle := shiftedRowMeasure_le_of_degree_bound
      (row := r) (shift := shift) (d := D) ?_
    · rw [hrsize] at hmle
      exact hmle
    · intro rowDeg hdeg
      refine kernelLeafDegreeStep_fold_bound rows shift (List.range rows.size)
        0 (List.mem_range.mpr hi') ?_
      rw [hgetD]
      exact hdeg
  have hsum := List.sum_le_card_nsmul
    (rows.toList.map (fun r ↦ shiftedRowMeasure r shift)) ((D + 1) * (n + 1))
    (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact hbound r hr)
  rw [List.length_map, Array.length_toList, smul_eq_mul] at hsum
  rw [reduceKernelLeafFuel_eq, hw, ← hD]
  calc (rows.toList.map (fun r ↦ shiftedRowMeasure r shift)).sum
      ≤ rows.size * ((D + 1) * (n + 1)) := hsum
    _ < (rows.size + 1) * ((D + 1) * (n + 1)) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self rows.size)
          (by positivity)
    _ = (rows.size + 1) * (n + 1) * (D + 1) := by ring

/-- The pivot-table reduction preserves the generated row module: every
nonzero source row stays inside the row span of the reduced matrix. -/
theorem reduceKernelLeafRowsByPivots_rowSpan_superset [DecidableEq F]
    {rows : PolynomialMatrix F} {shift : Array Nat} {n : Nat}
    (hsizes : ∀ r ∈ MatrixRows rows, r.size = n)
    {row : PolynomialRow F} (hrow : row ∈ MatrixRows rows)
    (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan (reduceKernelLeafRowsByPivots rows shift) := by
  have hpos : 0 < rows.size := size_pos_of_mem_matrixRows hrow
  have hw : MatrixWidth rows = n := matrixWidth_eq_of_first_row hpos hsizes
  rw [reduceKernelLeafRowsByPivots]
  rw [← Array.foldl_toList]
  refine (insertKernelLeaf_foldl_rowSpan (n := n) rows.toList
    (reduceKernelLeafFuel rows shift)
    (Array.replicate (MatrixWidth rows) none) shift ?_ ?_ ?_ ?_).2 row hrow hnz
  · rw [Array.size_replicate]
    exact hw
  · exact fun r hr ↦ hsizes r hr
  · intro p r hget
    rcases Nat.lt_or_ge p
        (Array.replicate (MatrixWidth rows)
          (none : Option (PolynomialRow F))).size with hp | hp
    · rw [array_getD_of_lt' _ _ hp, Array.getElem_replicate] at hget
      cases hget
    · rw [array_getD_of_le' _ _ hp] at hget
      cases hget
  · rw [pivotTableMeasure_replicate, Nat.zero_add]
    exact sum_shiftedRowMeasure_lt_reduceKernelLeafFuel hsizes hw

/-- Reduced kernel-leaf rows keep the uniform width and are nonzero. -/
theorem reduceKernelLeafRowsByPivots_rows {n : Nat}
    {rows : PolynomialMatrix F} {shift : Array Nat}
    (hsizes : ∀ r ∈ MatrixRows rows, r.size = n) :
    ∀ r ∈ MatrixRows (reduceKernelLeafRowsByPivots rows shift),
      r.size = n ∧ rowIsZero r = false := by
  intro r hr
  rw [reduceKernelLeafRowsByPivots, ← Array.foldl_toList] at hr
  have hinit : ∀ p r,
      (Array.replicate (MatrixWidth rows)
        (none : Option (PolynomialRow F))).getD p none = some r →
      r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
    intro p r hget
    rcases Nat.lt_or_ge p
        (Array.replicate (MatrixWidth rows)
          (none : Option (PolynomialRow F))).size with hp | hp
    · rw [array_getD_of_lt' _ _ hp, Array.getElem_replicate] at hget
      cases hget
    · rw [array_getD_of_le' _ _ hp] at hget
      cases hget
  have hinv := insertKernelLeaf_foldl_pivotInv (n := n) rows.toList
    (reduceKernelLeafFuel rows shift)
    (Array.replicate (MatrixWidth rows) none) shift
    (fun r hr ↦ hsizes r hr) hinit
  refine pivotRows_invariant
    (fun r ↦ r.size = n ∧ rowIsZero r = false) ?_ hr
  intro p r hget
  refine ⟨(hinv p r hget).1, ?_⟩
  have hnz := not_rowIsZero_of_rowShiftedLeadingPosition?_eq_some
    (hinv p r hget).2
  cases hb : rowIsZero r
  · rfl
  · exact absurd (rowIsZero_iff.1 hb) hnz

/-- The incremental insertion step is the plain pivot reduction of the pushed
matrix: the nonzero-row filter never removes anything. -/
private theorem insertKernelLeafRowIncremental_eq {n : Nat}
    {basis : PolynomialMatrix F} {shift : Array Nat} {row : PolynomialRow F}
    (hsizes : ∀ r ∈ MatrixRows (basis.push row), r.size = n) :
    insertKernelLeafRowIncremental basis shift row =
      reduceKernelLeafRowsByPivots (basis.push row) shift := by
  rw [insertKernelLeafRowIncremental, reduceKernelLeafRows]
  rw [Array.filter_eq_self]
  intro r hr
  have hr' : r ∈ MatrixRows (reduceKernelLeafRowsByPivots (basis.push row)
      shift) := by
    rw [MatrixRows]
    exact Array.mem_def.mp hr
  rw [(reduceKernelLeafRowsByPivots_rows hsizes r hr').2]
  rfl

omit [BEq F] [LawfulBEq F] in
/-- Rows of a matrix stay rows after a push. -/
private theorem mem_matrixRows_push_left {basis : PolynomialMatrix F}
    {row r : PolynomialRow F} (hr : r ∈ MatrixRows basis) :
    r ∈ MatrixRows (basis.push row) := by
  rw [MatrixRows, Array.toList_push]
  exact List.mem_append.mpr (Or.inl hr)

omit [BEq F] [LawfulBEq F] in
/-- The pushed row is a row of the pushed matrix. -/
private theorem mem_matrixRows_push_self {basis : PolynomialMatrix F}
    {row : PolynomialRow F} : row ∈ MatrixRows (basis.push row) := by
  rw [MatrixRows, Array.toList_push]
  exact List.mem_append.mpr (Or.inr List.mem_cons_self)

omit [LawfulBEq F] in
/-- The empty row is a zero row. -/
theorem rowIsZero_empty : RowIsZero (#[] : PolynomialRow F) := by
  intro p hp
  simp at hp

/-- Incremental kernel-leaf insertion keeps every previously accounted nonzero
row and every inserted nonzero row inside the row span of the final basis. -/
private theorem insertIncremental_foldl_rowSpan [DecidableEq F] {n : Nat} :
    ∀ (l : List (PolynomialRow F)) (basis : PolynomialMatrix F)
      (shift : Array Nat),
      (∀ r ∈ l, r.size = n) →
      (∀ r ∈ MatrixRows basis, r.size = n) →
      (∀ r ∈ MatrixRows basis, rowIsZero r = false) →
      (∀ x : PolynomialRow F, ¬ RowIsZero x → x ∈ RowSpan basis →
        x ∈ RowSpan (l.foldl
          (fun b r ↦ insertKernelLeafRowIncremental b shift r) basis)) ∧
      (∀ r ∈ l, ¬ RowIsZero r →
        r ∈ RowSpan (l.foldl
          (fun b r ↦ insertKernelLeafRowIncremental b shift r) basis)) := by
  intro l
  induction l with
  | nil =>
      intro basis shift _ _ _
      refine ⟨fun x _ hx ↦ hx, ?_⟩
      intro r hr
      simp at hr
  | cons head tail ihl =>
      intro basis shift hl hbsz hbnz
      have hheadsize : head.size = n := hl head List.mem_cons_self
      have htailsizes : ∀ r ∈ tail, r.size = n :=
        fun r hr ↦ hl r (List.mem_cons_of_mem head hr)
      rw [List.foldl_cons]
      have hpushsz : ∀ r ∈ MatrixRows (basis.push head), r.size = n := by
        intro r hr
        rcases mem_matrixRows_push hr with hr' | rfl
        · exact hbsz r hr'
        · exact hheadsize
      set basis₁ := insertKernelLeafRowIncremental basis shift head with hb₁
      have hb₁eq :
          basis₁ = reduceKernelLeafRowsByPivots (basis.push head) shift :=
        insertKernelLeafRowIncremental_eq hpushsz
      have hb₁sz : ∀ r ∈ MatrixRows basis₁, r.size = n := by
        rw [hb₁eq]
        exact fun r hr ↦ (reduceKernelLeafRowsByPivots_rows hpushsz r hr).1
      have hb₁nz : ∀ r ∈ MatrixRows basis₁, rowIsZero r = false := by
        rw [hb₁eq]
        exact fun r hr ↦ (reduceKernelLeafRowsByPivots_rows hpushsz r hr).2
      have hIH := ihl basis₁ shift htailsizes hb₁sz hb₁nz
      have hstep : ∀ r ∈ MatrixRows (basis.push head), ¬ RowIsZero r →
          r ∈ RowSpan basis₁ := by
        intro r hr hrnz
        rw [hb₁eq]
        exact reduceKernelLeafRowsByPivots_rowSpan_superset hpushsz hr hrnz
      have hbasisnz : ∀ r ∈ MatrixRows basis, ¬ RowIsZero r := by
        intro r hr hz
        have hzb := rowIsZero_iff.2 hz
        rw [hbnz r hr] at hzb
        cases hzb
      have hA : ∀ x : PolynomialRow F, ¬ RowIsZero x → x ∈ RowSpan basis →
          x ∈ RowSpan basis₁ := by
        intro x hxnz hx
        by_cases hbsize : basis.size = 0
        · have hbempty : basis = #[] :=
            Array.eq_empty_of_size_eq_zero hbsize
          rw [hbempty] at hx
          have hxempty := eq_empty_of_mem_rowSpan_empty hx
          rw [hxempty] at hxnz
          exact absurd rowIsZero_empty hxnz
        · have hbpos : 0 < basis.size := Nat.pos_of_ne_zero hbsize
          have hwb : MatrixWidth basis = n :=
            matrixWidth_eq_of_first_row hbpos hbsz
          have hb0mem : basis[0] ∈ MatrixRows basis := by
            rw [MatrixRows]
            exact Array.getElem_mem_toList hbpos
          have hb0nz : ¬ RowIsZero basis[0] := hbasisnz basis[0] hb0mem
          have hb0span : basis[0] ∈ RowSpan basis₁ :=
            hstep basis[0] (mem_matrixRows_push_left hb0mem) hb0nz
          have hb₁pos : 0 < basis₁.size := by
            rcases Nat.eq_zero_or_pos basis₁.size with h0 | hpos'
            · have hb₁empty : basis₁ = #[] :=
                Array.eq_empty_of_size_eq_zero h0
              rw [hb₁empty] at hb0span
              have h0eq := eq_empty_of_mem_rowSpan_empty hb0span
              rw [h0eq] at hb0nz
              exact absurd rowIsZero_empty hb0nz
            · exact hpos'
          have hwb₁ : MatrixWidth basis₁ = n :=
            matrixWidth_eq_of_first_row hb₁pos hb₁sz
          rcases hx with ⟨coeffs, _, rfl⟩
          refine rowLinearCombination_mem_rowSpan_of_rows_mem
            (wellFormed_of_sizes hb₁sz) (hwb.trans hwb₁.symm) ?_ coeffs
          intro r hr
          exact hstep r (mem_matrixRows_push_left hr) (hbasisnz r hr)
      constructor
      · intro x hxnz hx
        exact hIH.1 x hxnz (hA x hxnz hx)
      · intro r hr hrnz
        rcases List.mem_cons.mp hr with heq | hrtail
        · subst heq
          exact hIH.1 r hrnz (hstep r mem_matrixRows_push_self hrnz)
        · exact hIH.2 r hrtail hrnz

/-- The incremental kernel-leaf reduction preserves the generated row module:
every nonzero source row stays inside the row span of the reduced basis. -/
theorem reduceKernelLeafRowsIncremental_rowSpan_superset [DecidableEq F]
    {rows : PolynomialMatrix F} {shift : Array Nat} {n : Nat}
    (hsizes : ∀ r ∈ MatrixRows rows, r.size = n)
    {row : PolynomialRow F} (hrow : row ∈ MatrixRows rows)
    (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan (reduceKernelLeafRowsIncremental rows shift) := by
  rw [reduceKernelLeafRowsIncremental, ← Array.foldl_toList]
  refine (insertIncremental_foldl_rowSpan (n := n) rows.toList #[] shift
    (fun r hr ↦ hsizes r hr) ?_ ?_).2 row hrow hnz
  · intro r hr
    simp [MatrixRows] at hr
  · intro r hr
    simp [MatrixRows] at hr

end Approximant

end PolynomialMatrix

end CompPoly
