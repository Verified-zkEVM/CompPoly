/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import CompPoly.LinearAlgebra.PolynomialMatrix.StrassenCorrectness
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# X-Adic Row Soundness Toolkit

The `RowApproximates` predicate, its divisibility characterization, closure
under the row operations used by the leaf reduction and completion steps, and
the soundness of one divide-and-conquer composition step.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## X-adic row soundness toolkit

Semantic tools for proving that every row produced by the recursive PM-basis
driver satisfies the X-adic approximant conditions.  Soundness is phrased via
`X^order` divisibility of the `toPoly` image, which makes it closed under the
row operations used by the reduction, completion, and composition steps. -/

/-- A row approximates an X-adic problem when every column product vanishes to
the required order. -/
def RowApproximates (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) (row : PolynomialRow F) : Prop :=
  ∀ j, j < problem.orders.size →
    truncateX (problem.orders.getD j 0)
      (rowGet (rowMulMatrixWith mulCtx row problem.matrix) j) = 0

/-- Truncation vanishes exactly on `X^order`-multiples under `toPoly`. -/
theorem truncateX_eq_zero_iff_X_pow_dvd (order : Nat) (p : CPolynomial F) :
    truncateX order p = 0 ↔ (Polynomial.X : Polynomial F) ^ order ∣ p.toPoly := by
  rw [Polynomial.X_pow_dvd_iff]
  constructor
  · intro h t ht
    have hcoeff := congrArg (fun q ↦ CPolynomial.coeff q t) h
    simp only [truncateX_coeff, if_pos ht, CPolynomial.coeff_zero] at hcoeff
    rw [← CPolynomial.coeff_toPoly]
    exact hcoeff
  · intro h
    apply CPolynomial.eq_iff_coeff.2
    intro t
    rw [truncateX_coeff, CPolynomial.coeff_zero]
    split
    · rename_i ht
      rw [CPolynomial.coeff_toPoly]
      exact h t ht
    · rfl

/-- Truncation of the zero polynomial is zero. -/
theorem truncateX_zero_eq_zero (order : Nat) :
    truncateX (F := F) order 0 = 0 := by
  rw [truncateX_eq_zero_iff_X_pow_dvd, CPolynomial.toPoly_zero]
  exact dvd_zero _

private theorem pm_foldl_add_eq_sum {M : Type*} [AddCommMonoid M] (f : Nat → M) :
    ∀ n : Nat,
      (List.range n).foldl (fun acc k ↦ acc + f k) 0 = ∑ k ∈ Finset.range n, f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ]

/-- `toPoly` commutes with finite range sums. -/
theorem pm_toPoly_finset_sum (f : Nat → CPolynomial F) (n : Nat) :
    (∑ k ∈ Finset.range n, f k).toPoly = ∑ k ∈ Finset.range n, (f k).toPoly := by
  induction n with
  | zero =>
      simp [CPolynomial.toPoly_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, CPolynomial.toPoly_add, ih]

private theorem rowMulMatrixWith_size (mulCtx : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) :
    (rowMulMatrixWith mulCtx row M).size = MatrixWidth M := by
  simp [rowMulMatrixWith]

private theorem rowGet_rowMulMatrixWith_of_width_le (mulCtx : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) {j : Nat}
    (hj : MatrixWidth M ≤ j) :
    rowGet (rowMulMatrixWith mulCtx row M) j = 0 := by
  rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
    (by rw [rowMulMatrixWith_size]; omega)]
  rfl

/-- Column entries of a row-by-matrix product as sums over the matrix height,
under `toPoly`. -/
theorem rowGet_rowMulMatrixWith_toPoly (mulCtx : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) {j : Nat}
    (hj : j < MatrixWidth M) :
    (rowGet (rowMulMatrixWith mulCtx row M) j).toPoly =
      ∑ k ∈ Finset.range M.size,
        (rowGet row k).toPoly * (rowGet (M.getD k #[]) j).toPoly := by
  rw [rowMulMatrixWith, rowGet, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  rw [pm_foldl_add_eq_sum (fun k ↦ mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j))]
  have hsum : ∀ n : Nat,
      (∑ k ∈ Finset.range n,
        mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j)).toPoly =
      ∑ k ∈ Finset.range n,
        (rowGet row k).toPoly * (rowGet (M.getD k #[]) j).toPoly := by
    intro n
    rw [pm_toPoly_finset_sum]
    refine Finset.sum_congr rfl fun k _hk ↦ ?_
    rw [mulCtx.mul_eq_mul, CPolynomial.toPoly_mul]
  rw [hsum]
  rcases Nat.le_total row.size M.size with h | h
  · refine Finset.sum_subset
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      fun k _hk hknot ↦ ?_
    have hk : row.size ≤ k := by simpa using hknot
    have hzero : rowGet row k = 0 := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hk]
      rfl
    rw [hzero, CPolynomial.toPoly_zero, zero_mul]
  · symm
    refine Finset.sum_subset
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
      fun k _hk hknot ↦ ?_
    have hk : M.size ≤ k := by simpa using hknot
    have hzero : M.getD k #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hk]
      rfl
    rw [hzero, show rowGet (#[] : PolynomialRow F) j = 0 from rfl,
      CPolynomial.toPoly_zero, mul_zero]

/-- Divisibility form of the approximant condition, one column at a time. -/
theorem rowApproximates_iff (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) (row : PolynomialRow F) :
    RowApproximates mulCtx problem row ↔
      ∀ j, j < problem.orders.size → j < MatrixWidth problem.matrix →
        (Polynomial.X : Polynomial F) ^ (problem.orders.getD j 0) ∣
          ∑ k ∈ Finset.range problem.matrix.size,
            (rowGet row k).toPoly *
              (rowGet (problem.matrix.getD k #[]) j).toPoly := by
  constructor
  · intro h j hj hjw
    have := h j hj
    rw [truncateX_eq_zero_iff_X_pow_dvd,
      rowGet_rowMulMatrixWith_toPoly mulCtx row problem.matrix hjw] at this
    exact this
  · intro h j hj
    rcases Nat.lt_or_ge j (MatrixWidth problem.matrix) with hjw | hjw
    · rw [truncateX_eq_zero_iff_X_pow_dvd,
        rowGet_rowMulMatrixWith_toPoly mulCtx row problem.matrix hjw]
      exact h j hj hjw
    · rw [rowGet_rowMulMatrixWith_of_width_le mulCtx row problem.matrix hjw]
      exact truncateX_zero_eq_zero _

/-- Row subtraction preserves the approximant condition. -/
theorem rowApproximates_rowSub (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) {a b : PolynomialRow F}
    (ha : RowApproximates mulCtx problem a)
    (hb : RowApproximates mulCtx problem b) :
    RowApproximates mulCtx problem (rowSub a b) := by
  rw [rowApproximates_iff] at ha hb ⊢
  intro j hj hjw
  have hsum : ∑ k ∈ Finset.range problem.matrix.size,
      (rowGet (rowSub a b) k).toPoly *
        (rowGet (problem.matrix.getD k #[]) j).toPoly =
      (∑ k ∈ Finset.range problem.matrix.size,
        (rowGet a k).toPoly * (rowGet (problem.matrix.getD k #[]) j).toPoly) -
      ∑ k ∈ Finset.range problem.matrix.size,
        (rowGet b k).toPoly * (rowGet (problem.matrix.getD k #[]) j).toPoly := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _hk ↦ ?_
    rw [rowGet_rowSub, CPolynomial.toPoly_sub, sub_mul]
  rw [hsum]
  exact dvd_sub (ha j hj hjw) (hb j hj hjw)

private theorem polynomialScaleCoeffX_zero (c : F) (d : Nat) :
    polynomialScaleCoeffX c d (0 : CPolynomial F) = 0 := by
  rw [polynomialScaleCoeffX]
  split
  · rfl
  · rw [if_pos (by simp)]

/-- Coefficient-shift scaling under `toPoly`. -/
theorem polynomialScaleCoeffX_toPoly (c : F) (d : Nat) (p : CPolynomial F) :
    (polynomialScaleCoeffX c d p).toPoly =
      Polynomial.C c * Polynomial.X ^ d * p.toPoly := by
  rw [polynomialScaleCoeffX]
  by_cases hc : c == 0
  · rw [if_pos hc]
    have hc' : c = 0 := by simpa using hc
    rw [hc', CPolynomial.toPoly_zero]
    simp
  · rw [if_neg hc]
    by_cases hp : p == 0
    · rw [if_pos hp]
      have hp' : p = 0 := by simpa using hp
      rw [hp', CPolynomial.toPoly_zero]
      simp
    · rw [if_neg hp]
      apply Polynomial.ext
      intro t
      rw [← CPolynomial.coeff_toPoly, CPolynomial.coeff_ofArray]
      have hrhs : (Polynomial.C c * Polynomial.X ^ d * p.toPoly).coeff t =
          if d ≤ t then c * (p.toPoly.coeff (t - d)) else 0 := by
        rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.X_pow_mul,
          Polynomial.coeff_mul_X_pow']
        split
        · rfl
        · rw [mul_zero]
      rw [hrhs]
      rcases Nat.lt_or_ge t d with htd | htd
      · rw [if_neg (by omega)]
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_append_left (by simpa using htd),
          List.getElem?_replicate_of_lt htd]
        rfl
      · rw [if_pos htd]
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
          List.getElem?_append_right (by simpa using htd)]
        rw [List.length_replicate]
        rw [List.getElem?_map]
        rw [← CPolynomial.coeff_toPoly]
        rcases Nat.lt_or_ge (t - d) p.val.toList.length with hin | hin
        · rw [List.getElem?_eq_getElem hin, Option.map_some, Option.getD_some]
          congr 1
          rw [show CPolynomial.coeff p (t - d) = p.val.coeff (t - d) from rfl]
          rw [CPolynomial.Raw.coeff]
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
            (by simpa using hin), Option.getD_some]
          simp [Array.getElem_toList]
        · rw [List.getElem?_eq_none hin, Option.map_none, Option.getD_none]
          rw [show CPolynomial.coeff p (t - d) = p.val.coeff (t - d) from rfl]
          rw [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none (by simpa using hin)]
          simp

private theorem rowGet_rowScaleCoeffX (c : F) (d : Nat) (row : PolynomialRow F)
    (k : Nat) :
    rowGet (rowScaleCoeffX c d row) k = polynomialScaleCoeffX c d (rowGet row k) := by
  rcases Nat.lt_or_ge k row.size with hk | hk
  · rw [rowScaleCoeffX, rowGet, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by simpa using hk), Option.getD_some,
      Array.getElem_map]
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
      Option.getD_some]
  · rw [rowScaleCoeffX, rowGet, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using hk)]
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hk]
    rw [show ((none : Option (CPolynomial F)).getD 0) = 0 from rfl,
      polynomialScaleCoeffX_zero]

/-- Coefficient-shift row scaling preserves the approximant condition. -/
theorem rowApproximates_rowScaleCoeffX (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) {row : PolynomialRow F} (c : F) (d : Nat)
    (h : RowApproximates mulCtx problem row) :
    RowApproximates mulCtx problem (rowScaleCoeffX c d row) := by
  rw [rowApproximates_iff] at h ⊢
  intro j hj hjw
  have hsum : ∑ k ∈ Finset.range problem.matrix.size,
      (rowGet (rowScaleCoeffX c d row) k).toPoly *
        (rowGet (problem.matrix.getD k #[]) j).toPoly =
      Polynomial.C c * Polynomial.X ^ d *
        ∑ k ∈ Finset.range problem.matrix.size,
          (rowGet row k).toPoly * (rowGet (problem.matrix.getD k #[]) j).toPoly := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _hk ↦ ?_
    rw [rowGet_rowScaleCoeffX, polynomialScaleCoeffX_toPoly, mul_assoc, mul_assoc]
  rw [hsum]
  exact Dvd.dvd.mul_left (h j hj hjw) _

/-- Leading-term cancellation preserves the approximant condition. -/
theorem rowApproximates_cancelKernelLeafLeadingTerm
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    {target reducer : PolynomialRow F} (shift : Array Nat)
    (htarget : RowApproximates mulCtx problem target)
    (hreducer : RowApproximates mulCtx problem reducer) :
    RowApproximates mulCtx problem
      (cancelKernelLeafLeadingTerm target reducer shift) := by
  rw [cancelKernelLeafLeadingTerm]
  split
  · split
    · split
      · exact htarget
      · exact rowApproximates_rowSub mulCtx problem htarget
          (rowApproximates_rowScaleCoeffX mulCtx problem _ _ hreducer)
    · exact htarget
  · exact htarget

/-- Pivot-table insertion preserves the approximant condition of all stored
rows. -/
theorem insertKernelLeafPivotRowWithFuel_approximates
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F) :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      (∀ p r, pivots.getD p none = some r → RowApproximates mulCtx problem r) →
      RowApproximates mulCtx problem row →
      ∀ p r,
        (insertKernelLeafPivotRowWithFuel fuel pivots shift row).getD p none =
          some r →
        RowApproximates mulCtx problem r := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row hpivots _hrow p r hget
      exact hpivots p r hget
  | succ fuel ih =>
      intro pivots shift row hpivots hrow p r hget
      rw [insertKernelLeafPivotRowWithFuel] at hget
      have hset : ∀ (position : Nat) (newRow : PolynomialRow F),
          RowApproximates mulCtx problem newRow →
          ∀ p' r',
            (pivots.setIfInBounds position (some newRow)).getD p' none = some r' →
            RowApproximates mulCtx problem r' := by
        intro position newRow hnew p' r' hget'
        by_cases hpos : p' = position ∧ position < pivots.size
        · rcases hpos with ⟨hp, hlt⟩
          subst hp
          rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_self_of_lt hlt, Option.getD_some] at hget'
          cases hget'
          exact hnew
        · rcases Nat.lt_or_ge p' pivots.size with hplt | hpge
          · have hne : p' ≠ position := by
              intro hcontra
              exact hpos ⟨hcontra, hcontra ▸ hplt⟩
            rw [Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_ne (by omega)] at hget'
            exact hpivots p' r' (by rw [Array.getD_eq_getD_getElem?]; exact hget')
          · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
              (by simpa using hpge)] at hget'
            cases hget'
      cases hterm : rowShiftedLeadingTerm? row shift with
      | none =>
          simp only [hterm] at hget
          exact hpivots p r hget
      | some target =>
          simp only [hterm] at hget
          cases hpivot : pivots.getD target.position none with
          | none =>
              simp only [hpivot] at hget
              exact hset target.position row hrow p r hget
          | some pivot =>
              simp only [hpivot] at hget
              cases hpterm : rowShiftedLeadingTerm? pivot shift with
              | none =>
                  simp only [hpterm] at hget
                  exact hset target.position row hrow p r hget
              | some reducer =>
                  simp only [hpterm] at hget
                  have hpivotrow : RowApproximates mulCtx problem pivot :=
                    hpivots target.position pivot hpivot
                  split at hget
                  · refine ih (pivots.setIfInBounds target.position (some row)) shift
                      (cancelKernelLeafLeadingTerm pivot row shift) ?_ ?_ p r hget
                    · intro p' r' hget'
                      exact hset target.position row hrow p' r' hget'
                    · exact rowApproximates_cancelKernelLeafLeadingTerm mulCtx problem
                        shift hpivotrow hrow
                  · exact ih pivots shift (cancelKernelLeafLeadingTerm row pivot shift)
                      hpivots
                      (rowApproximates_cancelKernelLeafLeadingTerm mulCtx problem
                        shift hrow hpivotrow)
                      p r hget

/-- Rows extracted from a sound pivot table satisfy the approximant
condition. -/
theorem pivotRows_approximates (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) {pivots : Array (Option (PolynomialRow F))}
    (hpivots : ∀ p r, pivots.getD p none = some r →
      RowApproximates mulCtx problem r)
    {row : PolynomialRow F} (hrow : row ∈ MatrixRows (pivotRows pivots)) :
    RowApproximates mulCtx problem row := by
  rw [MatrixRows, pivotRows] at hrow
  rw [List.toList_toArray] at hrow
  rcases List.mem_filterMap.mp hrow with ⟨entry, hentry, hid⟩
  rcases List.getElem_of_mem hentry with ⟨p, hp, hget⟩
  refine hpivots p row ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hp),
    Option.getD_some]
  rw [show pivots[p] = pivots.toList[p] from by rw [Array.getElem_toList]]
  rw [hget]
  exact hid

/-- Pivot-table reduction preserves the approximant condition. -/
theorem reduceKernelLeafRowsByPivots_approximates
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    {rows : PolynomialMatrix F} (shift : Array Nat)
    (hrows : ∀ row, row ∈ MatrixRows rows → RowApproximates mulCtx problem row)
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (reduceKernelLeafRowsByPivots rows shift)) :
    RowApproximates mulCtx problem row := by
  rw [reduceKernelLeafRowsByPivots] at hrow
  refine pivotRows_approximates mulCtx problem ?_ hrow
  have hfold : ∀ (l : List (PolynomialRow F))
      (pivots : Array (Option (PolynomialRow F))),
      (∀ r, r ∈ l → RowApproximates mulCtx problem r) →
      (∀ p r, pivots.getD p none = some r → RowApproximates mulCtx problem r) →
      ∀ p r,
        (l.foldl (fun pivots row ↦
            insertKernelLeafPivotRowWithFuel (reduceKernelLeafFuel rows shift)
              pivots shift row) pivots).getD p none = some r →
        RowApproximates mulCtx problem r := by
    intro l
    induction l with
    | nil =>
        intro pivots _hl hpivots p r hget
        exact hpivots p r hget
    | cons head tail ih =>
        intro pivots hl hpivots p r hget
        rw [List.foldl_cons] at hget
        refine ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem head hr)) ?_ p r hget
        intro p' r' hget'
        exact insertKernelLeafPivotRowWithFuel_approximates mulCtx problem
          (reduceKernelLeafFuel rows shift) pivots shift head hpivots
          (hl head List.mem_cons_self) p' r' hget'
  rw [← Array.foldl_toList]
  refine hfold rows.toList _ (fun r hr ↦ hrows r hr) ?_
  intro p r hget
  rw [Array.getD_eq_getD_getElem?] at hget
  rcases Nat.lt_or_ge p (Array.replicate (MatrixWidth rows)
      (none : Option (PolynomialRow F))).size with hp | hp
  · rw [Array.getElem?_eq_getElem hp, Option.getD_some] at hget
    rw [Array.getElem_replicate] at hget
    cases hget
  · rw [Array.getElem?_eq_none hp] at hget
    cases hget

omit [LawfulBEq F] in
/-- Compaction preserves row membership soundness. -/
theorem compactNonzeroRows_subset {rows : PolynomialMatrix F}
    {row : PolynomialRow F} (hrow : row ∈ MatrixRows (compactNonzeroRows rows)) :
    row ∈ MatrixRows rows := by
  rw [MatrixRows, compactNonzeroRows] at hrow
  rw [MatrixRows]
  have hmem : row ∈ rows ∧ rowIsZero row = false := by simpa using hrow
  simpa using hmem.1

omit [LawfulBEq F] in
/-- Compacted rows are nonzero. -/
theorem compactNonzeroRows_nonzero {rows : PolynomialMatrix F}
    {row : PolynomialRow F} (hrow : row ∈ MatrixRows (compactNonzeroRows rows)) :
    rowIsZero row = false := by
  rw [MatrixRows, compactNonzeroRows] at hrow
  have hmem : row ∈ rows ∧ rowIsZero row = false := by simpa using hrow
  exact hmem.2

/-- The monomial `coeffXPower c d` under `toPoly`. -/
theorem coeffXPower_toPoly (c : F) (d : Nat) :
    (coeffXPower c d).toPoly = Polynomial.C c * Polynomial.X ^ d := by
  apply Polynomial.ext
  intro t
  rw [← CPolynomial.coeff_toPoly, coeffXPower, CPolynomial.coeff_ofArray]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rcases Nat.lt_trichotomy t d with ht | ht | ht
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt
      (by simpa using ht), Option.getD_some, Array.getElem_replicate,
      if_neg (by omega), mul_zero]
  · subst ht
    rw [Array.getD_eq_getD_getElem?]
    rw [show ((Array.replicate t (0 : F)).push c)[t]? = some c from by
      rw [Array.getElem?_push]
      simp]
    simp
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
    simp [Nat.ne_of_gt ht]

/-- Monomial unit rows of sufficiently high degree satisfy every X-adic
condition. -/
theorem rowApproximates_monomialUnitRow (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) {i d : Nat}
    (hd : ∀ j, j < problem.orders.size → problem.orders.getD j 0 ≤ d) :
    RowApproximates mulCtx problem
      (monomialUnitRow problem.matrix.size i d) := by
  rw [rowApproximates_iff]
  intro j hj hjw
  refine Finset.dvd_sum fun k _hk ↦ ?_
  rcases Nat.lt_or_ge k problem.matrix.size with hk | hk
  · have hentry : rowGet (monomialUnitRow (F := F) problem.matrix.size i d) k =
        if i == k then coeffXPower 1 d else 0 := by
      rw [monomialUnitRow, rowGet, Array.getD_eq_getD_getElem?,
        List.getElem?_toArray, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some]
    rw [hentry]
    by_cases hik : i == k
    · rw [if_pos hik, coeffXPower_toPoly]
      calc (Polynomial.X : Polynomial F) ^ (problem.orders.getD j 0)
          ∣ (Polynomial.X : Polynomial F) ^ d := pow_dvd_pow _ (hd j hj)
        _ ∣ Polynomial.C (1 : F) * Polynomial.X ^ d *
              (rowGet (problem.matrix.getD k #[]) j).toPoly :=
            Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
    · rw [if_neg hik, CPolynomial.toPoly_zero, zero_mul]
      exact dvd_zero _
  · have hentry : rowGet (monomialUnitRow (F := F) problem.matrix.size i d) k =
        0 := by
      rw [monomialUnitRow, rowGet, Array.getD_eq_getD_getElem?,
        List.getElem?_toArray, List.getElem?_eq_none (by simpa using hk),
        Option.getD_none]
    rw [hentry, CPolynomial.toPoly_zero, zero_mul]
    exact dvd_zero _

omit [BEq F] [LawfulBEq F] in
/-- Every entry of the order vector is bounded by `maxOrder`. -/
theorem getD_le_maxOrder (problem : XAdicProblem F) {j : Nat}
    (hj : j < problem.orders.size) :
    problem.orders.getD j 0 ≤ maxOrder problem := by
  rw [maxOrder]
  have hmem : problem.orders.getD j 0 ∈ problem.orders.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
    exact Array.getElem_mem_toList hj
  rw [← Array.foldl_toList]
  have hgen : ∀ (l : List Nat) (acc : Nat) (x : Nat), x ∈ l →
      x ≤ l.foldl max acc := by
    intro l
    induction l with
    | nil =>
        intro acc x hx
        cases hx
    | cons head tail ih =>
        intro acc x hx
        rw [List.foldl_cons]
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx
          have hbase : max acc x ≤ tail.foldl max (max acc x) := by
            have hmono : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a := by
              intro l
              induction l with
              | nil => intro a; exact le_rfl
              | cons h t iht =>
                  intro a
                  rw [List.foldl_cons]
                  exact le_trans (Nat.le_max_left a h) (iht (max a h))
            exact hmono tail (max acc x)
          omega
        · exact ih (max acc head) x hx
  exact hgen problem.orders.toList 0 _ hmem

/-- Missing-pivot completion rows satisfy every X-adic condition. -/
theorem missingCompletionRows_approximates (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) (shift : Array Nat) (rows : PolynomialMatrix F)
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (missingCompletionRows problem shift rows)) :
    RowApproximates mulCtx problem row := by
  rw [MatrixRows, missingCompletionRows] at hrow
  rw [List.toList_toArray] at hrow
  rcases List.mem_filterMap.mp hrow with ⟨i, _hi, hsome⟩
  split at hsome
  · cases hsome
  · cases hsome
    refine rowApproximates_monomialUnitRow mulCtx problem fun j hj ↦ ?_
    exact le_trans (getD_le_maxOrder problem hj) (Nat.le_max_right 1 _)

/-- Pivot completion preserves the approximant condition. -/
theorem completeMissingPivotRows_approximates (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) (shift : Array Nat) {rows : PolynomialMatrix F}
    (hrows : ∀ row, row ∈ MatrixRows rows → RowApproximates mulCtx problem row)
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (completeMissingPivotRows problem shift rows)) :
    RowApproximates mulCtx problem row := by
  rw [MatrixRows, completeMissingPivotRows, Array.toList_append] at hrow
  rcases List.mem_append.mp hrow with hmem | hmem
  · exact hrows row hmem
  · exact missingCompletionRows_approximates mulCtx problem shift rows hmem

/-! ## Composition soundness -/

/-- Coefficients of the shifted truncation `divXTrunc`. -/
theorem divXTrunc_coeff (shift order : Nat) (p : CPolynomial F) (t : Nat) :
    CPolynomial.coeff (divXTrunc shift order p) t =
      if t < order then CPolynomial.coeff p (t + shift) else 0 := by
  rw [divXTrunc, CPolynomial.coeff_ofArray]
  rcases Nat.lt_or_ge t order with ht | ht
  · rw [if_pos ht, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_range ht, Option.map_some, Option.getD_some]
  · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_none (by simpa using ht), Option.getD_none]

/-- The row-by-matrix product does not depend on the multiplication context. -/
theorem rowMulMatrixWith_ctx (ctx₁ ctx₂ : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) :
    rowMulMatrixWith ctx₁ row M = rowMulMatrixWith ctx₂ row M := by
  rw [rowMulMatrixWith, rowMulMatrixWith]
  congr 1
  refine List.map_congr_left fun j _hj ↦ ?_
  refine List.foldl_ext _ _ _ fun acc k _hk ↦ ?_
  rw [ctx₁.mul_eq_mul, ctx₂.mul_eq_mul]

omit [BEq F] [LawfulBEq F] in
/-- `getD` of a mapped natural-number array at an in-bounds index. -/
theorem natArray_map_getD (f : Nat → Nat) (a : Array Nat) {j : Nat}
    (hj : j < a.size) :
    (a.map f).getD j 0 = f (a.getD j 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, Array.getElem?_eq_getElem hj]
  rfl

omit [BEq F] [LawfulBEq F] in
/-- A nonempty matrix with uniform row width `n` has `MatrixWidth` `n`. -/
theorem matrixWidth_eq_of_first_row {M : PolynomialMatrix F} {n : Nat}
    (hne : 0 < M.size)
    (hsize : ∀ r ∈ MatrixRows M, r.size = n) :
    MatrixWidth M = n := by
  rw [MatrixWidth, Array.getElem?_eq_getElem hne]
  exact hsize M[0] (by rw [MatrixRows]; exact Array.getElem_mem_toList hne)

omit [BEq F] [LawfulBEq F] in
/-- In-bounds `getD` rows are matrix rows. -/
theorem getD_mem_matrixRows {M : PolynomialMatrix F} {l : Nat}
    (hl : l < M.size) : M.getD l #[] ∈ MatrixRows M := by
  rw [MatrixRows, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl,
    Option.getD_some]
  exact Array.getElem_mem_toList hl

/-- Column entries of a doubly composed row product, when the inner basis has
uniform row width. -/
private theorem rowGet_composed_toPoly (mulCtx : CPolynomial.MulContext F)
    {P₁ M : PolynomialMatrix F}
    (hsize : ∀ r ∈ MatrixRows P₁, r.size = M.size)
    (p₂ : PolynomialRow F) {j : Nat} (hj : j < MatrixWidth M) :
    (rowGet (rowMulMatrixWith mulCtx (rowMulMatrixWith mulCtx p₂ P₁) M) j).toPoly =
      ∑ l ∈ Finset.range P₁.size, (rowGet p₂ l).toPoly *
        (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) M) j).toPoly := by
  rcases Nat.eq_zero_or_pos P₁.size with hP₁ | hP₁
  · rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj, hP₁]
    rw [Finset.range_zero, Finset.sum_empty]
    refine Finset.sum_eq_zero fun k _hk ↦ ?_
    have hzero : rowGet (rowMulMatrixWith mulCtx p₂ P₁) k = 0 := by
      have hwidth : MatrixWidth P₁ = 0 := by
        rw [MatrixWidth, Array.getElem?_eq_none (by omega)]
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
        (by rw [rowMulMatrixWith_size, hwidth]; omega)]
      rfl
    rw [hzero, CPolynomial.toPoly_zero, zero_mul]
  · have hwidth₁ : MatrixWidth P₁ = M.size :=
      matrixWidth_eq_of_first_row hP₁ hsize
    rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj]
    have hentry : ∀ k, k < M.size →
        (rowGet (rowMulMatrixWith mulCtx p₂ P₁) k).toPoly =
          ∑ l ∈ Finset.range P₁.size,
            (rowGet p₂ l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly := by
      intro k hk
      exact rowGet_rowMulMatrixWith_toPoly mulCtx p₂ P₁ (by omega)
    calc ∑ k ∈ Finset.range M.size,
          (rowGet (rowMulMatrixWith mulCtx p₂ P₁) k).toPoly *
            (rowGet (M.getD k #[]) j).toPoly
        = ∑ k ∈ Finset.range M.size, ∑ l ∈ Finset.range P₁.size,
            (rowGet p₂ l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly *
              (rowGet (M.getD k #[]) j).toPoly := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          rw [hentry k (Finset.mem_range.mp hk), Finset.sum_mul]
      _ = ∑ l ∈ Finset.range P₁.size, ∑ k ∈ Finset.range M.size,
            (rowGet p₂ l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly *
              (rowGet (M.getD k #[]) j).toPoly := Finset.sum_comm
      _ = ∑ l ∈ Finset.range P₁.size, (rowGet p₂ l).toPoly *
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) M) j).toPoly := by
          refine Finset.sum_congr rfl fun l _hl ↦ ?_
          rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _hk ↦ ?_
          ring

/-- Soundness of one PM-basis composition step: a residual-approximant row
times a lower-approximant basis approximates the full problem. -/
theorem rowApproximates_composed (mulCtx : CPolynomial.MulContext F)
    {problem : XAdicProblem F} {d₁ : Nat}
    {P₁ Rmat : PolynomialMatrix F}
    (hP₁ : ∀ r ∈ MatrixRows P₁,
      RowApproximates mulCtx
        { orders := lowerOrders problem d₁, matrix := problem.matrix } r ∧
      r.size = problem.matrix.size)
    (hRsize : Rmat.size = P₁.size)
    (hRwidth : 0 < P₁.size → MatrixWidth problem.matrix ≤ MatrixWidth Rmat)
    (hR : ∀ l j, l < P₁.size → j < problem.orders.size →
      j < MatrixWidth problem.matrix →
      ∀ t, t < problem.orders.getD j 0 - d₁ →
        CPolynomial.coeff (rowGet (Rmat.getD l #[]) j) t =
          CPolynomial.coeff
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) problem.matrix) j)
            (t + d₁))
    {p₂ : PolynomialRow F}
    (hp₂ : RowApproximates mulCtx
      { orders := residualOrders problem d₁, matrix := Rmat } p₂) :
    RowApproximates mulCtx problem (rowMulMatrixWith mulCtx p₂ P₁) := by
  rw [rowApproximates_iff]
  intro j hj hjw
  rw [← rowGet_rowMulMatrixWith_toPoly mulCtx _ problem.matrix hjw,
    rowGet_composed_toPoly mulCtx (fun r hr ↦ (hP₁ r hr).2) p₂ hjw]
  set o := problem.orders.getD j 0 with ho
  have hP₁dvd : ∀ l, l < P₁.size →
      (Polynomial.X : Polynomial F) ^ (min o d₁) ∣
        (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
          problem.matrix) j).toPoly := by
    intro l hl
    have hmem := getD_mem_matrixRows hl
    have happrox := (hP₁ _ hmem).1 j (by simpa [lowerOrders] using hj)
    rw [truncateX_eq_zero_iff_X_pow_dvd] at happrox
    have horder : (lowerOrders problem d₁).getD j 0 = min o d₁ := by
      rw [lowerOrders, natArray_map_getD _ _ hj]
    rwa [horder] at happrox
  rcases Nat.le_total o d₁ with hod | hod
  · refine Finset.dvd_sum fun l hl ↦ ?_
    have hdvd := hP₁dvd l (Finset.mem_range.mp hl)
    rw [Nat.min_eq_left hod] at hdvd
    exact Dvd.dvd.mul_left hdvd _
  · rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | hP₁0
    · rw [hP₁0, Finset.range_zero, Finset.sum_empty]
      exact dvd_zero _
    have hwidthR : j < MatrixWidth Rmat := by
      have := hRwidth hP₁0
      omega
    have hquot : ∀ l, ∃ sl : Polynomial F,
        l < P₁.size →
        (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
          problem.matrix) j).toPoly = Polynomial.X ^ d₁ * sl := by
      intro l
      by_cases hl : l < P₁.size
      · have hdvd := hP₁dvd l hl
        rw [Nat.min_eq_right (by omega)] at hdvd
        rcases hdvd with ⟨sl, hsl⟩
        exact ⟨sl, fun _ ↦ hsl⟩
      · exact ⟨0, fun h ↦ absurd h hl⟩
    choose s hs using hquot
    have hcong : ∀ l, l < P₁.size →
        (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
          (rowGet (Rmat.getD l #[]) j).toPoly - s l := by
      intro l hl
      rw [Polynomial.X_pow_dvd_iff]
      intro t ht
      rw [Polynomial.coeff_sub, ← CPolynomial.coeff_toPoly,
        hR l j hl hj hjw t (by omega)]
      rw [CPolynomial.coeff_toPoly]
      have hcoeff : ((rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
          problem.matrix) j).toPoly).coeff (t + d₁) =
          (Polynomial.X ^ d₁ * s l).coeff (t + d₁) := by
        rw [hs l hl]
      rw [Polynomial.coeff_X_pow_mul] at hcoeff
      rw [hcoeff]
      exact sub_self _
    have hresidual : (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
        ∑ l ∈ Finset.range P₁.size,
          (rowGet p₂ l).toPoly * (rowGet (Rmat.getD l #[]) j).toPoly := by
      have hjres : j < (residualOrders problem d₁).size := by
        rw [residualOrders]
        simpa using hj
      have happrox := hp₂ j hjres
      rw [truncateX_eq_zero_iff_X_pow_dvd,
        rowGet_rowMulMatrixWith_toPoly mulCtx p₂ Rmat hwidthR] at happrox
      have horder : (residualOrders problem d₁).getD j 0 = o - d₁ := by
        rw [residualOrders, natArray_map_getD _ _ hj]
      rw [horder, hRsize] at happrox
      exact happrox
    have hquotsum : (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
        ∑ l ∈ Finset.range P₁.size, (rowGet p₂ l).toPoly * s l := by
      have hdiff : (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
          (∑ l ∈ Finset.range P₁.size,
            (rowGet p₂ l).toPoly * (rowGet (Rmat.getD l #[]) j).toPoly) -
          ∑ l ∈ Finset.range P₁.size, (rowGet p₂ l).toPoly * s l := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun l hl ↦ ?_
        rw [← mul_sub]
        exact Dvd.dvd.mul_left (hcong l (Finset.mem_range.mp hl)) _
      have hsub := dvd_sub hresidual hdiff
      simpa using hsub
    have hsum : ∑ l ∈ Finset.range P₁.size, (rowGet p₂ l).toPoly *
        (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
          problem.matrix) j).toPoly =
        Polynomial.X ^ d₁ *
          ∑ l ∈ Finset.range P₁.size, (rowGet p₂ l).toPoly * s l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [hs l (Finset.mem_range.mp hl)]
      ring
    rw [hsum, show o = d₁ + (o - d₁) from by omega, pow_add]
    exact mul_dvd_mul_left _ hquotsum

end Approximant

end PolynomialMatrix

end CompPoly
