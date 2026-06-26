/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Recursion
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeafCompleteness
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.WeakPopovMinimal

/-!
# Recursive PM-Basis Correctness

Soundness and shifted minimality of the kernel-leaf recursive PM-basis:
every produced row satisfies the X-adic conditions with the principal width,
the recursion generates the full solution module, and the root-normalized
basis is shifted weak Popov, so the predictable-degree property yields a
basis row dominating every nonzero solution.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Every row of the fuel-bounded kernel-leaf PM-basis core approximates the
problem and has the principal row width. -/
theorem pmBasisWithFuelCore_kernelLeaf_rows (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      ∀ row ∈ MatrixRows (pmBasisWithFuelCore
        (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
          composeLeafCutoff) fuel problem shift),
        RowApproximates mulCtx problem row ∧ row.size = problem.matrix.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift row hrow
      rw [pmBasisWithFuelCore] at hrow
      exact kernelLeafBasis_rows mulCtx problem shift row
        (compactNonzeroRows_subset hrow)
  | succ fuel ih =>
      intro problem shift row hrow
      rw [pmBasisWithFuelCore] at hrow
      split at hrow
      · exact kernelLeafBasis_rows mulCtx problem shift row
          (compactNonzeroRows_subset hrow)
      · set d₁ := maxOrder problem / 2 with hd₁
        set lower : XAdicProblem F :=
          { orders := lowerOrders problem d₁, matrix := problem.matrix } with hlower
        set P₁ := pmBasisWithFuelCore
          (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
            composeLeafCutoff) fuel lower shift with hP₁def
        set resOrders := residualOrders problem d₁ with hresOrders
        set Rmat := residualMatrixWithProduct
          (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
          problem.matrix d₁ resOrders with hRmatdef
        set residual : XAdicProblem F :=
          { orders := resOrders, matrix := Rmat } with hresidual
        set shifted := updateShiftByRows P₁ shift with hshifted
        set P₂ := pmBasisWithFuelCore
          (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
            composeLeafCutoff) fuel residual shifted with hP₂def
        have hrow2 : row ∈ MatrixRows (compactNonzeroRows
            (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁)) := hrow
        have hmem := compactNonzeroRows_subset hrow2
        have hnz := compactNonzeroRows_nonzero hrow2
        rw [mulStrassenWith_eq_mulWith, matrixRows_mulWith] at hmem
        rcases List.mem_map.mp hmem with ⟨p₂, hp₂mem, rfl⟩
        have hctx : rowMulMatrixWith lowCtx.mulContext p₂ P₁ =
            rowMulMatrixWith mulCtx p₂ P₁ := rowMulMatrixWith_ctx _ _ _ _
        rw [hctx] at hnz ⊢
        have hIH₁ : ∀ r ∈ MatrixRows P₁,
            RowApproximates mulCtx lower r ∧ r.size = problem.matrix.size :=
          fun r hr ↦ ih lower shift r hr
        have hIH₂ := ih residual shifted p₂ hp₂mem
        rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | hP₁0
        · exfalso
          have hP₁empty : P₁ = #[] := Array.eq_empty_of_size_eq_zero hP₁0
          have hsize0 : (rowMulMatrixWith mulCtx p₂ P₁).size = 0 := by
            rw [rowMulMatrixWith_size, hP₁empty]
            rfl
          rw [Array.eq_empty_of_size_eq_zero hsize0] at hnz
          simp [rowIsZero] at hnz
        · -- Shape facts for the residual matrix.
          have hprodsize : (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
              (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix).size =
                P₁.size := mulTruncColumnStrassenWith_size _ _ _ _ _
          have hRsize : Rmat.size = P₁.size := by
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [ofFn_size, hprodsize]
          have hprodwidth : 0 < P₁.size →
              MatrixWidth (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix) =
                MatrixWidth problem.matrix := by
            intro hpos
            rw [mulTruncColumnStrassenWith_eq_truncateColumns]
            refine matrixWidth_eq_of_first_row
              (by rw [truncateColumns_size, mulWith_size]; omega) ?_
            intro r hr
            rw [MatrixRows, truncateColumns, Array.toList_map] at hr
            rcases List.mem_map.mp hr with ⟨r', hr', rfl⟩
            have hsize' : (rowTruncateColumns
                (resOrders.map fun order ↦ order + d₁) r').size = r'.size := by
              simp [rowTruncateColumns]
            rw [hsize']
            have hr'' : r' ∈ (MatrixRows P₁).map fun r ↦
                rowMulMatrixWith lowCtx.mulContext r problem.matrix := by
              rw [← matrixRows_mulWith]
              exact hr'
            rcases List.mem_map.mp hr'' with ⟨r'', _hr'', rfl⟩
            rw [rowMulMatrixWith_size]
          have hRwidth : 0 < P₁.size →
              MatrixWidth problem.matrix ≤ MatrixWidth Rmat := by
            intro hpos
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [MatrixWidth_ofFn, if_neg (by omega), hprodwidth hpos]
          constructor
          · refine rowApproximates_composed mulCtx hIH₁ hRsize hRwidth ?_ hIH₂.1
            intro l j hl hj hjw t ht
            have hd₁lt : d₁ < problem.orders.getD j 0 := by omega
            have hjres : j < resOrders.size := by
              rw [hresOrders, residualOrders]
              simpa using hj
            have hRentry : rowGet (Rmat.getD l #[]) j =
                divXTrunc d₁ (resOrders.getD j 0)
                  (rowGet ((mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                    (resOrders.map fun order ↦ order + d₁) P₁
                    problem.matrix).getD l #[]) j) := by
              rw [hRmatdef]
              simp only [residualMatrixWithProduct]
              rw [rowGet_ofFn, if_pos ⟨by rw [hprodsize]; exact hl,
                by rw [hprodwidth hP₁0]; exact hjw⟩]
            rw [hRentry, divXTrunc_coeff,
              if_pos (by rw [hresOrders, residualOrders,
                natArray_map_getD _ _ hj]; omega)]
            rw [mulTruncColumnStrassenWith_entry lowCtx composeLeafCutoff _ P₁
              problem.matrix (by omega) j]
            rw [truncateX_coeff, if_pos (by
              rw [natArray_map_getD _ _ hjres, hresOrders, residualOrders,
                natArray_map_getD _ _ hj]
              omega)]
            rw [rowMulMatrixWith_ctx lowCtx.mulContext mulCtx]
          · rw [rowMulMatrixWith_size,
              matrixWidth_eq_of_first_row hP₁0 (fun r hr ↦ (hIH₁ r hr).2)]

/-- Every row of the kernel-leaf recursive PM-basis satisfies the X-adic
approximant conditions. -/
theorem pmBasis_kernelLeaf_approximates (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat)
    (problem : XAdicProblem F) (shift : Array Nat) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (pmBasis
      (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
        composeLeafCutoff) problem shift)) :
    RowApproximates mulCtx problem row := by
  rw [pmBasis, pmBasisWithFuel, pmBasisNormalizeRoot] at hrow
  refine completeMissingPivotRows_approximates mulCtx problem shift ?_ hrow
  intro r hr
  have hr' := compactNonzeroRows_subset hr
  rw [reduceKernelLeafRows] at hr'
  refine reduceKernelLeafRowsByPivots_invariant (RowApproximates mulCtx problem)
    (fun t r' s ht hr'' ↦
      rowApproximates_cancelKernelLeafLeadingTerm mulCtx problem s ht hr'')
    shift ?_ hr'
  intro y hy
  exact (pmBasisWithFuelCore_kernelLeaf_rows mulCtx lowCtx leafCutoff
    composeLeafCutoff _ problem shift y hy).1

/-! ## Generation completeness of the recursive PM-basis core

Every nonzero solution row of an X-adic problem lies in the row module
generated by the recursive PM-basis core.  Together with the shifted weak-Popov
shape of the root normalization this yields the predictable-degree minimality
of the final basis. -/

omit [LawfulBEq F] in
/-- Zero rows read as zero in every coordinate. -/
private theorem pm_rowGet_eq_zero_of_rowIsZero {row : PolynomialRow F}
    (h : RowIsZero row) (j : Nat) : rowGet row j = 0 := by
  rcases Nat.lt_or_ge j row.size with hj | hj
  · rw [rowGet, array_getD_of_lt' _ _ hj]
    exact h row[j] (Array.getElem_mem_toList hj)
  · rw [rowGet, array_getD_of_le' _ _ hj]

omit [LawfulBEq F] in
/-- Rows reading as zero in every coordinate are zero rows. -/
private theorem pm_rowIsZero_of_rowGet {row : PolynomialRow F}
    (h : ∀ j, rowGet row j = 0) : RowIsZero row := by
  intro p hp
  rcases List.getElem_of_mem hp with ⟨j, hj, hget⟩
  have hj' : j < row.size := by simpa using hj
  have hzero := h j
  rw [rowGet, array_getD_of_lt' _ _ hj'] at hzero
  rw [← hget, Array.getElem_toList]
  exact hzero

/-- Spans of all-zero row sets contain only zero rows. -/
private theorem pm_rowIsZero_of_mem_rowSpan_all_zero {X : PolynomialMatrix F}
    (hall : ∀ r ∈ MatrixRows X, RowIsZero r) {row : PolynomialRow F}
    (hrow : row ∈ RowSpan X) : RowIsZero row := by
  rcases hrow with ⟨coeffs, _hsize, rfl⟩
  refine pm_rowIsZero_of_rowGet fun j ↦ ?_
  rw [pm_rowGet_rowLinearCombination]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [pm_rowGet_eq_zero_of_rowIsZero
    (hall _ (getD_mem_matrixRows (Finset.mem_range.mp hi))) j, mul_zero]

/-- Span transfer for uniform-width matrices: nonzero span members move along
any row map that covers the nonzero source rows. -/
private theorem pm_mem_rowSpan_of_nonzero_rows_mem [DecidableEq F]
    {A B : PolynomialMatrix F} {n : Nat} (hn : 0 < n)
    (hA : ∀ r ∈ MatrixRows A, r.size = n)
    (hB : ∀ r ∈ MatrixRows B, r.size = n)
    (hrows : ∀ r ∈ MatrixRows A, ¬ RowIsZero r → r ∈ RowSpan B)
    {row : PolynomialRow F} (hrow : row ∈ RowSpan A) (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan B := by
  by_cases hallzero : ∀ r ∈ MatrixRows A, RowIsZero r
  · exact absurd (pm_rowIsZero_of_mem_rowSpan_all_zero hallzero hrow) hnz
  · have hex : ∃ r ∈ MatrixRows A, ¬ RowIsZero r := by
      by_contra hnot
      refine hallzero fun r hr ↦ ?_
      by_contra hz
      exact hnot ⟨r, hr, hz⟩
    rcases hex with ⟨r₀, hr₀mem, hr₀nz⟩
    have hr₀B := hrows r₀ hr₀mem hr₀nz
    have hBpos : 0 < B.size := by
      rcases Nat.eq_zero_or_pos B.size with h0 | hp
      · exfalso
        rw [Array.eq_empty_of_size_eq_zero h0] at hr₀B
        have hr₀empty := eq_empty_of_mem_rowSpan_empty hr₀B
        have := hA r₀ hr₀mem
        rw [hr₀empty] at this
        simp at this
        omega
      · exact hp
    have hApos : 0 < A.size := size_pos_of_mem_matrixRows hr₀mem
    have hwB : MatrixWidth B = n := matrixWidth_eq_of_first_row hBpos hB
    refine rowSpan_subset_of_rows_mem (wellFormed_of_sizes hB)
      ((matrixWidth_eq_of_first_row hApos hA).trans hwB.symm) ?_ hrow
    intro r hr
    by_cases hz : RowIsZero r
    · have hreq : r = zeroRow n := by
        rw [← hA r hr]
        exact rowIsZero_eq_zeroRow hz
      rw [hreq, ← hwB]
      exact zeroRow_mem_rowSpan (wellFormed_of_sizes hB)
    · exact hrows r hr hz

/-- Nonzero rows survive zero-row compaction. -/
private theorem pm_mem_matrixRows_compactNonzeroRows {X : PolynomialMatrix F}
    {r : PolynomialRow F} (hr : r ∈ MatrixRows X) (hnz : ¬ RowIsZero r) :
    r ∈ MatrixRows (compactNonzeroRows X) := by
  rw [MatrixRows, ← Array.mem_def] at hr ⊢
  rw [compactNonzeroRows, Array.mem_filter]
  refine ⟨hr, ?_⟩
  cases hb : rowIsZero r
  · rfl
  · exact absurd (rowIsZero_iff.1 hb) hnz

/-- Zero-row compaction keeps every nonzero span member. -/
private theorem pm_mem_rowSpan_compactNonzeroRows [DecidableEq F]
    {X : PolynomialMatrix F} {n : Nat} (hn : 0 < n)
    (hsizes : ∀ r ∈ MatrixRows X, r.size = n)
    {row : PolynomialRow F} (hrow : row ∈ RowSpan X) (hnz : ¬ RowIsZero row) :
    row ∈ RowSpan (compactNonzeroRows X) := by
  refine pm_mem_rowSpan_of_nonzero_rows_mem hn hsizes
    (fun r hr ↦ hsizes r (compactNonzeroRows_subset hr)) ?_ hrow hnz
  intro r hr hrnz
  exact matrix_row_mem_rowSpan
    (wellFormed_of_sizes fun s hs ↦ hsizes s (compactNonzeroRows_subset hs))
    (pm_mem_matrixRows_compactNonzeroRows hr hrnz)

/-- `toPoly` distinguishes canonical polynomials. -/
private theorem pm_eq_of_toPoly_eq {a b : CPolynomial F}
    (h : a.toPoly = b.toPoly) : a = b := by
  apply CPolynomial.eq_iff_coeff.2
  intro t
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, h]

/-- Column entries of a combination-by-matrix product as coefficient-weighted
sums of the row-by-matrix products. -/
private theorem pm_combination_mul_toPoly (mulCtx : CPolynomial.MulContext F)
    {P₁ M : PolynomialMatrix F} (q : PolynomialRow F) {j : Nat}
    (hj : j < MatrixWidth M) :
    (rowGet (rowMulMatrixWith mulCtx (rowLinearCombination q P₁) M) j).toPoly =
      ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
        (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) M) j).toPoly := by
  rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj]
  have hentry : ∀ k, (rowGet (rowLinearCombination q P₁) k).toPoly =
      ∑ l ∈ Finset.range P₁.size,
        (rowGet q l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly := by
    intro k
    rw [pm_rowGet_rowLinearCombination,
      pm_toPoly_finset_sum (fun l ↦ q.getD l 0 * rowGet (P₁.getD l #[]) k)
        P₁.size]
    refine Finset.sum_congr rfl fun l _hl ↦ ?_
    rw [CPolynomial.toPoly_mul]
    rfl
  calc ∑ k ∈ Finset.range M.size,
        (rowGet (rowLinearCombination q P₁) k).toPoly *
          (rowGet (M.getD k #[]) j).toPoly
      = ∑ k ∈ Finset.range M.size, ∑ l ∈ Finset.range P₁.size,
          (rowGet q l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly *
            (rowGet (M.getD k #[]) j).toPoly := by
        refine Finset.sum_congr rfl fun k _hk ↦ ?_
        rw [hentry k, Finset.sum_mul]
    _ = ∑ l ∈ Finset.range P₁.size, ∑ k ∈ Finset.range M.size,
          (rowGet q l).toPoly * (rowGet (P₁.getD l #[]) k).toPoly *
            (rowGet (M.getD k #[]) j).toPoly := Finset.sum_comm
    _ = ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
          (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) M) j).toPoly := by
        refine Finset.sum_congr rfl fun l _hl ↦ ?_
        rw [rowGet_rowMulMatrixWith_toPoly mulCtx _ M hj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _hk ↦ ?_
        ring

/-- Converse of the composition soundness step: the coefficient row of a
full-problem solution against a lower basis solves the residual problem. -/
private theorem pm_rowApproximates_residual_of_combination
    (mulCtx : CPolynomial.MulContext F)
    {problem : XAdicProblem F} {d₁ : Nat} {P₁ Rmat : PolynomialMatrix F}
    (hP₁ : ∀ r ∈ MatrixRows P₁,
      RowApproximates mulCtx
        { orders := lowerOrders problem d₁, matrix := problem.matrix } r ∧
      r.size = problem.matrix.size)
    (hRsize : Rmat.size = P₁.size)
    (hRwidth : MatrixWidth Rmat ≤ MatrixWidth problem.matrix)
    (hR : ∀ l j, l < P₁.size → j < problem.orders.size →
      j < MatrixWidth problem.matrix →
      ∀ t, t < problem.orders.getD j 0 - d₁ →
        CPolynomial.coeff (rowGet (Rmat.getD l #[]) j) t =
          CPolynomial.coeff
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[]) problem.matrix) j)
            (t + d₁))
    {q : PolynomialRow F}
    (happrox : RowApproximates mulCtx problem (rowLinearCombination q P₁)) :
    RowApproximates mulCtx
      { orders := residualOrders problem d₁, matrix := Rmat } q := by
  rw [rowApproximates_iff]
  intro j hj hjw
  have hj' : j < problem.orders.size := by
    simpa [residualOrders] using hj
  have hjwM : j < MatrixWidth problem.matrix := Nat.lt_of_lt_of_le hjw hRwidth
  set o := problem.orders.getD j 0 with ho
  have horder : (residualOrders problem d₁).getD j 0 = o - d₁ := by
    rw [residualOrders, natArray_map_getD _ _ hj']
  rw [horder]
  rcases Nat.le_total o d₁ with hod | hod
  · rw [Nat.sub_eq_zero_of_le hod, pow_zero]
    exact one_dvd _
  · rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | _hP₁0
    · rw [hRsize, hP₁0, Finset.range_zero, Finset.sum_empty]
      exact dvd_zero _
    · have hP₁dvd : ∀ l, l < P₁.size →
          (Polynomial.X : Polynomial F) ^ d₁ ∣
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
              problem.matrix) j).toPoly := by
        intro l hl
        have hmem := getD_mem_matrixRows hl
        have happroxl := (hP₁ _ hmem).1 j (by simpa [lowerOrders] using hj')
        rw [truncateX_eq_zero_iff_X_pow_dvd] at happroxl
        have horderl : (lowerOrders problem d₁).getD j 0 = min o d₁ := by
          rw [lowerOrders, natArray_map_getD _ _ hj']
        rwa [horderl, Nat.min_eq_right hod] at happroxl
      have hquot : ∀ l, ∃ sl : Polynomial F, l < P₁.size →
          (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
            problem.matrix) j).toPoly = Polynomial.X ^ d₁ * sl := by
        intro l
        by_cases hl : l < P₁.size
        · rcases hP₁dvd l hl with ⟨sl, hsl⟩
          exact ⟨sl, fun _ ↦ hsl⟩
        · exact ⟨0, fun h ↦ absurd h hl⟩
      choose s hs using hquot
      have hrowdvd : (Polynomial.X : Polynomial F) ^ o ∣
          ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
            (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
              problem.matrix) j).toPoly := by
        have h0 := (rowApproximates_iff mulCtx problem _).1 happrox j hj' hjwM
        rwa [← rowGet_rowMulMatrixWith_toPoly mulCtx _ problem.matrix hjwM,
          pm_combination_mul_toPoly mulCtx q hjwM] at h0
      have hsum : ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
          (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
            problem.matrix) j).toPoly =
          Polynomial.X ^ d₁ *
            ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly * s l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [hs l (Finset.mem_range.mp hl)]
        ring
      rw [hsum, show o = d₁ + (o - d₁) from by omega, pow_add] at hrowdvd
      have hquotsum : (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
          ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly * s l :=
        (mul_dvd_mul_iff_left (pow_ne_zero d₁ Polynomial.X_ne_zero)).1 hrowdvd
      have hcong : ∀ l, l < P₁.size →
          (Polynomial.X : Polynomial F) ^ (o - d₁) ∣
            (rowGet (Rmat.getD l #[]) j).toPoly - s l := by
        intro l hl
        rw [Polynomial.X_pow_dvd_iff]
        intro t ht
        rw [Polynomial.coeff_sub, ← CPolynomial.coeff_toPoly,
          hR l j hl hj' hjwM t (by omega), CPolynomial.coeff_toPoly]
        have hcoeff : ((rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
            problem.matrix) j).toPoly).coeff (t + d₁) =
            (Polynomial.X ^ d₁ * s l).coeff (t + d₁) := by
          rw [hs l hl]
        rw [Polynomial.coeff_X_pow_mul] at hcoeff
        rw [hcoeff]
        exact sub_self _
      have hfinal : ∑ k ∈ Finset.range Rmat.size, (rowGet q k).toPoly *
          (rowGet (Rmat.getD k #[]) j).toPoly =
          (∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly * s l) +
            ∑ l ∈ Finset.range P₁.size, (rowGet q l).toPoly *
              ((rowGet (Rmat.getD l #[]) j).toPoly - s l) := by
        rw [hRsize, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _hl ↦ ?_
        ring
      rw [hfinal]
      exact dvd_add hquotsum
        (Finset.dvd_sum fun l hl ↦
          Dvd.dvd.mul_left (hcong l (Finset.mem_range.mp hl)) _)

/-- Combinations against a basis of combinations are combinations against the
composed product matrix. -/
private theorem pm_rowLinearCombination_combination
    (mulCtx : CPolynomial.MulContext F)
    {P₁ P₂ : PolynomialMatrix F} {n : Nat}
    (hP₁pos : 0 < P₁.size) (hP₂pos : 0 < P₂.size)
    (hsizes : ∀ r ∈ MatrixRows P₁, r.size = n)
    (w : Array (CPolynomial F)) :
    rowLinearCombination (rowLinearCombination w P₂) P₁ =
      rowLinearCombination w (mulWith mulCtx P₂ P₁) := by
  have hw₁ : MatrixWidth P₁ = n := matrixWidth_eq_of_first_row hP₁pos hsizes
  have hCsize : (mulWith mulCtx P₂ P₁).size = P₂.size := mulWith_size mulCtx P₂ P₁
  have hCsizes : ∀ r ∈ MatrixRows (mulWith mulCtx P₂ P₁), r.size = n := by
    intro r hr
    rw [matrixRows_mulWith] at hr
    rcases List.mem_map.mp hr with ⟨p₂, _hp₂, rfl⟩
    rw [rowMulMatrixWith_size, hw₁]
  have hCw : MatrixWidth (mulWith mulCtx P₂ P₁) = n :=
    matrixWidth_eq_of_first_row (by omega) hCsizes
  refine pm_row_ext ?_ fun j ↦ ?_
  · rw [pm_rowLinearCombination_size hsizes hw₁,
      pm_rowLinearCombination_size hCsizes hCw]
  · rw [pm_rowGet_rowLinearCombination, pm_rowGet_rowLinearCombination, hCsize]
    rcases Nat.lt_or_ge j n with hj | hj
    · refine pm_eq_of_toPoly_eq ?_
      rw [pm_toPoly_finset_sum
        (fun l ↦ (rowLinearCombination w P₂).getD l 0 * rowGet (P₁.getD l #[]) j)
        P₁.size]
      rw [pm_toPoly_finset_sum
        (fun i ↦ w.getD i 0 * rowGet ((mulWith mulCtx P₂ P₁).getD i #[]) j)
        P₂.size]
      have hjw₁ : j < MatrixWidth P₁ := by omega
      calc ∑ l ∈ Finset.range P₁.size,
            ((rowLinearCombination w P₂).getD l 0 *
              rowGet (P₁.getD l #[]) j).toPoly
          = ∑ l ∈ Finset.range P₁.size, ∑ i ∈ Finset.range P₂.size,
              (w.getD i 0).toPoly * (rowGet (P₂.getD i #[]) l).toPoly *
                (rowGet (P₁.getD l #[]) j).toPoly := by
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            rw [CPolynomial.toPoly_mul]
            have hwl : ((rowLinearCombination w P₂).getD l 0).toPoly =
                ∑ i ∈ Finset.range P₂.size,
                  (w.getD i 0).toPoly * (rowGet (P₂.getD i #[]) l).toPoly := by
              rw [show (rowLinearCombination w P₂).getD l 0 =
                  rowGet (rowLinearCombination w P₂) l from rfl,
                pm_rowGet_rowLinearCombination,
                pm_toPoly_finset_sum
                  (fun i ↦ w.getD i 0 * rowGet (P₂.getD i #[]) l) P₂.size]
              refine Finset.sum_congr rfl fun i _hi ↦ ?_
              rw [CPolynomial.toPoly_mul]
            rw [hwl, Finset.sum_mul]
        _ = ∑ i ∈ Finset.range P₂.size, ∑ l ∈ Finset.range P₁.size,
              (w.getD i 0).toPoly * (rowGet (P₂.getD i #[]) l).toPoly *
                (rowGet (P₁.getD l #[]) j).toPoly := Finset.sum_comm
        _ = ∑ i ∈ Finset.range P₂.size,
              (w.getD i 0 * rowGet ((mulWith mulCtx P₂ P₁).getD i #[]) j).toPoly := by
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [CPolynomial.toPoly_mul,
              mulWith_getD mulCtx P₂ P₁ (Finset.mem_range.mp hi),
              rowGet_rowMulMatrixWith_toPoly mulCtx _ P₁ hjw₁, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _hl ↦ ?_
            ring
    · refine Eq.trans (Finset.sum_eq_zero fun l hl ↦ ?_)
        (Finset.sum_eq_zero fun i hi ↦ ?_).symm
      · have hzero : rowGet (P₁.getD l #[]) j = 0 := by
          rw [rowGet, array_getD_of_le' _ _ (by
            rw [hsizes _ (getD_mem_matrixRows (Finset.mem_range.mp hl))]
            omega)]
        rw [hzero, mul_zero]
      · have hi' : i < (mulWith mulCtx P₂ P₁).size := by
          rw [hCsize]
          exact Finset.mem_range.mp hi
        have hzero : rowGet ((mulWith mulCtx P₂ P₁).getD i #[]) j = 0 := by
          rw [rowGet, array_getD_of_le' _ _ (by
            rw [hCsizes _ (getD_mem_matrixRows hi')]
            omega)]
        rw [hzero, mul_zero]

/-- **Generation completeness of the recursive PM-basis core.**  Every nonzero
solution row of an X-adic problem lies in the row module generated by the
fuel-bounded recursive PM-basis core. -/
theorem pmBasisWithFuelCore_kernelLeaf_rowSpan_complete [DecidableEq F]
    (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) :
    ∀ (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat),
      0 < problem.matrix.size → WellFormed problem.matrix →
      ∀ row : PolynomialRow F, RowApproximates mulCtx problem row →
        row.size = problem.matrix.size → ¬ RowIsZero row →
        row ∈ RowSpan (pmBasisWithFuelCore
          (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
            composeLeafCutoff) fuel problem shift) := by
  intro fuel
  induction fuel with
  | zero =>
      intro problem shift hpos hwf row happrox hsize hnz
      rw [pmBasisWithFuelCore]
      exact pm_mem_rowSpan_compactNonzeroRows hpos
        (fun r hr ↦ (kernelLeafBasis_rows mulCtx problem shift r hr).2)
        (kernelLeafBasis_rowSpan_complete mulCtx problem shift hpos hwf
          happrox hsize hnz)
        hnz
  | succ fuel ih =>
      intro problem shift hpos hwf row happrox hsize hnz
      rw [pmBasisWithFuelCore]
      split
      · exact pm_mem_rowSpan_compactNonzeroRows hpos
          (fun r hr ↦ (kernelLeafBasis_rows mulCtx problem shift r hr).2)
          (kernelLeafBasis_rowSpan_complete mulCtx problem shift hpos hwf
            happrox hsize hnz)
          hnz
      · set d₁ := maxOrder problem / 2 with hd₁
        set lower : XAdicProblem F :=
          { orders := lowerOrders problem d₁, matrix := problem.matrix }
          with hlower
        set P₁ := pmBasisWithFuelCore
          (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
            composeLeafCutoff) fuel lower shift with hP₁def
        set resOrders := residualOrders problem d₁ with hresOrders
        set Rmat := residualMatrixWithProduct
          (mulTruncColumnStrassenWith lowCtx composeLeafCutoff) P₁
          problem.matrix d₁ resOrders with hRmatdef
        set residual : XAdicProblem F :=
          { orders := resOrders, matrix := Rmat } with hresidual
        set shifted := updateShiftByRows P₁ shift with hshifted
        set P₂ := pmBasisWithFuelCore
          (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
            composeLeafCutoff) fuel residual shifted with hP₂def
        have hIH₁ : ∀ r ∈ MatrixRows P₁,
            RowApproximates mulCtx lower r ∧ r.size = problem.matrix.size :=
          fun r hr ↦ pmBasisWithFuelCore_kernelLeaf_rows mulCtx lowCtx
            leafCutoff composeLeafCutoff fuel lower shift r hr
        -- The row solves the lower-order problem.
        have hlowapprox : RowApproximates mulCtx lower row := by
          rw [rowApproximates_iff] at happrox ⊢
          intro j hj hjw
          have hj' : j < problem.orders.size := by
            simpa [hlower, lowerOrders] using hj
          refine dvd_trans (pow_dvd_pow _ ?_) (happrox j hj' hjw)
          have horder : (lowerOrders problem d₁).getD j 0 =
              min (problem.orders.getD j 0) d₁ := by
            rw [lowerOrders, natArray_map_getD _ _ hj']
          rw [hlower]
          simp only [horder]
          omega
        have hrow₁ : row ∈ RowSpan P₁ :=
          ih lower shift hpos hwf row hlowapprox hsize hnz
        rcases Nat.eq_zero_or_pos P₁.size with hP₁0 | hP₁0
        · exfalso
          rw [Array.eq_empty_of_size_eq_zero hP₁0] at hrow₁
          have hempty := eq_empty_of_mem_rowSpan_empty hrow₁
          rw [hempty] at hsize
          simp at hsize
          omega
        · rcases hrow₁ with ⟨q, hqsize, hqeq⟩
          -- Shape facts for the residual matrix.
          have hprodsize : (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
              (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix).size =
                P₁.size := mulTruncColumnStrassenWith_size _ _ _ _ _
          have hRsize : Rmat.size = P₁.size := by
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [ofFn_size, hprodsize]
          have hprodwidth :
              MatrixWidth (mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                (resOrders.map fun order ↦ order + d₁) P₁ problem.matrix) =
                MatrixWidth problem.matrix := by
            rw [mulTruncColumnStrassenWith_eq_truncateColumns]
            refine matrixWidth_eq_of_first_row
              (by rw [truncateColumns_size, mulWith_size]; omega) ?_
            intro r hr
            rw [MatrixRows, truncateColumns, Array.toList_map] at hr
            rcases List.mem_map.mp hr with ⟨r', hr', rfl⟩
            have hsize' : (rowTruncateColumns
                (resOrders.map fun order ↦ order + d₁) r').size = r'.size := by
              simp [rowTruncateColumns]
            rw [hsize']
            have hr'' : r' ∈ (MatrixRows P₁).map fun r ↦
                rowMulMatrixWith lowCtx.mulContext r problem.matrix := by
              rw [← matrixRows_mulWith]
              exact hr'
            rcases List.mem_map.mp hr'' with ⟨r'', _hr'', rfl⟩
            rw [rowMulMatrixWith_size]
          have hRwidth : MatrixWidth Rmat = MatrixWidth problem.matrix := by
            rw [hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [MatrixWidth_ofFn, if_neg (by omega), hprodwidth]
          have hRcong : ∀ l j, l < P₁.size → j < problem.orders.size →
              j < MatrixWidth problem.matrix →
              ∀ t, t < problem.orders.getD j 0 - d₁ →
                CPolynomial.coeff (rowGet (Rmat.getD l #[]) j) t =
                  CPolynomial.coeff
                    (rowGet (rowMulMatrixWith mulCtx (P₁.getD l #[])
                      problem.matrix) j) (t + d₁) := by
            intro l j hl hj hjw t ht
            have hd₁lt : d₁ < problem.orders.getD j 0 := by omega
            have hjres : j < resOrders.size := by
              rw [hresOrders, residualOrders]
              simpa using hj
            have hRentry : rowGet (Rmat.getD l #[]) j =
                divXTrunc d₁ (resOrders.getD j 0)
                  (rowGet ((mulTruncColumnStrassenWith lowCtx composeLeafCutoff
                    (resOrders.map fun order ↦ order + d₁) P₁
                    problem.matrix).getD l #[]) j) := by
              rw [hRmatdef]
              simp only [residualMatrixWithProduct]
              rw [rowGet_ofFn, if_pos ⟨by rw [hprodsize]; exact hl,
                by rw [hprodwidth]; exact hjw⟩]
            rw [hRentry, divXTrunc_coeff,
              if_pos (by rw [hresOrders, residualOrders,
                natArray_map_getD _ _ hj]; omega)]
            rw [mulTruncColumnStrassenWith_entry lowCtx composeLeafCutoff _ P₁
              problem.matrix (by omega) j]
            rw [truncateX_coeff, if_pos (by
              rw [natArray_map_getD _ _ hjres, hresOrders, residualOrders,
                natArray_map_getD _ _ hj]
              omega)]
            rw [rowMulMatrixWith_ctx lowCtx.mulContext mulCtx]
          -- The combination coefficients are nonzero and solve the residual.
          have hq_nz : ¬ RowIsZero q := by
            intro hqz
            apply hnz
            rw [hqeq]
            refine pm_rowIsZero_of_rowGet fun j ↦ ?_
            rw [pm_rowGet_rowLinearCombination]
            refine Finset.sum_eq_zero fun i _hi ↦ ?_
            rw [show q.getD i 0 = rowGet q i from rfl,
              pm_rowGet_eq_zero_of_rowIsZero hqz, zero_mul]
          have hqapprox : RowApproximates mulCtx residual q := by
            rw [hresidual, hresOrders]
            refine pm_rowApproximates_residual_of_combination mulCtx hIH₁
              hRsize (le_of_eq hRwidth) hRcong ?_
            rw [← hqeq]
            exact happrox
          have hwf_R : WellFormed Rmat := by
            refine wellFormed_of_sizes
              (n := MatrixWidth (mulTruncColumnStrassenWith lowCtx
                composeLeafCutoff (resOrders.map fun order ↦ order + d₁) P₁
                problem.matrix)) ?_
            intro r hr
            rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
            have hi' : i < Rmat.size := by simpa [MatrixRows] using hi
            have hr_eq : Rmat.getD i #[] = r := by
              rw [array_getD_of_lt' _ _ hi', ← Array.getElem_toList]
              exact hget
            rw [← hr_eq, hRmatdef]
            simp only [residualMatrixWithProduct]
            rw [getD_ofFn, if_pos (by
              rw [hRmatdef] at hi'
              simpa [residualMatrixWithProduct, ofFn_size] using hi')]
            simp
          have hRpos : 0 < Rmat.size := by omega
          have hq_size : q.size = Rmat.size := by omega
          have hrow₂ : q ∈ RowSpan P₂ :=
            ih residual shifted hRpos hwf_R q hqapprox hq_size hq_nz
          rcases hrow₂ with ⟨w, hwsize, hweq⟩
          have hP₂pos : 0 < P₂.size := by
            rcases Nat.eq_zero_or_pos P₂.size with h0 | hp
            · exfalso
              rw [Array.eq_empty_of_size_eq_zero h0] at hweq
              have hqempty : q = #[] := by
                rw [hweq, rowLinearCombination]
                rfl
              rw [hqempty] at hq_nz
              exact hq_nz rowIsZero_empty
            · exact hp
          -- Compose the two combinations through the product basis.
          have hdistrib : row =
              rowLinearCombination w (mulWith lowCtx.mulContext P₂ P₁) := by
            rw [hqeq, hweq]
            exact pm_rowLinearCombination_combination lowCtx.mulContext hP₁0
              hP₂pos (fun r hr ↦ (hIH₁ r hr).2) w
          have hfinal : row ∈ RowSpan (compactNonzeroRows
              (mulStrassenWith lowCtx composeLeafCutoff P₂ P₁)) := by
            rw [mulStrassenWith_eq_mulWith]
            refine pm_mem_rowSpan_compactNonzeroRows hpos ?_ ?_ hnz
            · intro r hr
              rw [matrixRows_mulWith] at hr
              rcases List.mem_map.mp hr with ⟨p₂, _hp₂, rfl⟩
              rw [rowMulMatrixWith_size,
                matrixWidth_eq_of_first_row hP₁0 fun r hr ↦ (hIH₁ r hr).2]
            · exact ⟨w, by rw [mulWith_size]; omega, hdistrib⟩
          exact hfinal

/-! ## Root normalization shape and shifted minimality -/

omit [BEq F] [LawfulBEq F] in
/-- Zero padding on the right does not change row reads. -/
private theorem pm_rowGet_append_replicate (row : PolynomialRow F)
    (m k : Nat) :
    rowGet (row ++ Array.replicate m (0 : CPolynomial F)) k = rowGet row k := by
  rcases Nat.lt_or_ge k row.size with hk | hk
  · rw [rowGet, rowGet, pm_append_getD_left _ hk]
  · rw [rowGet, rowGet, pm_append_getD_right _ hk, array_getD_of_le' _ _ hk]
    rcases Nat.lt_or_ge (k - row.size) m with h | h
    · rw [array_getD_of_lt' _ _ (by simpa using h), Array.getElem_replicate]
    · rw [array_getD_of_le' _ _ (by simpa using h)]

/-- Zero padding preserves the X-adic approximant conditions. -/
private theorem pm_rowApproximates_append_replicate
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    {row : PolynomialRow F} (m : Nat)
    (h : RowApproximates mulCtx problem row) :
    RowApproximates mulCtx problem
      (row ++ Array.replicate m (0 : CPolynomial F)) := by
  rw [rowApproximates_iff] at h ⊢
  intro j hj hjw
  have hsum : ∑ k ∈ Finset.range problem.matrix.size,
      (rowGet (row ++ Array.replicate m (0 : CPolynomial F)) k).toPoly *
        (rowGet (problem.matrix.getD k #[]) j).toPoly =
      ∑ k ∈ Finset.range problem.matrix.size,
        (rowGet row k).toPoly * (rowGet (problem.matrix.getD k #[]) j).toPoly :=
    Finset.sum_congr rfl fun k _hk ↦ by rw [pm_rowGet_append_replicate]
  rw [hsum]
  exact h j hj hjw

/-- Coordinates reading zero contribute no shifted entry degree. -/
private theorem pm_shiftedEntryDegree_eq_none_of_rowGet_eq_zero
    {row : PolynomialRow F} {shift : Array Nat} {j : Nat}
    (h : rowGet row j = 0) : shiftedEntryDegree? row shift j = none := by
  simp [shiftedEntryDegree?, h]

omit [LawfulBEq F] in
/-- Shifted entry degrees only depend on row reads. -/
private theorem pm_shiftedEntryDegree_congr {row row' : PolynomialRow F}
    {shift : Array Nat} {j : Nat} (h : rowGet row' j = rowGet row j) :
    shiftedEntryDegree? row' shift j = shiftedEntryDegree? row shift j := by
  simp only [shiftedEntryDegree?, h]

/-- Zero padding preserves the shifted row degree. -/
private theorem pm_rowShiftedDegree_append_replicate (row : PolynomialRow F)
    (shift : Array Nat) (m : Nat) :
    rowShiftedDegree? (row ++ Array.replicate m (0 : CPolynomial F)) shift =
      rowShiftedDegree? row shift := by
  set row' := row ++ Array.replicate m (0 : CPolynomial F) with hrow'
  have hget : ∀ j, rowGet row' j = rowGet row j :=
    pm_rowGet_append_replicate row m
  have hentry : ∀ j,
      shiftedEntryDegree? row' shift j = shiftedEntryDegree? row shift j :=
    fun j ↦ pm_shiftedEntryDegree_congr (hget j)
  have hzero_iff : RowIsZero row' ↔ RowIsZero row := by
    constructor
    · intro h
      refine pm_rowIsZero_of_rowGet fun j ↦ ?_
      rw [← hget j]
      exact pm_rowGet_eq_zero_of_rowIsZero h j
    · intro h
      refine pm_rowIsZero_of_rowGet fun j ↦ ?_
      rw [hget j]
      exact pm_rowGet_eq_zero_of_rowIsZero h j
  cases hd : rowShiftedDegree? row shift with
  | none =>
      rw [rowShiftedDegree?_eq_none_iff] at hd ⊢
      exact hzero_iff.mpr hd
  | some d =>
      cases hd' : rowShiftedDegree? row' shift with
      | none =>
          exfalso
          rw [rowShiftedDegree?_eq_none_iff] at hd'
          have hnone : rowShiftedDegree? row shift = none :=
            rowShiftedDegree?_eq_none_iff.2 (hzero_iff.mp hd')
          rw [hd] at hnone
          cases hnone
      | some d' =>
          rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hd
            with ⟨j, hj, hej⟩
          rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hd'
            with ⟨j', hj', hej'⟩
          have hj'row : j' < row.size := by
            by_contra hge
            have hzero : rowGet row j' = 0 := by
              rw [rowGet, array_getD_of_le' _ _ (by omega)]
            rw [hentry j',
              pm_shiftedEntryDegree_eq_none_of_rowGet_eq_zero hzero] at hej'
            cases hej'
          have h1 : d' ≤ d :=
            shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hd hj'row
              (by rw [← hentry j']; exact hej')
          have hsize' : row'.size = row.size + m := by
            rw [hrow']
            simp
          have h2 : d ≤ d' :=
            shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some (j := j) hd'
              (by omega) (by rw [hentry j]; exact hej)
          exact congrArg some (by omega)

/-- High monomial coefficients are nonzero. -/
private theorem pm_coeffXPower_one_ne_zero (d : Nat) :
    coeffXPower (1 : F) d ≠ 0 := by
  intro h
  have hcoeff : CPolynomial.coeff (coeffXPower (1 : F) d) d = 1 := by
    rw [CPolynomial.coeff_toPoly, coeffXPower_toPoly, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  rw [h, CPolynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

/-- Degree of a high monomial coefficient. -/
private theorem pm_coeffXPower_one_natDegree (d : Nat) :
    (coeffXPower (1 : F) d).natDegree = d := by
  rw [CPolynomial.natDegree_toPoly, coeffXPower_toPoly, Polynomial.C_1,
    one_mul, Polynomial.natDegree_X_pow]

/-- Diagonal shifted entry degree of a monomial unit row. -/
private theorem pm_shiftedEntryDegree_monomialUnitRow_self {n i : Nat}
    (cap : Nat) (shift : Array Nat) (hi : i < n) :
    shiftedEntryDegree? (monomialUnitRow (F := F) n i cap) shift i =
      some (cap + shift.getD i 0) := by
  have hget : rowGet (monomialUnitRow (F := F) n i cap) i =
      coeffXPower 1 cap := by
    rw [pm_rowGet_monomialUnitRow, if_pos ⟨hi, rfl⟩]
  rw [shiftedEntryDegree?_eq_some_of_rowGet_ne_zero (by
      rw [hget]
      exact pm_coeffXPower_one_ne_zero cap),
    hget, pm_coeffXPower_one_natDegree]

/-- Off-diagonal shifted entry degrees of a monomial unit row are undefined. -/
private theorem pm_shiftedEntryDegree_monomialUnitRow_ne {n i j : Nat}
    (cap : Nat) (shift : Array Nat) (hij : i ≠ j) :
    shiftedEntryDegree? (monomialUnitRow (F := F) n i cap) shift j = none := by
  refine pm_shiftedEntryDegree_eq_none_of_rowGet_eq_zero ?_
  rw [pm_rowGet_monomialUnitRow, if_neg fun h ↦ hij h.2]

/-- Shifted row degree of a monomial unit row. -/
private theorem pm_rowShiftedDegree_monomialUnitRow {n i : Nat} (cap : Nat)
    (shift : Array Nat) (hi : i < n) :
    rowShiftedDegree? (monomialUnitRow (F := F) n i cap) shift =
      some (cap + shift.getD i 0) := by
  cases hd : rowShiftedDegree? (monomialUnitRow (F := F) n i cap) shift with
  | none =>
      exfalso
      have hz := rowShiftedDegree?_eq_none_iff.1 hd
      have hzero := pm_rowGet_eq_zero_of_rowIsZero hz i
      rw [pm_rowGet_monomialUnitRow, if_pos ⟨hi, rfl⟩] at hzero
      exact pm_coeffXPower_one_ne_zero cap hzero
  | some d =>
      rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hd
        with ⟨j, hj, hej⟩
      rcases eq_or_ne i j with rfl | hij
      · rw [pm_shiftedEntryDegree_monomialUnitRow_self cap shift hi] at hej
        rw [← hej]
      · rw [pm_shiftedEntryDegree_monomialUnitRow_ne cap shift hij] at hej
        cases hej

/-- Shifted leading position of a monomial unit row. -/
private theorem pm_rowShiftedLeadingPosition_monomialUnitRow [DecidableEq F]
    {n i : Nat} (cap : Nat) (shift : Array Nat) (hi : i < n) :
    rowShiftedLeadingPosition? (monomialUnitRow (F := F) n i cap) shift =
      some i := by
  have hdeg := pm_rowShiftedDegree_monomialUnitRow (F := F) cap shift hi
  rcases rowShiftedLeadingPosition?_some_of_degree hdeg with ⟨pos, hpos⟩
  have hentry := rowShiftedLeadingPosition?_entry_eq hdeg hpos
  rcases eq_or_ne i pos with rfl | hne
  · exact hpos
  · rw [pm_shiftedEntryDegree_monomialUnitRow_ne cap shift hne] at hentry
    cases hentry

omit [LawfulBEq F] in
/-- Stored rows witness their shifted leading position in the row set. -/
private theorem pm_rowsContainLeadingPosition_of_getD
    {rows : PolynomialMatrix F} {shift : Array Nat} {i p : Nat}
    (hi : i < rows.size)
    (hpos : rowShiftedLeadingPosition? (rows.getD i #[]) shift = some p) :
    rowsContainLeadingPosition rows shift p = true := by
  rw [rowsContainLeadingPosition, Array.any_eq_true]
  refine ⟨i, hi, ?_⟩
  rw [← array_getD_of_lt' rows #[] hi, hpos]
  exact beq_self_eq_true p

omit [LawfulBEq F] in
/-- Pivot tables whose slots store their own leading positions extract to
shifted weak-Popov row sets. -/
private theorem pm_pivotRows_shiftedWeakPopov
    {pivots : Array (Option (PolynomialRow F))} {shift : Array Nat}
    (hinv : ∀ p r, pivots.getD p none = some r →
      rowShiftedLeadingPosition? r shift = some p) :
    ShiftedWeakPopov (pivotRows pivots) shift := by
  have hpair : (pivots.toList.filterMap id).Pairwise
      (fun a b ↦ rowShiftedLeadingPosition? a shift ≠
        rowShiftedLeadingPosition? b shift) := by
    rw [List.pairwise_filterMap, List.pairwise_iff_getElem]
    intro u v hu hv huv b hb b' hb'
    have hu' : u < pivots.size := by simpa using hu
    have hv' : v < pivots.size := by simpa using hv
    have hbu : pivots.getD u none = some b := by
      rw [array_getD_of_lt' _ _ hu', ← Array.getElem_toList]
      exact hb
    have hbv : pivots.getD v none = some b' := by
      rw [array_getD_of_lt' _ _ hv', ← Array.getElem_toList]
      exact hb'
    rw [hinv u b hbu, hinv v b' hbv]
    intro hcontra
    cases hcontra
    omega
  rw [List.pairwise_iff_getElem] at hpair
  have hsz : (pivotRows pivots).size = (pivots.toList.filterMap id).length := by
    rw [pivotRows]
    simp
  have hget : ∀ k, k < (pivotRows pivots).size →
      ∀ hk : k < (pivots.toList.filterMap id).length,
      (pivotRows pivots).getD k #[] = (pivots.toList.filterMap id)[k] := by
    intro k hk hk'
    rw [pivotRows, array_getD_of_lt' _ _ (by simpa using hk'),
      List.getElem_toArray]
  intro i j hi hj hij hpi hpj
  rcases Nat.lt_or_ge i j with h | h
  · rw [hget i hi (by omega), hget j hj (by omega)]
    exact hpair i j (by omega) (by omega) h
  · have hji : j < i := by omega
    rw [hget i hi (by omega), hget j hj (by omega)]
    exact (hpair j i (by omega) (by omega) hji).symm

/-- Per-row shape facts for the missing-pivot completion rows. -/
private theorem pm_missingCompletionRows_facts [DecidableEq F]
    (problem : XAdicProblem F) (shift : Array Nat) (rows : PolynomialMatrix F)
    {k : Nat} (hk : k < (missingCompletionRows problem shift rows).size) :
    ∃ i, i < problem.matrix.size ∧
      rowShiftedLeadingPosition?
        ((missingCompletionRows problem shift rows).getD k #[]) shift =
          some i ∧
      rowsContainLeadingPosition rows shift i = false := by
  have hmem : (missingCompletionRows problem shift rows).getD k #[] ∈
      (List.range problem.matrix.size).filterMap (fun i ↦
        if rowsContainLeadingPosition rows shift i then none
        else some (monomialUnitRow problem.matrix.size i
          (leafDegreeCap problem))) := by
    rw [missingCompletionRows] at hk ⊢
    rw [array_getD_of_lt' _ _ hk, List.getElem_toArray]
    exact List.getElem_mem _
  rcases List.mem_filterMap.mp hmem with ⟨i, hi, hg⟩
  rw [List.mem_range] at hi
  by_cases hc : rowsContainLeadingPosition rows shift i
  · rw [if_pos hc] at hg
    cases hg
  · rw [if_neg hc] at hg
    refine ⟨i, hi, ?_, by simpa using hc⟩
    rw [← Option.some.inj hg]
    exact pm_rowShiftedLeadingPosition_monomialUnitRow
      (leafDegreeCap problem) shift hi

/-- Distinct missing-pivot completion rows have distinct shifted leading
positions. -/
private theorem pm_missingCompletionRows_pairwise [DecidableEq F]
    (problem : XAdicProblem F) (shift : Array Nat) (rows : PolynomialMatrix F)
    {k k' : Nat} (hk : k < (missingCompletionRows problem shift rows).size)
    (hk' : k' < (missingCompletionRows problem shift rows).size)
    (hkk : k < k') :
    rowShiftedLeadingPosition?
        ((missingCompletionRows problem shift rows).getD k #[]) shift ≠
      rowShiftedLeadingPosition?
        ((missingCompletionRows problem shift rows).getD k' #[]) shift := by
  have hmlist : missingCompletionRows problem shift rows =
      ((List.range problem.matrix.size).filterMap (fun i ↦
        if rowsContainLeadingPosition rows shift i then none
        else some (monomialUnitRow problem.matrix.size i
          (leafDegreeCap problem)))).toArray := by
    simp only [missingCompletionRows]
  have hpair : ((List.range problem.matrix.size).filterMap (fun i ↦
      if rowsContainLeadingPosition rows shift i then none
      else some (monomialUnitRow (F := F) problem.matrix.size i
        (leafDegreeCap problem)))).Pairwise
      (fun a b ↦ rowShiftedLeadingPosition? a shift ≠
        rowShiftedLeadingPosition? b shift) := by
    rw [List.pairwise_filterMap, List.pairwise_iff_getElem]
    intro u v hu hv huv b hb b' hb'
    have hu' : u < problem.matrix.size := by simpa using hu
    have hv' : v < problem.matrix.size := by simpa using hv
    simp only [List.getElem_range] at hb hb'
    have hbpos : rowShiftedLeadingPosition? b shift = some u := by
      by_cases hc : rowsContainLeadingPosition rows shift u
      · rw [if_pos hc] at hb
        cases hb
      · rw [if_neg hc] at hb
        rw [← Option.some.inj hb]
        exact pm_rowShiftedLeadingPosition_monomialUnitRow
          (leafDegreeCap problem) shift hu'
    have hbpos' : rowShiftedLeadingPosition? b' shift = some v := by
      by_cases hc : rowsContainLeadingPosition rows shift v
      · rw [if_pos hc] at hb'
        cases hb'
      · rw [if_neg hc] at hb'
        rw [← Option.some.inj hb']
        exact pm_rowShiftedLeadingPosition_monomialUnitRow
          (leafDegreeCap problem) shift hv'
    rw [hbpos, hbpos']
    intro hcontra
    cases hcontra
    omega
  rw [List.pairwise_iff_getElem] at hpair
  rw [hmlist] at hk hk' ⊢
  have hk_len : k < ((List.range problem.matrix.size).filterMap (fun i ↦
      if rowsContainLeadingPosition rows shift i then none
      else some (monomialUnitRow (F := F) problem.matrix.size i
        (leafDegreeCap problem)))).length := by
    simpa using hk
  have hk'_len : k' < ((List.range problem.matrix.size).filterMap (fun i ↦
      if rowsContainLeadingPosition rows shift i then none
      else some (monomialUnitRow (F := F) problem.matrix.size i
        (leafDegreeCap problem)))).length := by
    simpa using hk'
  rw [array_getD_of_lt' _ _ hk, array_getD_of_lt' _ _ hk',
    List.getElem_toArray, List.getElem_toArray]
  exact hpair k k' hk_len hk'_len hkk

/-- Missing-pivot completion preserves the shifted weak-Popov property. -/
private theorem pm_completeMissingPivotRows_shiftedWeakPopov [DecidableEq F]
    (problem : XAdicProblem F) (shift : Array Nat) {rows : PolynomialMatrix F}
    (hwp : ShiftedWeakPopov rows shift) :
    ShiftedWeakPopov (completeMissingPivotRows problem shift rows) shift := by
  intro i j hi hj hij hpi hpj
  rw [completeMissingPivotRows, Array.size_append] at hi hj
  rw [completeMissingPivotRows] at hpi hpj ⊢
  rcases Nat.lt_or_ge i rows.size with hi' | hi' <;>
    rcases Nat.lt_or_ge j rows.size with hj' | hj'
  · rw [pm_append_getD_left _ hi'] at hpi
    rw [pm_append_getD_left _ hj'] at hpj
    rw [pm_append_getD_left _ hi', pm_append_getD_left _ hj']
    exact hwp i j hi' hj' hij hpi hpj
  · rw [pm_append_getD_left _ hi'] at hpi ⊢
    rw [pm_append_getD_right _ hj'] at hpj ⊢
    cases hp : rowShiftedLeadingPosition? (rows.getD i #[]) shift with
    | none => exact absurd hp hpi
    | some p =>
        rcases pm_missingCompletionRows_facts problem shift rows
          (k := j - rows.size) (by omega) with ⟨im, _him, hposm, hcontm⟩
        rw [hposm]
        intro heq
        cases Option.some.inj heq
        have htrue := pm_rowsContainLeadingPosition_of_getD hi' hp
        rw [hcontm] at htrue
        cases htrue
  · rw [pm_append_getD_left _ hj'] at hpj ⊢
    rw [pm_append_getD_right _ hi'] at hpi ⊢
    cases hp : rowShiftedLeadingPosition? (rows.getD j #[]) shift with
    | none => exact absurd hp hpj
    | some p =>
        rcases pm_missingCompletionRows_facts problem shift rows
          (k := i - rows.size) (by omega) with ⟨im, _him, hposm, hcontm⟩
        rw [hposm]
        intro heq
        cases Option.some.inj heq
        have htrue := pm_rowsContainLeadingPosition_of_getD hj' hp
        rw [hcontm] at htrue
        cases htrue
  · rw [pm_append_getD_right _ hi', pm_append_getD_right _ hj']
    have hki : i - rows.size < (missingCompletionRows problem shift rows).size :=
      by omega
    have hkj : j - rows.size < (missingCompletionRows problem shift rows).size :=
      by omega
    rcases Nat.lt_or_ge (i - rows.size) (j - rows.size) with h | h
    · exact pm_missingCompletionRows_pairwise problem shift rows hki hkj h
    · have hlt : j - rows.size < i - rows.size := by omega
      exact (pm_missingCompletionRows_pairwise problem shift rows hkj hki
        hlt).symm

/-- **Shifted minimality of the recursive PM-basis.**  Every nonzero X-adic
solution row is shifted-degree dominated by some row of the root-normalized
recursive PM-basis. -/
theorem pmBasis_kernelLeaf_complete_minimal [DecidableEq F]
    (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat)
    (problem : XAdicProblem F) (shift : Array Nat) (row : PolynomialRow F)
    (hpos : 0 < problem.matrix.size) (hwf : WellFormed problem.matrix)
    (happrox : RowApproximates mulCtx problem row)
    (hnz : rowIsZero row = false) (hwidth : row.size ≤ problem.matrix.size) :
    ∃ basisRow degree,
      basisRow ∈ MatrixRows (pmBasis
        (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
          composeLeafCutoff) problem shift) ∧
      basisRow.size ≤ problem.matrix.size ∧
      rowShiftedDegree? basisRow shift = some degree ∧
      ∀ rowDegree, rowShiftedDegree? row shift = some rowDegree →
        degree ≤ rowDegree := by
  set n := problem.matrix.size with hn
  set runtime := kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
    composeLeafCutoff with hruntime
  -- Pad the solution row to the principal width.
  set row' := row ++ Array.replicate (n - row.size) (0 : CPolynomial F)
    with hrow'
  have hrow'size : row'.size = n := by
    rw [hrow']
    simp
    omega
  have hrownz : ¬ RowIsZero row := by
    intro h
    rw [← rowIsZero_iff, hnz] at h
    cases h
  have hrow'nz : ¬ RowIsZero row' := by
    intro h
    refine hrownz fun p hp ↦ h p ?_
    rw [hrow', Array.toList_append]
    exact List.mem_append.mpr (Or.inl hp)
  have hrow'approx : RowApproximates mulCtx problem row' :=
    pm_rowApproximates_append_replicate mulCtx problem (n - row.size) happrox
  have hrow'deg : rowShiftedDegree? row' shift = rowShiftedDegree? row shift :=
    pm_rowShiftedDegree_append_replicate row shift (n - row.size)
  -- The padded row lies in the span of the recursive core.
  set core := pmBasisWithFuelCore runtime (pmBasisFuel problem) problem shift
    with hcore
  have hcoresizes : ∀ r ∈ MatrixRows core, r.size = n :=
    fun r hr ↦ (pmBasisWithFuelCore_kernelLeaf_rows mulCtx lowCtx leafCutoff
      composeLeafCutoff (pmBasisFuel problem) problem shift r hr).2
  have hrow'span : row' ∈ RowSpan core :=
    pmBasisWithFuelCore_kernelLeaf_rowSpan_complete mulCtx lowCtx leafCutoff
      composeLeafCutoff (pmBasisFuel problem) problem shift hpos hwf row'
      hrow'approx hrow'size hrow'nz
  -- Lift the span through the root pivot reduction.
  set red := reduceKernelLeafRowsByPivots core shift with hred
  have hred_rows : ∀ r ∈ MatrixRows red, r.size = n ∧ rowIsZero r = false :=
    reduceKernelLeafRowsByPivots_rows hcoresizes
  have hrow'red : row' ∈ RowSpan red :=
    pm_mem_rowSpan_of_nonzero_rows_mem hpos hcoresizes
      (fun r hr ↦ (hred_rows r hr).1)
      (fun r hr hrnz ↦
        reduceKernelLeafRowsByPivots_rowSpan_superset hcoresizes hr hrnz)
      hrow'span hrow'nz
  have hcmp_eq : compactNonzeroRows red = red := by
    rw [compactNonzeroRows, Array.filter_eq_self]
    intro r hr
    rw [(hred_rows r (by rw [MatrixRows, ← Array.mem_def]; exact hr)).2]
    rfl
  -- The final basis is the completed reduction.
  have hbasis_eq : pmBasis runtime problem shift =
      completeMissingPivotRows problem shift red := by
    rw [pmBasis, pmBasisWithFuel, pmBasisNormalizeRoot, reduceKernelLeafRows,
      ← hcore, ← hred, hcmp_eq]
  have hfinsizes : ∀ r ∈ MatrixRows (completeMissingPivotRows problem shift
      red), r.size = n := by
    intro r hr
    rw [completeMissingPivotRows, MatrixRows, Array.toList_append] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hred_rows r hr).1
    · rw [missingCompletionRows, List.toList_toArray] at hr
      rcases List.mem_filterMap.mp hr with ⟨i, _hi, hg⟩
      by_cases hc : rowsContainLeadingPosition red shift i
      · rw [if_pos hc] at hg
        cases hg
      · rw [if_neg hc] at hg
        rw [← Option.some.inj hg, hn]
        simp [monomialUnitRow]
  have hrow'fin : row' ∈ RowSpan (completeMissingPivotRows problem shift
      red) := by
    refine pm_mem_rowSpan_of_nonzero_rows_mem hpos
      (fun r hr ↦ (hred_rows r hr).1) hfinsizes ?_ hrow'red hrow'nz
    intro r hr _hrnz
    refine matrix_row_mem_rowSpan (wellFormed_of_sizes hfinsizes) ?_
    rw [completeMissingPivotRows, MatrixRows, Array.toList_append]
    exact List.mem_append.mpr (Or.inl hr)
  -- The completed reduction is shifted weak-Popov.
  have hwp_red : ShiftedWeakPopov red shift := by
    have hred_eq : red = pivotRows (core.toList.foldl
        (fun pivots row ↦ insertKernelLeafPivotRowWithFuel
          (reduceKernelLeafFuel core shift) pivots shift row)
        (Array.replicate (MatrixWidth core) none)) := by
      rw [hred, reduceKernelLeafRowsByPivots, ← Array.foldl_toList]
    rw [hred_eq]
    refine pm_pivotRows_shiftedWeakPopov fun p r hget ↦ ?_
    have hinit : ∀ p r,
        (Array.replicate (MatrixWidth core)
          (none : Option (PolynomialRow F))).getD p none = some r →
        r.size = n ∧ rowShiftedLeadingPosition? r shift = some p := by
      intro p r hget
      rcases Nat.lt_or_ge p
          (Array.replicate (MatrixWidth core)
            (none : Option (PolynomialRow F))).size with hp | hp
      · rw [array_getD_of_lt' _ _ hp, Array.getElem_replicate] at hget
        cases hget
      · rw [array_getD_of_le' _ _ hp] at hget
        cases hget
    exact (insertKernelLeaf_foldl_pivotInv (n := n) core.toList
      (reduceKernelLeafFuel core shift)
      (Array.replicate (MatrixWidth core) none) shift
      (fun r hr ↦ hcoresizes r hr) hinit p r hget).2
  have hwp_fin : ShiftedWeakPopov
      (completeMissingPivotRows problem shift red) shift :=
    pm_completeMissingPivotRows_shiftedWeakPopov problem shift hwp_red
  -- Apply the predictable-degree property of weak-Popov matrices.
  have hdeg : rowShiftedDegree? row' shift ≠ none := by
    rw [hrow'deg]
    intro h
    exact hrownz (rowShiftedDegree?_eq_none_iff.1 h)
  obtain ⟨outRow, outDeg, rowDeg, houtmem, houtdeg, hrowdeg, hle⟩ :=
    shiftedWeakPopov_least_row_minimal
      (completeMissingPivotRows problem shift red) shift row'
      (wellFormed_of_sizes hfinsizes) hwp_fin hrow'fin hdeg
  refine ⟨outRow, outDeg, by rw [hbasis_eq]; exact houtmem,
    le_of_eq (hfinsizes outRow houtmem), houtdeg, ?_⟩
  intro rowDegree hrowDegree
  rw [hrow'deg, hrowDegree] at hrowdeg
  cases Option.some.inj hrowdeg
  exact hle

end Approximant

end PolynomialMatrix

end CompPoly
