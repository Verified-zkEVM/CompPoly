/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.RrefSemantics

/-!
# Dense RREF Shape Correctness

Pivot-column and processed-column invariants for dense row reduction.
-/

namespace CompPoly

namespace DenseMatrix

/-- Recorded pivot columns have the reduced-column shape expected of RREF. -/
def PivotColumnsShaped [Zero F] [One F] (M : DenseMatrix F)
    (pivots : Array Nat) : Prop :=
  ∀ i, i < pivots.size →
    i < M.rows ∧ pivots.getD i 0 < M.cols ∧
      ∀ row, row < M.rows → M.get row (pivots.getD i 0) = if row = i then 1 else 0

theorem pivotColumnsShaped_empty [Zero F] [One F] (M : DenseMatrix F) :
    PivotColumnsShaped M #[] := by
  intro i hi
  simp at hi

theorem swapRows_preserves_column_shape_of_ne [Zero F] [One F]
    {M : DenseMatrix F} (hM : WellFormed M) {rowA rowB pivot oldCol : Nat}
    (hrowA : rowA < M.rows) (hrowB : rowB < M.rows) (hcol : oldCol < M.cols)
    (hA : rowA ≠ pivot) (hB : rowB ≠ pivot)
    (hshape : ∀ row, row < M.rows → M.get row oldCol = if row = pivot then 1 else 0) :
    ∀ row, row < (swapRows M rowA rowB).rows →
      (swapRows M rowA rowB).get row oldCol = if row = pivot then 1 else 0 := by
  intro row hrowSwap
  have hrow : row < M.rows := by simpa [swapRows_rows] using hrowSwap
  by_cases hrowA' : row = rowA
  · subst row
    rw [swapRows_get_left hM hrowA hcol]
    rw [hshape rowB hrowB]
    rw [if_neg hB, if_neg hA]
  · by_cases hrowB' : row = rowB
    · subst row
      rw [swapRows_get_right hM hrowB hcol]
      rw [hshape rowA hrowA]
      rw [if_neg hA, if_neg hB]
    · rw [swapRows_get_of_row_ne hcol]
      · exact hshape row hrow
      · intro h
        exact hrowA' h.symm
      · intro h
        exact hrowB' h.symm

theorem list_forIn_addScaledRow_get_of_not_mem [Field F]
    (rows : List Nat) {out : DenseMatrix F} {row col pivotRow pivotCol : Nat}
    (hcol : col < out.cols) (hnot : row ∉ rows) :
    (Id.run (forIn rows out fun r M ↦
      if r = pivotRow then
        pure (ForInStep.yield M)
      else
        pure (ForInStep.yield
          (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
      Id (DenseMatrix F))).get row col = out.get row col := by
  induction rows generalizing out with
  | nil =>
      simp
  | cons r rows ih =>
      have hr_ne : r ≠ row := by
        intro hr
        apply hnot
        simp [hr]
      have hnotTail : row ∉ rows := by
        intro hmem
        apply hnot
        simp [hmem]
      by_cases hrp : r = pivotRow
      · simpa [List.forIn_cons, hrp] using
          ih (out := out) hcol hnotTail
      · have hstepCol : col < (addScaledRow out r pivotRow (-(out.get r pivotCol))).cols := by
          simpa [addScaledRow] using hcol
        have hstepGet :
            (addScaledRow out r pivotRow (-(out.get r pivotCol))).get row col =
              out.get row col := by
          rw [addScaledRow_get_of_row_ne (M := out) (target := r) (source := pivotRow)
            (row := row) (col := col) (-(out.get r pivotCol)) hcol hr_ne]
        calc
          (Id.run (forIn (r :: rows) out fun r M ↦
              if r = pivotRow then
                pure (ForInStep.yield M)
              else
                pure (ForInStep.yield
                  (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
              Id (DenseMatrix F))).get row col
              = (Id.run (forIn rows
                  (addScaledRow out r pivotRow (-(out.get r pivotCol))) fun r M ↦
                  if r = pivotRow then
                    pure (ForInStep.yield M)
                  else
                    pure (ForInStep.yield
                      (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
                  Id (DenseMatrix F))).get row col := by
                    simp [List.forIn_cons, hrp]
          _ = (addScaledRow out r pivotRow (-(out.get r pivotCol))).get row col :=
                ih (out := addScaledRow out r pivotRow (-(out.get r pivotCol)))
                  hstepCol hnotTail
          _ = out.get row col := hstepGet

theorem list_forIn_addScaledRow_get_pivotRow [Field F]
    (rows : List Nat) {out : DenseMatrix F} {pivotRow pivotCol : Nat}
    (hcol : pivotCol < out.cols) (hpivot : out.get pivotRow pivotCol = 1) :
    (Id.run (forIn rows out fun row M ↦
      if row = pivotRow then
        pure (ForInStep.yield M)
      else
        pure (ForInStep.yield
          (addScaledRow M row pivotRow (-(M.get row pivotCol)))) :
      Id (DenseMatrix F))).get pivotRow pivotCol = 1 := by
  induction rows generalizing out with
  | nil =>
      simpa using hpivot
  | cons row rows ih =>
      by_cases hrow : row = pivotRow
      · simpa [List.forIn_cons, hrow] using ih (out := out) hcol hpivot
      · have hstepCol : pivotCol <
            (addScaledRow out row pivotRow (-(out.get row pivotCol))).cols := by
          simpa [addScaledRow] using hcol
        have hstepPivot :
            (addScaledRow out row pivotRow (-(out.get row pivotCol))).get
              pivotRow pivotCol = 1 := by
          rw [addScaledRow_get_of_row_ne (M := out) (target := row) (source := pivotRow)
            (row := pivotRow) (col := pivotCol) (-(out.get row pivotCol)) hcol hrow]
          exact hpivot
        simpa [List.forIn_cons, hrow] using
          ih (out := addScaledRow out row pivotRow (-(out.get row pivotCol)))
            hstepCol hstepPivot

theorem list_forIn_addScaledRow_get_row_mem [Field F]
    (rows : List Nat) {out : DenseMatrix F} {row pivotRow pivotCol : Nat}
    (hout : WellFormed out) (hpivotRow : pivotRow < out.rows)
    (hcol : pivotCol < out.cols) (hpivot : out.get pivotRow pivotCol = 1)
    (hrows : ∀ r, r ∈ rows → r < out.rows) (hnodup : rows.Nodup)
    (hmem : row ∈ rows) (hne : row ≠ pivotRow) :
    (Id.run (forIn rows out fun r M ↦
      if r = pivotRow then
        pure (ForInStep.yield M)
      else
        pure (ForInStep.yield
          (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
      Id (DenseMatrix F))).get row pivotCol = 0 := by
  induction rows generalizing out with
  | nil =>
      simp at hmem
  | cons r rows ih =>
      have hrowsTail : ∀ d, d ∈ rows → d < out.rows := by
        intro d hd
        exact hrows d (by simp [hd])
      have hnodupTail : rows.Nodup := hnodup.tail
      by_cases hrp : r = pivotRow
      · subst r
        have hmemTail : row ∈ rows := by
          simp only [List.mem_cons] at hmem
          cases hmem with
          | inl h =>
              exact (hne h).elim
          | inr h =>
              exact h
        simpa [List.forIn_cons, hmemTail, hne.symm] using
          ih (out := out) hout hpivotRow hcol hpivot hrowsTail hnodupTail hmemTail
      · by_cases hr : r = row
        · subst r
          have hrowLt : row < out.rows := hrows row (by simp)
          have hstepWf : WellFormed (addScaledRow out row pivotRow (-(out.get row pivotCol))) :=
            addScaledRow_wf hout row pivotRow (-(out.get row pivotCol))
          have hstepRows :
              (addScaledRow out row pivotRow (-(out.get row pivotCol))).rows = out.rows := by
            simp [addScaledRow]
          have hstepCols :
              (addScaledRow out row pivotRow (-(out.get row pivotCol))).cols = out.cols := by
            simp [addScaledRow]
          have hstepZero :
              (addScaledRow out row pivotRow (-(out.get row pivotCol))).get row pivotCol = 0 := by
            rw [addScaledRow_get_same hout hrowLt hcol (-(out.get row pivotCol))]
            rw [hpivot]
            ring
          have hnotTail : row ∉ rows := (List.nodup_cons.mp hnodup).1
          calc
            (Id.run (forIn (row :: rows) out fun r M ↦
              if r = pivotRow then
                pure (ForInStep.yield M)
              else
                pure (ForInStep.yield
                  (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
              Id (DenseMatrix F))).get row pivotCol
                = (Id.run (forIn rows
                    (addScaledRow out row pivotRow (-(out.get row pivotCol))) fun r M ↦
                    if r = pivotRow then
                      pure (ForInStep.yield M)
                    else
                      pure (ForInStep.yield
                        (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
                    Id (DenseMatrix F))).get row pivotCol := by
                      simp [List.forIn_cons, hne]
            _ = (addScaledRow out row pivotRow (-(out.get row pivotCol))).get row pivotCol :=
                  list_forIn_addScaledRow_get_of_not_mem rows
                    (out := addScaledRow out row pivotRow (-(out.get row pivotCol)))
                    (row := row) (col := pivotCol) (pivotRow := pivotRow) (pivotCol := pivotCol)
                    (by simpa [hstepCols] using hcol) hnotTail
            _ = 0 := hstepZero
        · have hmemTail : row ∈ rows := by
            have hrow_ne_r : row ≠ r := by intro h; exact hr h.symm
            simpa [List.mem_cons, hrow_ne_r] using hmem
          have hstepWf : WellFormed (addScaledRow out r pivotRow (-(out.get r pivotCol))) :=
            addScaledRow_wf hout r pivotRow (-(out.get r pivotCol))
          have hstepRowsEq :
              (addScaledRow out r pivotRow (-(out.get r pivotCol))).rows = out.rows := by
            simp [addScaledRow]
          have hstepCol : pivotCol <
              (addScaledRow out r pivotRow (-(out.get r pivotCol))).cols := by
            simpa [addScaledRow] using hcol
          have hpivotStep : pivotRow <
              (addScaledRow out r pivotRow (-(out.get r pivotCol))).rows := by
            simpa [hstepRowsEq] using hpivotRow
          have hrowsStep : ∀ d, d ∈ rows →
              d < (addScaledRow out r pivotRow (-(out.get r pivotCol))).rows := by
            intro d hd
            simpa [hstepRowsEq] using hrowsTail d hd
          have hpivStep :
              (addScaledRow out r pivotRow (-(out.get r pivotCol))).get pivotRow pivotCol = 1 := by
            rw [addScaledRow_get_of_row_ne (M := out) (target := r) (source := pivotRow)
              (row := pivotRow) (col := pivotCol) (-(out.get r pivotCol)) hcol hrp]
            exact hpivot
          simpa [List.forIn_cons, hrp] using
            ih (out := addScaledRow out r pivotRow (-(out.get r pivotCol)))
              hstepWf hpivotStep hstepCol hpivStep hrowsStep hnodupTail hmemTail

theorem list_forIn_addScaledRow_get_of_source_zero [Field F]
    (rows : List Nat) {out : DenseMatrix F} {row pivotRow oldCol pivotCol : Nat}
    (hout : WellFormed out) (hcol : oldCol < out.cols)
    (hrows : ∀ r, r ∈ rows → r < out.rows)
    (hsource : out.get pivotRow oldCol = 0) :
    (Id.run (forIn rows out fun r M ↦
      if r = pivotRow then
        pure (ForInStep.yield M)
      else
        pure (ForInStep.yield
          (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
      Id (DenseMatrix F))).get row oldCol = out.get row oldCol := by
  induction rows generalizing out with
  | nil =>
      simp
  | cons r rows ih =>
      have hrowsTail : ∀ d, d ∈ rows → d < out.rows := by
        intro d hd
        exact hrows d (by simp [hd])
      by_cases hrp : r = pivotRow
      · simpa [List.forIn_cons, hrp] using ih (out := out) hout hcol hrowsTail hsource
      · have hrLt : r < out.rows := hrows r (by simp)
        have hstepWf : WellFormed (addScaledRow out r pivotRow (-(out.get r pivotCol))) :=
          addScaledRow_wf hout r pivotRow (-(out.get r pivotCol))
        have hstepRows :
            (addScaledRow out r pivotRow (-(out.get r pivotCol))).rows = out.rows := by
          simp [addScaledRow]
        have hstepCols :
            (addScaledRow out r pivotRow (-(out.get r pivotCol))).cols = out.cols := by
          simp [addScaledRow]
        have hsourceStep :
            (addScaledRow out r pivotRow (-(out.get r pivotCol))).get pivotRow oldCol = 0 := by
          rw [addScaledRow_get_of_row_ne (M := out) (target := r) (source := pivotRow)
            (row := pivotRow) (col := oldCol) (-(out.get r pivotCol)) hcol hrp]
          exact hsource
        have hrowStep :
            (addScaledRow out r pivotRow (-(out.get r pivotCol))).get row oldCol =
              out.get row oldCol := by
          by_cases hrr : r = row
          · subst r
            rw [addScaledRow_get_same hout hrLt hcol (-(out.get row pivotCol))]
            rw [hsource]
            simp
          · rw [addScaledRow_get_of_row_ne (M := out) (target := r) (source := pivotRow)
              (row := row) (col := oldCol) (-(out.get r pivotCol)) hcol hrr]
        calc
          (Id.run (forIn (r :: rows) out fun r M ↦
            if r = pivotRow then
              pure (ForInStep.yield M)
            else
              pure (ForInStep.yield
                (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
            Id (DenseMatrix F))).get row oldCol
              = (Id.run (forIn rows
                  (addScaledRow out r pivotRow (-(out.get r pivotCol))) fun r M ↦
                  if r = pivotRow then
                    pure (ForInStep.yield M)
                  else
                    pure (ForInStep.yield
                      (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
                  Id (DenseMatrix F))).get row oldCol := by
                    simp [List.forIn_cons, hrp]
          _ = (addScaledRow out r pivotRow (-(out.get r pivotCol))).get row oldCol :=
                ih (out := addScaledRow out r pivotRow (-(out.get r pivotCol)))
                  hstepWf (by simpa [hstepCols] using hcol)
                  (by
                    intro d hd
                    simpa [hstepRows] using hrowsTail d hd)
                  hsourceStep
          _ = out.get row oldCol := hrowStep

theorem normalizeAndEliminate_get_pivot [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {pivotRow pivotCol : Nat}
    (hpivotRow : pivotRow < M.rows) (hpivotCol : pivotCol < M.cols)
    (hpivot : M.get pivotRow pivotCol ≠ 0) :
    (normalizeAndEliminate M pivotRow pivotCol).get pivotRow pivotCol = 1 := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · exact (hpivot (beq_iff_eq.mp hp)).elim
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hscaledPivot :
        (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).get pivotRow pivotCol = 1 := by
      rw [scaleRow_get_same hM hpivotRow hpivotCol (M.get pivotRow pivotCol)⁻¹]
      exact inv_mul_cancel₀ hpivot
    have hscaledCol : pivotCol <
        (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).cols := by
      simpa [scaleRow] using hpivotCol
    simpa [scaleRow] using
      list_forIn_addScaledRow_get_pivotRow
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        hscaledCol hscaledPivot

theorem normalizeAndEliminate_get_row_pivot [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {pivotRow pivotCol row : Nat}
    (hpivotRow : pivotRow < M.rows) (hpivotCol : pivotCol < M.cols)
    (hrow : row < M.rows) (hne : row ≠ pivotRow)
    (hpivot : M.get pivotRow pivotCol ≠ 0) :
    (normalizeAndEliminate M pivotRow pivotCol).get row pivotCol = 0 := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · exact (hpivot (beq_iff_eq.mp hp)).elim
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    let scaled := scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹
    have hscaledWf : WellFormed scaled := by
      exact scaleRow_wf hM pivotRow (M.get pivotRow pivotCol)⁻¹
    have hpivotScaled : pivotRow < scaled.rows := by
      simpa [scaled, scaleRow] using hpivotRow
    have hrowScaled : row < scaled.rows := by
      simpa [scaled, scaleRow] using hrow
    have hcolScaled : pivotCol < scaled.cols := by
      simpa [scaled, scaleRow] using hpivotCol
    have hscaledPivot : scaled.get pivotRow pivotCol = 1 := by
      unfold scaled
      rw [scaleRow_get_same hM hpivotRow hpivotCol (M.get pivotRow pivotCol)⁻¹]
      exact inv_mul_cancel₀ hpivot
    have hmem : row ∈
        List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1 := by
      simp [Std.Legacy.Range.size, scaleRow, hrow]
    have hrows : ∀ r,
        r ∈ List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1 →
        r < scaled.rows := by
      intro r hr
      have hrange := List.mem_range'_1.mp hr
      simpa [scaled, scaleRow, Std.Legacy.Range.size] using hrange.2
    simpa [scaled, scaleRow] using
      list_forIn_addScaledRow_get_row_mem
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        hscaledWf hpivotScaled hcolScaled hscaledPivot hrows
        (List.nodup_range' (s := 0)
          (n := Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]))
        hmem hne

theorem normalizeAndEliminate_get_of_pivotRow_zero [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {pivotRow pivotCol oldCol row : Nat}
    (hpivotRow : pivotRow < M.rows) (holdCol : oldCol < M.cols)
    (hpivotZero : M.get pivotRow oldCol = 0) :
    (normalizeAndEliminate M pivotRow pivotCol).get row oldCol = M.get row oldCol := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · simp [hp]
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    let scaled := scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹
    have hscaledWf : WellFormed scaled := by
      exact scaleRow_wf hM pivotRow (M.get pivotRow pivotCol)⁻¹
    have hcolScaled : oldCol < scaled.cols := by
      simpa [scaled, scaleRow] using holdCol
    have hsourceScaled : scaled.get pivotRow oldCol = 0 := by
      unfold scaled
      rw [scaleRow_get_same hM hpivotRow holdCol (M.get pivotRow pivotCol)⁻¹]
      rw [hpivotZero]
      simp
    have hrows : ∀ r,
        r ∈ List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1 →
        r < scaled.rows := by
      intro r hr
      have hrange := List.mem_range'_1.mp hr
      simpa [scaled, scaleRow, Std.Legacy.Range.size] using hrange.2
    have hloop :
        (Id.run (forIn
          (List.range' 0
            (Std.Legacy.Range.size
              [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
          (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) fun r M ↦
          if r = pivotRow then
            pure (ForInStep.yield M)
          else
            pure (ForInStep.yield
              (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
          Id (DenseMatrix F))).get row oldCol =
          scaled.get row oldCol := by
      simpa [scaled] using
        list_forIn_addScaledRow_get_of_source_zero
          (List.range' 0
            (Std.Legacy.Range.size
              [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
          (out := scaled) (row := row) (pivotRow := pivotRow)
          (oldCol := oldCol) (pivotCol := pivotCol)
          hscaledWf hcolScaled hrows hsourceScaled
    trans scaled.get row oldCol
    · simpa [scaled, scaleRow] using hloop
    · by_cases hrow : row = pivotRow
      · subst row
        exact hsourceScaled.trans hpivotZero.symm
      · unfold scaled
        rw [scaleRow_get_of_row_ne (M := M) (r := pivotRow) (row := row)
          (col := oldCol) (M.get pivotRow pivotCol)⁻¹ holdCol (by intro h; exact hrow h.symm)]

theorem rrefLoop_pivots_size_le_rows [Field F] [BEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      row ≤ M.rows →
        (rrefLoop fuel col row M pivots).pivots.size ≤
          pivots.size + (M.rows - row) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots _hrow
      simp [rrefLoop]
  | succ fuel ih =>
      intro col row M pivots hrow
      rw [rrefLoop]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard]
        cases hp : findPivotRow M row col with
        | none =>
            exact ih (col + 1) row M pivots hrow
        | some pivotRow =>
            have hrow_lt : row < M.rows := by
              have hand := Bool.and_eq_true_iff.mp hguard
              exact of_decide_eq_true hand.2
            have hrows :
                (normalizeAndEliminate (swapRows M pivotRow row) row col).rows =
                  M.rows := by
              rw [normalizeAndEliminate_rows, swapRows_rows]
            have hrec := ih (col + 1) (row + 1)
              (normalizeAndEliminate (swapRows M pivotRow row) row col)
              (pivots.push col) (by
                rw [hrows]
                exact Nat.succ_le_of_lt hrow_lt)
            rw [hrows] at hrec
            have harith :
                (pivots.push col).size + (M.rows - (row + 1)) ≤
                  pivots.size + (M.rows - row) := by
              simp [Array.size_push]
              omega
            exact le_trans hrec harith
      · simp [hguard]

theorem rref_pivots_size_le_rows [Field F] [BEq F]
    (M : DenseMatrix F) : (rref M).pivots.size ≤ M.rows := by
  unfold rref
  simpa using (rrefLoop_pivots_size_le_rows (fuel := M.cols + 1) (col := 0)
    (row := 0) (M := M) (pivots := #[]) (Nat.zero_le _))

/-- All recorded pivot columns are strictly before the current scan column. -/
def PivotColumnsBefore (pivots : Array Nat) (col : Nat) : Prop :=
  ∀ i, i < pivots.size → pivots.getD i 0 < col

/-- Pivot columns are strictly increasing in pivot-row order. -/
def PivotColumnsStrict (pivots : Array Nat) : Prop :=
  ∀ i j, i < pivots.size → j < pivots.size → i < j →
    pivots.getD i 0 < pivots.getD j 0

theorem pivotColumnsBefore_empty (col : Nat) :
    PivotColumnsBefore #[] col := by
  intro i hi
  simp at hi

theorem pivotColumnsStrict_empty : PivotColumnsStrict #[] := by
  intro i _ hi _ _
  simp at hi

theorem pivotColumnsBefore_mono {pivots : Array Nat} {col next : Nat}
    (h : PivotColumnsBefore pivots col) (hcol : col < next) :
    PivotColumnsBefore pivots next := by
  intro i hi
  exact Nat.lt_trans (h i hi) hcol

theorem pivotColumnsBefore_push {pivots : Array Nat} {col next : Nat}
    (h : PivotColumnsBefore pivots col) (hcol : col < next) :
    PivotColumnsBefore (pivots.push col) next := by
  intro i hi
  by_cases hlast : i = pivots.size
  · subst i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
    simp [hcol]
  · have hiOld : i < pivots.size := by
      rw [Array.size_push] at hi
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hiOld]
    have hold := h i hiOld
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiOld] at hold
    exact Nat.lt_trans hold hcol

theorem pivotColumnsStrict_push {pivots : Array Nat} {col : Nat}
    (hstrict : PivotColumnsStrict pivots) (hbefore : PivotColumnsBefore pivots col) :
    PivotColumnsStrict (pivots.push col) := by
  intro i j hi hj hij
  by_cases hjlast : j = pivots.size
  · subst j
    have hiOld : i < pivots.size := by
      rw [Array.size_push] at hi
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hiOld]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
    simp only [Option.getD_some]
    have hold := hbefore i hiOld
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiOld] at hold
    exact hold
  · have hjOld : j < pivots.size := by
      rw [Array.size_push] at hj
      omega
    have hiOld : i < pivots.size := Nat.lt_trans hij hjOld
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hiOld]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hjOld]
    have hlt := hstrict i j hiOld hjOld hij
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hiOld] at hlt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjOld] at hlt
    exact hlt

theorem pivotColumnsStrict_getD_ne {pivots : Array Nat}
    (hstrict : PivotColumnsStrict pivots) {i j : Nat}
    (hi : i < pivots.size) (hj : j < pivots.size) (hne : i ≠ j) :
    pivots.getD i 0 ≠ pivots.getD j 0 := by
  intro heq
  by_cases hij : i < j
  · have hlt := hstrict i j hi hj hij
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt
  · have hji : j < i := by omega
    have hlt := hstrict j i hj hi hji
    rw [heq] at hlt
    exact Nat.lt_irrefl _ hlt

theorem rrefLoop_pivots_getD_lt_cols [Field F] [BEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      (∀ i, i < pivots.size → pivots.getD i 0 < M.cols) →
        ∀ i, i < (rrefLoop fuel col row M pivots).pivots.size →
          (rrefLoop fuel col row M pivots).pivots.getD i 0 < M.cols := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots hpiv i hi
      exact hpiv i hi
  | succ fuel ih =>
      intro col row M pivots hpiv i hi
      rw [rrefLoop] at hi ⊢
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard] at hi ⊢
        cases hp : findPivotRow M row col with
        | none =>
            have hi' : i < (rrefLoop fuel (col + 1) row M pivots).pivots.size := by
              simpa [hp] using hi
            have hrec := ih (col + 1) row M pivots hpiv i hi'
            simpa [hp] using hrec
        | some pivotRow =>
            let M' := normalizeAndEliminate (swapRows M pivotRow row) row col
            have hcols : M'.cols = M.cols := by
              simp [M', normalizeAndEliminate_cols, swapRows_cols]
            have hcol_lt : col < M.cols := by
              have hand := Bool.and_eq_true_iff.mp hguard
              exact of_decide_eq_true hand.1
            have hpivPush : ∀ i, i < (pivots.push col).size →
                (pivots.push col).getD i 0 < M'.cols := by
              intro j hj
              by_cases hlast : j = pivots.size
              · subst j
                rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
                simp [hcols, hcol_lt]
              · have hjOld : j < pivots.size := by
                  rw [Array.size_push] at hj
                  omega
                rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hjOld]
                have hold := hpiv j hjOld
                rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjOld] at hold
                simpa [hcols] using hold
            have hi' :
                i < (rrefLoop fuel (col + 1) (row + 1) M'
                  (pivots.push col)).pivots.size := by
              simpa [hp, M'] using hi
            have hrec := ih (col + 1) (row + 1) M' (pivots.push col) hpivPush i hi'
            simpa [M', hcols] using hrec
      · simp [hguard] at hi ⊢
        simpa [Array.getD_eq_getD_getElem?] using hpiv i hi

theorem rref_pivots_getD_lt_cols [Field F] [BEq F] (M : DenseMatrix F) :
    ∀ i, i < (rref M).pivots.size → (rref M).pivots.getD i 0 < M.cols := by
  unfold rref
  exact rrefLoop_pivots_getD_lt_cols _ _ _ _ _ (by
    intro i hi
    simp at hi)

theorem rrefLoop_pivotColumnsStrict [Field F] [BEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      PivotColumnsBefore pivots col → PivotColumnsStrict pivots →
        PivotColumnsStrict (rrefLoop fuel col row M pivots).pivots := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots _ hstrict
      exact hstrict
  | succ fuel ih =>
      intro col row M pivots hbefore hstrict
      rw [rrefLoop]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard]
        cases hp : findPivotRow M row col with
        | none =>
            exact ih (col + 1) row M pivots
              (pivotColumnsBefore_mono hbefore (Nat.lt_succ_self col)) hstrict
        | some pivotRow =>
            exact ih (col + 1) (row + 1)
              (normalizeAndEliminate (swapRows M pivotRow row) row col)
              (pivots.push col)
              (pivotColumnsBefore_push hbefore (Nat.lt_succ_self col))
              (pivotColumnsStrict_push hstrict hbefore)
      · simp [hguard]
        exact hstrict

theorem rref_pivotColumnsStrict [Field F] [BEq F] (M : DenseMatrix F) :
    PivotColumnsStrict (rref M).pivots := by
  unfold rref
  exact rrefLoop_pivotColumnsStrict _ _ _ _ _
    (pivotColumnsBefore_empty 0) pivotColumnsStrict_empty

theorem rrefLoop_pivotColumnsShaped [Field F] [BEq F] [LawfulBEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      WellFormed M →
        row = pivots.size →
          PivotColumnsBefore pivots col →
            PivotColumnsShaped M pivots →
              PivotColumnsShaped (rrefLoop fuel col row M pivots).matrix
                (rrefLoop fuel col row M pivots).pivots := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots _ _ _ hshape
      exact hshape
  | succ fuel ih =>
      intro col row M pivots hM hrowEq hbefore hshape
      rw [rrefLoop]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard]
        cases hp : findPivotRow M row col with
        | none =>
            exact ih (col + 1) row M pivots hM hrowEq
              (pivotColumnsBefore_mono hbefore (Nat.lt_succ_self col)) hshape
        | some pivotRow =>
            have hand := Bool.and_eq_true_iff.mp hguard
            have hcol : col < M.cols := of_decide_eq_true hand.1
            have hrow : row < M.rows := of_decide_eq_true hand.2
            have hpivotLt : pivotRow < M.rows := findPivotRow_some_lt hp
            have hpivotGe : row ≤ pivotRow := findPivotRow_some_ge hp
            let swapped := swapRows M pivotRow row
            let reduced := normalizeAndEliminate swapped row col
            have hswappedWf : WellFormed swapped := by
              exact swapRows_wf hM pivotRow row
            have hrowSwapped : row < swapped.rows := by
              simpa [swapped, swapRows_rows] using hrow
            have hcolSwapped : col < swapped.cols := by
              simpa [swapped, swapRows_cols] using hcol
            have hpivotSwap : swapped.get row col ≠ 0 := by
              unfold swapped
              rw [swapRows_get_right hM hrow hcol]
              exact findPivotRow_some_ne_zero hp
            have hreducedWf : WellFormed reduced := by
              exact normalizeAndEliminate_wf hswappedWf row col
            have hshapeReduced : PivotColumnsShaped reduced (pivots.push col) := by
              intro i hi
              by_cases hlast : i = pivots.size
              · subst i
                have hrowIndex : pivots.size < reduced.rows := by
                  unfold reduced
                  rw [normalizeAndEliminate_rows, swapRows_rows]
                  simpa [← hrowEq] using hrow
                have hcolIndex : (pivots.push col).getD pivots.size 0 < reduced.cols := by
                  unfold reduced
                  rw [normalizeAndEliminate_cols, swapRows_cols]
                  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
                  simpa using hcol
                refine ⟨hrowIndex, hcolIndex, ?_⟩
                intro r hr
                have hrM : r < M.rows := by
                  unfold reduced at hr
                  rwa [normalizeAndEliminate_rows, swapRows_rows] at hr
                rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
                by_cases hrp : r = pivots.size
                · have hrrow : r = row := by
                    rw [hrp, ← hrowEq]
                  subst r
                  rw [← hrowEq]
                  simp only [Option.getD_some]
                  unfold reduced
                  exact normalizeAndEliminate_get_pivot hswappedWf hrowSwapped hcolSwapped
                    hpivotSwap
                · have hrrow : r ≠ row := by
                    intro h
                    apply hrp
                    rw [h, hrowEq]
                  rw [if_neg hrp]
                  unfold reduced
                  exact normalizeAndEliminate_get_row_pivot hswappedWf hrowSwapped
                    hcolSwapped (by simpa [swapped, swapRows_rows] using hrM)
                    hrrow hpivotSwap
              · have hiOld : i < pivots.size := by
                  rw [Array.size_push] at hi
                  omega
                have hshape_i := hshape i hiOld
                let oldCol := pivots.getD i 0
                have holdColM : oldCol < M.cols := hshape_i.2.1
                have hrowIndex : i < reduced.rows := by
                  unfold reduced
                  rw [normalizeAndEliminate_rows, swapRows_rows]
                  exact hshape_i.1
                have hcolIndex : (pivots.push col).getD i 0 < reduced.cols := by
                  unfold reduced
                  rw [normalizeAndEliminate_cols, swapRows_cols]
                  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hiOld]
                  simp only [Option.getD_some]
                  simpa [oldCol, Array.getD_eq_getD_getElem?,
                    Array.getElem?_eq_getElem hiOld] using holdColM
                refine ⟨hrowIndex, hcolIndex, ?_⟩
                intro r hrReduced
                have hrow_ne_i : row ≠ i := by
                  rw [hrowEq]
                  omega
                have hpivot_ne_i : pivotRow ≠ i := by
                  intro hpi
                  rw [hpi, hrowEq] at hpivotGe
                  omega
                have hswappedShape : ∀ r, r < swapped.rows →
                    swapped.get r oldCol = if r = i then 1 else 0 := by
                  unfold swapped
                  exact swapRows_preserves_column_shape_of_ne hM hpivotLt hrow holdColM
                    hpivot_ne_i hrow_ne_i (by
                      intro r hr
                      exact hshape_i.2.2 r hr)
                have hsourceZero : swapped.get row oldCol = 0 := by
                  have h := hswappedShape row hrowSwapped
                  rw [if_neg hrow_ne_i] at h
                  exact h
                rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hiOld]
                simp only [Option.getD_some]
                have hgetOld : pivots[i] = oldCol := by
                  simp [oldCol, Array.getD_eq_getD_getElem?,
                    Array.getElem?_eq_getElem hiOld]
                unfold reduced
                rw [hgetOld]
                rw [normalizeAndEliminate_get_of_pivotRow_zero hswappedWf hrowSwapped
                  (by simpa [swapped, swapRows_cols, oldCol] using holdColM) hsourceZero]
                exact hswappedShape r (by
                  unfold reduced at hrReduced
                  rwa [normalizeAndEliminate_rows] at hrReduced)
            exact ih (col + 1) (row + 1) reduced (pivots.push col)
              hreducedWf
              (by simp [Array.size_push, hrowEq])
              (pivotColumnsBefore_push hbefore (Nat.lt_succ_self col))
              hshapeReduced
      · simp [hguard]
        exact hshape

theorem rref_pivotColumnsShaped [Field F] [BEq F] [LawfulBEq F]
    (M : DenseMatrix F) (hM : WellFormed M) :
    PivotColumnsShaped (rref M).matrix (rref M).pivots := by
  unfold rref
  exact rrefLoop_pivotColumnsShaped _ _ _ _ _ hM rfl
    (pivotColumnsBefore_empty 0) (pivotColumnsShaped_empty M)

/-- All rows at or below the active pivot row are zero in already-scanned columns. -/
def ProcessedColumnsZeroBelow [Zero F] (M : DenseMatrix F)
    (activeRow col : Nat) : Prop :=
  ∀ row c, activeRow ≤ row → row < M.rows → c < col → M.get row c = 0

theorem processedColumnsZeroBelow_pivot_step
    [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {row col pivotRow : Nat}
    (hrow : row < M.rows) (hcol : col < M.cols)
    (hpivotLt : pivotRow < M.rows) (hpivotGe : row ≤ pivotRow)
    (hpivotSwap : (swapRows M pivotRow row).get row col ≠ 0)
    (hproc : ProcessedColumnsZeroBelow M row col) :
    ProcessedColumnsZeroBelow
      (normalizeAndEliminate (swapRows M pivotRow row) row col)
      (row + 1) (col + 1) := by
  intro r c hrActive hrReduced hcProcessed
  let swapped := swapRows M pivotRow row
  let reduced := normalizeAndEliminate swapped row col
  have hswappedWf : WellFormed swapped := by
    exact swapRows_wf hM pivotRow row
  have hrowSwapped : row < swapped.rows := by
    simpa [swapped, swapRows_rows] using hrow
  have hcolSwapped : col < swapped.cols := by
    simpa [swapped, swapRows_cols] using hcol
  have hrM : r < M.rows := by
    have h := hrReduced
    simpa [swapped, reduced, normalizeAndEliminate_rows, swapRows_rows] using h
  have hrSwapped : r < swapped.rows := by
    simpa [swapped, swapRows_rows] using hrM
  have hr_ne_row : r ≠ row := by omega
  by_cases hcEq : c = col
  · subst c
    change reduced.get r col = 0
    unfold reduced
    exact normalizeAndEliminate_get_row_pivot hswappedWf hrowSwapped
      hcolSwapped hrSwapped hr_ne_row hpivotSwap
  · have hcOld : c < col := by omega
    have hcM : c < M.cols := Nat.lt_trans hcOld hcol
    have hcSwapped : c < swapped.cols := by
      simpa [swapped, swapRows_cols] using hcM
    have hsourceZero : swapped.get row c = 0 := by
      unfold swapped
      rw [swapRows_get_right hM hrow hcM]
      exact hproc pivotRow c hpivotGe hpivotLt hcOld
    change reduced.get r c = 0
    unfold reduced
    rw [normalizeAndEliminate_get_of_pivotRow_zero hswappedWf hrowSwapped
      hcSwapped hsourceZero]
    unfold swapped
    by_cases hrp : r = pivotRow
    · subst r
      rw [swapRows_get_left hM hpivotLt hcM]
      exact hproc row c (Nat.le_refl row) hrow hcOld
    · by_cases hrr : r = row
      · omega
      · rw [swapRows_get_of_row_ne hcM]
        · exact hproc r c (by omega) hrM hcOld
        · intro h
          exact hrp h.symm
        · intro h
          exact hrr h.symm

theorem rrefLoop_processedColumnsZeroBelow
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      WellFormed M →
        row = pivots.size →
          row ≤ M.rows →
            M.cols ≤ col + fuel →
              ProcessedColumnsZeroBelow M row col →
                ProcessedColumnsZeroBelow
                  (rrefLoop fuel col row M pivots).matrix
                  (rrefLoop fuel col row M pivots).pivots.size M.cols := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots _hM hrowEq _hrowLe hbound hproc
      simp [rrefLoop]
      intro r c hrActive hrM hc
      exact hproc r c (by omega) hrM (by omega)
  | succ fuel ih =>
      intro col row M pivots hM hrowEq hrowLe hbound hproc
      rw [rrefLoop]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard]
        cases hp : findPivotRow M row col with
        | none =>
            have hprocNext : ProcessedColumnsZeroBelow M row (col + 1) := by
              intro r c hrActive hrM hc
              by_cases hcOld : c < col
              · exact hproc r c hrActive hrM hcOld
              · have hcEq : c = col := by omega
                subst c
                exact findPivotRow_none_get_eq_zero hp hrActive hrM
            exact ih (col + 1) row M pivots hM hrowEq hrowLe (by omega) hprocNext
        | some pivotRow =>
            have hand := Bool.and_eq_true_iff.mp hguard
            have hcol : col < M.cols := of_decide_eq_true hand.1
            have hrow : row < M.rows := of_decide_eq_true hand.2
            have hpivotLt : pivotRow < M.rows := findPivotRow_some_lt hp
            have hpivotGe : row ≤ pivotRow := findPivotRow_some_ge hp
            let swapped := swapRows M pivotRow row
            let reduced := normalizeAndEliminate swapped row col
            have hswappedWf : WellFormed swapped := by
              exact swapRows_wf hM pivotRow row
            have hrowSwapped : row < swapped.rows := by
              simpa [swapped, swapRows_rows] using hrow
            have hpivotSwap : swapped.get row col ≠ 0 := by
              unfold swapped
              rw [swapRows_get_right hM hrow hcol]
              exact findPivotRow_some_ne_zero hp
            have hreducedWf : WellFormed reduced := by
              exact normalizeAndEliminate_wf hswappedWf row col
            have hreducedRows : reduced.rows = M.rows := by
              simp [reduced, swapped, normalizeAndEliminate_rows, swapRows_rows]
            have hreducedCols : reduced.cols = M.cols := by
              simp [reduced, swapped, normalizeAndEliminate_cols, swapRows_cols]
            have hprocReduced : ProcessedColumnsZeroBelow reduced (row + 1) (col + 1) := by
              unfold reduced swapped
              exact processedColumnsZeroBelow_pivot_step hM hrow hcol hpivotLt hpivotGe
                (by
                  rw [swapRows_get_right hM hrow hcol]
                  exact findPivotRow_some_ne_zero hp)
                hproc
            have hrec := ih (col + 1) (row + 1) reduced (pivots.push col)
              hreducedWf
              (by simp [Array.size_push, hrowEq])
              (by rw [hreducedRows]; omega)
              (by rw [hreducedCols]; omega)
              hprocReduced
            simpa [hp, reduced, swapped, hreducedCols] using hrec
      · simp [hguard]
        intro r c hrActive hrM hc
        by_cases hcolDone : M.cols ≤ col
        · exact hproc r c (by omega) hrM (by omega)
        · have hcolLt : col < M.cols := by omega
          have hrowDone : M.rows ≤ row := by
            by_contra hrowNot
            have hrowLt : row < M.rows := by omega
            have hguardTrue : col < M.cols && row < M.rows := by
              simp [hcolLt, hrowLt]
            exact hguard hguardTrue
          omega

theorem rref_processedColumnsZeroBelow
    [Field F] [BEq F] [LawfulBEq F]
    (M : DenseMatrix F) (hM : WellFormed M) :
    ProcessedColumnsZeroBelow (rref M).matrix (rref M).pivots.size M.cols := by
  unfold rref
  exact rrefLoop_processedColumnsZeroBelow (fuel := M.cols + 1) (col := 0)
    (row := 0) (M := M) (pivots := #[]) hM rfl (Nat.zero_le _) (by omega)
    (by
      intro row c _ _ hc
      omega)

end DenseMatrix

end CompPoly
