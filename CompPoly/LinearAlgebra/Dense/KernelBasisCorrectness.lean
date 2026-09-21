/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.LinearAlgebra.Dense.KernelCorrectness
public import CompPoly.LinearAlgebra.Dense.RowArrayCorrectness

/-!
# Dense Homogeneous-Kernel Basis Correctness

`homogeneousKernelBasis M` coincides with the row-array kernel
`homogeneousKernelBasisRows (toRows M) M.cols` for every well-formed `M`: the
two Gauss-Jordan loops make the same pivot choices and produce the same reduced
entries. The row-array soundness and completeness theorems therefore transfer to
the dense kernel.
-/

@[expose] public section

namespace CompPoly

namespace DenseMatrix

variable {F : Type*}

/-! ## Row representation -/

/-- `rows` has one row per row of `M`, and stores the entries of `M` below `M.cols`. -/
private def RowsRep [Zero F] (M : DenseMatrix F) (rows : Array (Array F)) : Prop :=
  rows.size = M.rows ∧
    ∀ i j, i < M.rows → j < M.cols → (rows.getD i #[]).getD j 0 = M.get i j

/-- The number of rows of `toRows M`. -/
theorem toRows_size [Zero F] (M : DenseMatrix F) : M.toRows.size = M.rows := by
  simp [toRows]

/-- Entries of `toRows M` below the matrix dimensions are the entries of `M`. -/
theorem toRows_getD [Zero F] (M : DenseMatrix F) {i j : Nat} (hi : i < M.rows)
    (hj : j < M.cols) : (M.toRows.getD i #[]).getD j 0 = M.get i j := by
  simp [toRows, Array.getD_eq_getD_getElem?, hi, hj]

private theorem rowsRep_toRows [Zero F] (M : DenseMatrix F) : RowsRep M M.toRows :=
  ⟨toRows_size M, fun _ _ hi hj ↦ toRows_getD M hi hj⟩

/-! ## Pivot search -/

private theorem foldl_findPivotRowStep_eq_find? [Zero F] [BEq F]
    (M : DenseMatrix F) (rows : Array (Array F)) (col : Nat) (xs : List Nat)
    (h : ∀ r ∈ xs, (rows.getD r #[]).getD col 0 = M.get r col) :
    xs.foldl (findPivotRowStep M col) none =
      xs.find? fun r ↦ (rows.getD r #[]).getD col 0 != 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, List.find?_cons, h x (by simp)]
      by_cases hx : (M.get x col == 0) = true
      · have hstep : findPivotRowStep M col none x = none := by
          simp [findPivotRowStep, hx]
        rw [hstep, ih (fun r hr ↦ h r (by simp [hr]))]
        simp [bne, hx]
      · have hstep : findPivotRowStep M col none x = some x := by
          simp [findPivotRowStep, hx]
        rw [hstep, findPivotRowStep_fold_some]
        simp [bne, hx]

private theorem findScalarPivotRow_eq_findPivotRow [Field F] [BEq F]
    {M : DenseMatrix F} {rows : Array (Array F)} (hrep : RowsRep M rows)
    {col : Nat} (hcol : col < M.cols) (start : Nat) :
    findScalarPivotRow rows start col = findPivotRow M start col := by
  unfold findScalarPivotRow
  rw [findPivotRow_eq_fold, hrep.1, foldl_findPivotRowStep_eq_find?]
  intro r hr
  exact hrep.2 r col (by have := List.mem_range'_1.mp hr; omega) hcol

/-! ## Row operations -/

private theorem rowsRep_swap [Field F] {M : DenseMatrix F} {rows : Array (Array F)}
    (hM : WellFormed M) (hrep : RowsRep M rows) {a b : Nat} (ha : a < M.rows)
    (hb : b < M.rows) : RowsRep (swapRows M a b) (swapScalarRows rows a b) := by
  have ha' : a < rows.size := hrep.1 ▸ ha
  have hb' : b < rows.size := hrep.1 ▸ hb
  refine ⟨by rw [swapScalarRows_size, swapRows_rows, hrep.1], ?_⟩
  intro i j hi hj
  rw [swapRows_rows] at hi
  rw [swapRows_cols] at hj
  rw [swapScalarRows_getD rows ha' hb' i]
  by_cases hib : i = b
  · subst hib
    rw [ite_eq_left rfl, swapRows_get_right hM hb hj, hrep.2 a j ha hj]
  · by_cases hia : i = a
    · subst hia
      rw [ite_eq_right hib, ite_eq_left rfl, swapRows_get_left hM ha hj, hrep.2 b j hb hj]
    · rw [ite_eq_right hib, ite_eq_right hia,
        swapRows_get_of_row_ne hj (Ne.symm hia) (Ne.symm hib), hrep.2 i j hi hj]

/-- Closed form of the elimination loop inside `normalizeAndEliminate`: each
listed row other than the pivot row has the pivot row, scaled by its own entry
in the pivot column, subtracted from it once. -/
private theorem list_forIn_addScaledRow_get [Field F]
    (rs : List Nat) {out : DenseMatrix F} {pivotRow pivotCol row k : Nat}
    (hout : WellFormed out) (hpr : pivotRow < out.rows) (hpc : pivotCol < out.cols)
    (hk : k < out.cols) (hrow : row < out.rows) (hnodup : rs.Nodup) :
    (Id.run (forIn rs out fun r M ↦
      if r = pivotRow then
        pure (ForInStep.yield M)
      else
        pure (ForInStep.yield
          (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
      Id (DenseMatrix F))).get row k =
      if row ∈ rs ∧ row ≠ pivotRow then
        out.get row k - out.get row pivotCol * out.get pivotRow k
      else
        out.get row k := by
  induction rs generalizing out with
  | nil => simp
  | cons r rs ih =>
      have hrs : rs.Nodup := (List.nodup_cons.mp hnodup).2
      have hrnot : r ∉ rs := (List.nodup_cons.mp hnodup).1
      by_cases hrp : r = pivotRow
      · subst hrp
        have h := ih (out := out) hout hpr hpc hk hrow hrs
        simp only [List.forIn_cons] at h ⊢
        refine h.trans ?_
        by_cases hrr : row = r <;> simp [hrr]
      · set out' := addScaledRow out r pivotRow (-(out.get r pivotCol)) with hout'
        have hwf' : WellFormed out' := addScaledRow_wf hout _ _ _
        have hrows' : out'.rows = out.rows := by simp [out', addScaledRow]
        have hcols' : out'.cols = out.cols := by simp [out', addScaledRow]
        have ih' := ih (out := out') hwf' (hrows' ▸ hpr) (hcols' ▸ hpc)
          (hcols' ▸ hk) (hrows' ▸ hrow) hrs
        have hpivot' : ∀ c, c < out.cols → out'.get pivotRow c = out.get pivotRow c :=
          fun c hc ↦ addScaledRow_get_of_row_ne _ hc hrp
        have hloop :
            (Id.run (forIn (r :: rs) out fun r M ↦
              if r = pivotRow then
                pure (ForInStep.yield M)
              else
                pure (ForInStep.yield
                  (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
              Id (DenseMatrix F))) =
            (Id.run (forIn rs out' fun r M ↦
              if r = pivotRow then
                pure (ForInStep.yield M)
              else
                pure (ForInStep.yield
                  (addScaledRow M r pivotRow (-(M.get r pivotCol)))) :
              Id (DenseMatrix F))) := by
          simp [List.forIn_cons, hrp, out']
        rw [hloop, ih', hpivot' k hk]
        by_cases hrr : row = r
        · subst hrr
          have hsame : ∀ c, c < out.cols →
              out'.get row c = out.get row c + -(out.get row pivotCol) * out.get pivotRow c :=
            fun c hc ↦ addScaledRow_get_same hout hrow hc _
          rw [ite_eq_right (fun h ↦ hrnot h.1),
            ite_eq_left ⟨List.mem_cons_self, hrp⟩, hsame k hk]
          ring
        · have hother : ∀ c, c < out.cols → out'.get row c = out.get row c :=
            fun c hc ↦ addScaledRow_get_of_row_ne _ hc (Ne.symm hrr)
          rw [hother k hk, hother pivotCol hpc]
          simp [List.mem_cons, hrr]

/-- Entries of `normalizeAndEliminate` below the matrix dimensions: the pivot row
is divided by the pivot, and every other row loses its pivot-column multiple of
the normalized pivot row. -/
theorem normalizeAndEliminate_get [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {pivotRow pivotCol row k : Nat}
    (hpr : pivotRow < M.rows) (hpc : pivotCol < M.cols)
    (hpivot : M.get pivotRow pivotCol ≠ 0) (hrow : row < M.rows) (hk : k < M.cols) :
    (normalizeAndEliminate M pivotRow pivotCol).get row k =
      if row = pivotRow then
        M.get pivotRow k / M.get pivotRow pivotCol
      else
        M.get row k -
          M.get row pivotCol * (M.get pivotRow k / M.get pivotRow pivotCol) := by
  unfold normalizeAndEliminate
  have hp : (M.get pivotRow pivotCol == 0) = false := by simpa using hpivot
  simp only [hp, Bool.false_eq_true, ↓reduceIte]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  set scaled := scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹ with hscaled
  have hwf : WellFormed scaled := scaleRow_wf hM _ _
  have hsr : scaled.rows = M.rows := by simp [scaled, scaleRow]
  have hsc : scaled.cols = M.cols := by simp [scaled, scaleRow]
  have hloop := list_forIn_addScaledRow_get
    (List.range' 0 (Std.Legacy.Range.size [:scaled.rows]) 1) (out := scaled)
    (pivotRow := pivotRow) (pivotCol := pivotCol) (row := row) (k := k) hwf
    (hsr ▸ hpr) (hsc ▸ hpc) (hsc ▸ hk) (hsr ▸ hrow) List.nodup_range'
  have hmem : row ∈ List.range' 0 (Std.Legacy.Range.size [:scaled.rows]) 1 := by
    rw [List.mem_range'_1]
    simp [Std.Legacy.Range.size, hsr, hrow]
  have hscaledPivot : ∀ c, c < M.cols →
      scaled.get pivotRow c = M.get pivotRow c / M.get pivotRow pivotCol := by
    intro c hc
    rw [scaleRow_get_same hM hpr hc, div_eq_inv_mul]
  have hscaledOther : ∀ c, c < M.cols → row ≠ pivotRow → scaled.get row c = M.get row c :=
    fun c hc hne ↦ scaleRow_get_of_row_ne _ hc (Ne.symm hne)
  refine (Eq.trans (by simp [scaled, scaleRow]) hloop).trans ?_
  by_cases hrp : row = pivotRow
  · subst hrp
    simp [hscaledPivot k hk]
  · simp only [hmem, ne_eq, hrp, not_false_eq_true, and_self, ↓reduceIte]
    rw [hscaledOther k hk hrp, hscaledOther pivotCol hpc hrp, hscaledPivot k hk]

private theorem rowsRep_normalizeAndEliminate [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} {rows : Array (Array F)} (hM : WellFormed M)
    (hrep : RowsRep M rows) {pivotRow pivotCol : Nat} (hpr : pivotRow < M.rows)
    (hpc : pivotCol < M.cols) (hpivot : M.get pivotRow pivotCol ≠ 0) :
    RowsRep (normalizeAndEliminate M pivotRow pivotCol)
      (normalizeAndEliminateScalarRows rows pivotRow pivotCol) := by
  have hpr' : pivotRow < rows.size := hrep.1 ▸ hpr
  have hpivot' : (rows.getD pivotRow #[]).getD pivotCol 0 ≠ 0 := by
    rwa [hrep.2 _ _ hpr hpc]
  refine ⟨?_, ?_⟩
  · rw [normalizeAndEliminate_rows, normalizeAndEliminateScalarRows_size, hrep.1]
  · intro i j hi hj
    rw [normalizeAndEliminate_rows] at hi
    rw [normalizeAndEliminate_cols] at hj
    rw [normalizeAndEliminateScalarRows_getD_entry rows pivotRow pivotCol hpr' hpivot',
      normalizeAndEliminate_get hM hpr hpc hpivot hi hj, hrep.2 _ _ hpr hj,
      hrep.2 _ _ hpr hpc, hrep.2 _ _ hi hj, hrep.2 _ _ hi hpc]

/-! ## Gauss-Jordan loop -/

private theorem rrefLoop_rowsRep [Field F] [BEq F] [LawfulBEq F] (cols : Nat) :
    ∀ (fuel col row : Nat) (M : DenseMatrix F) (rows : Array (Array F))
      (pivots : Array Nat), M.cols = cols → WellFormed M → RowsRep M rows →
      (rrefLoop fuel col row M pivots).pivots =
          (scalarRrefRowsLoop cols fuel col row rows pivots).pivots ∧
        RowsRep (rrefLoop fuel col row M pivots).matrix
          (scalarRrefRowsLoop cols fuel col row rows pivots).rows
  | 0, _, _, _, _, _, _, _, hrep => ⟨rfl, hrep⟩
  | fuel + 1, col, row, M, rows, pivots, hcols, hM, hrep => by
      subst hcols
      simp only [rrefLoop, scalarRrefRowsLoop]
      by_cases hin : col < M.cols ∧ row < M.rows
      · have hd : (decide (col < M.cols) && decide (row < M.rows)) = true := by
          simp [hin]
        have hs : ¬(decide (col ≥ M.cols) || decide (row ≥ rows.size)) = true := by
          simp only [hrep.1, Bool.or_eq_true, decide_eq_true_eq]
          omega
        rw [ite_eq_left hd, ite_eq_right hs,
          findScalarPivotRow_eq_findPivotRow hrep hin.1]
        cases hfind : findPivotRow M row col with
        | none =>
            exact rrefLoop_rowsRep M.cols fuel (col + 1) row M rows pivots rfl hM hrep
        | some p =>
            have hp : p < M.rows := findPivotRow_some_lt hfind
            have hpz : M.get p col ≠ 0 := findPivotRow_some_ne_zero hfind
            have hswWf : WellFormed (swapRows M p row) := swapRows_wf hM p row
            have hswRep := rowsRep_swap hM hrep hp hin.2
            have hswPivot : (swapRows M p row).get row col ≠ 0 := by
              rwa [swapRows_get_right hM hin.2 hin.1]
            have hswRows : (swapRows M p row).rows = M.rows := swapRows_rows M p row
            have hswCols : (swapRows M p row).cols = M.cols := swapRows_cols M p row
            have hred := rowsRep_normalizeAndEliminate hswWf hswRep
              (hswRows ▸ hin.2) (hswCols ▸ hin.1) hswPivot
            exact rrefLoop_rowsRep M.cols fuel (col + 1) (row + 1) _ _ _
              (by rw [normalizeAndEliminate_cols, hswCols])
              (normalizeAndEliminate_wf hswWf row col) hred
      · have hd : ¬(decide (col < M.cols) && decide (row < M.rows)) = true := by
          simpa using hin
        have hs : (decide (col ≥ M.cols) || decide (row ≥ rows.size)) = true := by
          simp only [hrep.1, Bool.or_eq_true, decide_eq_true_eq]
          omega
        rw [ite_eq_right hd, ite_eq_left hs]
        exact ⟨rfl, hrep⟩

private theorem rref_rowsRep [Field F] [BEq F] [LawfulBEq F] {M : DenseMatrix F}
    (hM : WellFormed M) :
    (rref M).pivots = (scalarRrefRows M.toRows M.cols).pivots ∧
      RowsRep (rref M).matrix (scalarRrefRows M.toRows M.cols).rows :=
  rrefLoop_rowsRep M.cols (M.cols + 1) 0 0 M M.toRows #[] rfl hM (rowsRep_toRows M)

/-- For a well-formed matrix, `rref` records the same pivot columns as the
row-array reduction of its rows. -/
theorem rref_pivots_eq_scalarRrefRows [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) :
    (rref M).pivots = (scalarRrefRows M.toRows M.cols).pivots :=
  (rref_rowsRep hM).1

/-! ## The two kernel bases agree -/

/-- The dense homogeneous-kernel basis equals the row-array kernel basis of the
matrix rows. -/
theorem homogeneousKernelBasis_eq_homogeneousKernelBasisRows [Field F] [BEq F]
    [LawfulBEq F] {M : DenseMatrix F} (hM : WellFormed M) :
    homogeneousKernelBasis M = homogeneousKernelBasisRows M.toRows M.cols := by
  obtain ⟨hpiv, hrep⟩ := rref_rowsRep hM
  have hcols : (rref M).matrix.cols = M.cols := rref_cols M
  have hrows : (rref M).matrix.rows = M.rows := rref_rows M
  have hle : (rref M).pivots.size ≤ M.rows := rref_pivots_size_le_rows M
  unfold homogeneousKernelBasis homogeneousKernelBasisRows
  simp only
  rw [hpiv]
  refine Array.map_congr_left fun free hfree ↦ ?_
  have hfreeLt : free < M.cols := (freeColumns_mem (Array.mem_toList_iff.mpr hfree)).1
  unfold basisVectorForFreeColumn basisVectorForFreeColumnRows
  refine Array.ext (by simp [hcols]) fun i hi _ ↦ ?_
  simp only [Array.getElem_ofFn]
  split
  · rfl
  · cases ht : pivotRowOfColumn? (scalarRrefRows M.toRows M.cols).pivots i with
    | none => rfl
    | some t =>
        have ht' := (pivotRowOfColumn?_some ht).1
        rw [← hpiv] at ht'
        simp only
        rw [hrep.2 t free (by omega) (by rw [hcols]; exact hfreeLt)]

/-! ## Soundness, completeness, and independence -/

private theorem list_foldl_add_range [AddCommMonoid F] (f : Nat → F) (n : Nat) :
    (List.range n).foldl (fun acc c ↦ acc + f c) 0 = ∑ c ∈ Finset.range n, f c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

/-- `dotRow` is the finite sum of products over the columns. -/
theorem dotRow_eq_sum [Semiring F] (M : DenseMatrix F) (row : Nat) (v : Array F) :
    dotRow M row v = ∑ k ∈ Finset.range M.cols, M.get row k * v.getD k 0 :=
  list_foldl_add_range _ _

private theorem toRows_sum_eq_dotRow [Field F] {M : DenseMatrix F} {row : Nat}
    (hrow : row < M.rows) (v : Array F) :
    ∑ k ∈ Finset.range M.cols, (M.toRows.getD row #[]).getD k 0 * v.getD k 0 =
      dotRow M row v := by
  rw [dotRow_eq_sum]
  exact Finset.sum_congr rfl fun k hk ↦ by
    rw [toRows_getD M hrow (Finset.mem_range.mp hk)]

private theorem mem_toRows [Zero F] {M : DenseMatrix F} {r : Array F}
    (hr : r ∈ M.toRows.toList) : ∃ row, row < M.rows ∧ M.toRows.getD row #[] = r := by
  obtain ⟨row, hrow, hget⟩ := List.mem_iff_getElem.mp hr
  have hrow' : row < M.toRows.size := by simpa using hrow
  refine ⟨row, toRows_size M ▸ hrow', ?_⟩
  rw [array_getD_of_lt' _ _ hrow', ← Array.getElem_toList hrow']
  exact hget

/-- Every vector of the dense homogeneous-kernel basis has the matrix column width. -/
theorem homogeneousKernelBasis_width [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (hv : v ∈ (homogeneousKernelBasis M).toList) : VectorWidth M v := by
  rw [homogeneousKernelBasis_eq_homogeneousKernelBasisRows hM] at hv
  exact homogeneousKernelBasisRows_size hv

/-- **Soundness of the dense kernel basis.** Every emitted vector solves the
homogeneous system. -/
theorem homogeneousKernelBasis_isHomogeneousSolution [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (hv : v ∈ (homogeneousKernelBasis M).toList) : IsHomogeneousSolution M v := by
  rw [homogeneousKernelBasis_eq_homogeneousKernelBasisRows hM] at hv
  intro row hrow
  rw [← toRows_sum_eq_dotRow hrow]
  refine homogeneousKernelBasisRows_dot_eq_zero hv ?_
  have hrow' : row < M.toRows.size := by rw [toRows_size]; exact hrow
  rw [array_getD_of_lt' _ _ hrow', ← Array.getElem_toList hrow']
  exact List.getElem_mem _

/-- **Completeness of the dense kernel basis.** Every homogeneous solution is,
below the column count, the linear combination of the basis vectors whose
coefficients are its entries at the free columns of `rref M`. -/
theorem homogeneousKernelBasis_complete [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (hv : IsHomogeneousSolution M v) :
    ∀ k, k < M.cols →
      v.getD k 0 =
        ∑ i ∈ Finset.range (homogeneousKernelBasis M).size,
          v.getD ((freeColumns M.cols (rref M).pivots).getD i 0) 0 *
            ((homogeneousKernelBasis M).getD i #[]).getD k 0 := by
  rw [homogeneousKernelBasis_eq_homogeneousKernelBasisRows hM,
    rref_pivots_eq_scalarRrefRows hM]
  refine homogeneousKernelBasisRows_complete M.toRows M.cols fun r hr ↦ ?_
  obtain ⟨row, hrow, rfl⟩ := mem_toRows hr
  rw [toRows_sum_eq_dotRow hrow]
  exact hv row hrow

/-- The number of dense kernel basis vectors is the number of free columns. -/
theorem homogeneousKernelBasis_size [Field F] [BEq F] (M : DenseMatrix F) :
    (homogeneousKernelBasis M).size = (freeColumns M.cols (rref M).pivots).size := by
  simp [homogeneousKernelBasis]

/-- The `i`-th dense kernel basis vector is one at the `i`-th free column and zero
at every other free column. -/
theorem homogeneousKernelBasis_getD_freeColumn [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {i j : Nat}
    (hi : i < (freeColumns M.cols (rref M).pivots).size)
    (hj : j < (freeColumns M.cols (rref M).pivots).size) :
    ((homogeneousKernelBasis M).getD i #[]).getD
        ((freeColumns M.cols (rref M).pivots).getD j 0) 0 =
      if j = i then 1 else 0 := by
  rw [homogeneousKernelBasis_eq_homogeneousKernelBasisRows hM]
  rw [rref_pivots_eq_scalarRrefRows hM] at hi hj ⊢
  rw [homogeneousKernelBasisRows_getD_eq _ _ hi]
  exact basisVector_getD_freeColumn _ _ _ hi hj

/-- **Linear independence of the dense kernel basis.** A linear combination of
the basis vectors that vanishes below the column count has all coefficients
zero. -/
theorem homogeneousKernelBasis_linearIndependent [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) (c : Nat → F)
    (hc : ∀ k, k < M.cols →
      ∑ i ∈ Finset.range (homogeneousKernelBasis M).size,
        c i * ((homogeneousKernelBasis M).getD i #[]).getD k 0 = 0) :
    ∀ i, i < (homogeneousKernelBasis M).size → c i = 0 := by
  intro j hj
  rw [homogeneousKernelBasis_size] at hj
  have hfree : (freeColumns M.cols (rref M).pivots).getD j 0 < M.cols :=
    (freeColumns_mem (freeColumns_getD_mem hj)).1
  have h := hc _ hfree
  rw [Finset.sum_eq_single j] at h
  · rwa [homogeneousKernelBasis_getD_freeColumn hM hj hj, ite_eq_left rfl, mul_one] at h
  · intro i hi hij
    rw [homogeneousKernelBasis_size] at hi
    rw [homogeneousKernelBasis_getD_freeColumn hM (Finset.mem_range.mp hi) hj,
      ite_eq_right (Ne.symm hij), mul_zero]
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by rw [homogeneousKernelBasis_size]; exact hj)) hj'

end DenseMatrix

end CompPoly
