/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.KernelInPlace
import CompPoly.LinearAlgebra.Dense.RowOpsCorrectness
import CompPoly.LinearAlgebra.Dense.RrefSemantics

/-!
# In-Place Dense Kernel Correctness

The in-place homogeneous-kernel backend (`KernelInPlace.lean`) performs the same
arithmetic, in the same order, as the copying backend (`RowOps.lean`/`Kernel.lean`),
so it returns the same witness. This file proves that equivalence, culminating in
`homogeneousWitnessInPlace_eq`, which lets the certified Guruswami-Sudan backend run
the in-place implementation while reusing every existing correctness theorem.
-/

namespace CompPoly

namespace DenseMatrix

variable {F : Type*}

/-- `setD` at a different index leaves the queried entry unchanged. -/
private theorem getD_setD_ne [Zero F] (d : Array F) {i j : Nat} (h : i ≠ j) (v : F) :
    (setD d i v).getD j 0 = d.getD j 0 := by
  unfold setD
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne h]

/-- A self-reading scale fold equals the constant-reading scale fold, as long as
the accumulator still agrees with the original array on the entries it reads. -/
private theorem foldl_scale_self_eq_const [Field F]
    (cols r : Nat) (factor : F) (data₀ : Array F) :
    ∀ (xs : List Nat), xs.Nodup →
      ∀ (d : Array F),
        (∀ c, c ∈ xs → d.getD (r * cols + c) 0 = data₀.getD (r * cols + c) 0) →
          List.foldl (fun d c ↦ setD d (r * cols + c) (factor * d.getD (r * cols + c) 0)) d xs =
            List.foldl
              (fun d c ↦ setD d (r * cols + c) (factor * data₀.getD (r * cols + c) 0)) d xs := by
  intro xs
  induction xs with
  | nil => intro _ d _; rfl
  | cons c xs ih =>
      intro hnodup d hagree
      simp only [List.foldl_cons]
      rw [hagree c (List.mem_cons_self ..)]
      apply ih hnodup.tail
      intro c' hc'
      have hne : c ≠ c' := fun h ↦ (List.nodup_cons.mp hnodup).1 (h ▸ hc')
      rw [getD_setD_ne _ (by omega)]
      exact hagree c' (List.mem_cons_of_mem _ hc')

/-- The in-place scale of a row produces the same backing array as the copying scale. -/
theorem scaleRowData_eq [Field F] (M : DenseMatrix F) (r : Nat) (factor : F) :
    scaleRowData M.cols r factor M.data = (scaleRow M r factor).data := by
  have h := foldl_scale_self_eq_const M.cols r factor M.data (List.range' 0 M.cols)
    (List.nodup_range' (s := 0) (n := M.cols)) M.data (fun c _ ↦ rfl)
  simpa [scaleRowData, scaleRow, get, index, Std.Legacy.Range.forIn_eq_forIn_range'] using h

/-- Row-major indices in distinct rows are distinct (within the column range). -/
private theorem row_col_index_ne {a b cols c c' : Nat} (hrow : a ≠ b)
    (hc : c < cols) (hc' : c' < cols) : a * cols + c ≠ b * cols + c' := by
  intro h
  have hcols : 0 < cols := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  apply hrow
  have hdiv := congrArg (· / cols) h
  simpa [Nat.mul_comm a cols, Nat.mul_comm b cols, Nat.mul_add_div hcols,
    Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hc'] using hdiv

/-- A self-reading add-scaled fold equals the constant-reading version, as long as the
accumulator still agrees with the original array on the target and source entries. -/
private theorem foldl_addScaled_self_eq_const [Field F]
    (cols target source : Nat) (factor : F) (data₀ : Array F) (hts : target ≠ source) :
    ∀ (xs : List Nat), xs.Nodup → (∀ c, c ∈ xs → c < cols) →
      ∀ (d : Array F),
        (∀ c, c ∈ xs → d.getD (target * cols + c) 0 = data₀.getD (target * cols + c) 0) →
        (∀ c, c ∈ xs → d.getD (source * cols + c) 0 = data₀.getD (source * cols + c) 0) →
          List.foldl (fun d c ↦ setD d (target * cols + c)
              (d.getD (target * cols + c) 0 + factor * d.getD (source * cols + c) 0)) d xs =
            List.foldl (fun d c ↦ setD d (target * cols + c)
              (data₀.getD (target * cols + c) 0 + factor * data₀.getD (source * cols + c) 0))
              d xs := by
  intro xs
  induction xs with
  | nil => intro _ _ d _ _; rfl
  | cons c xs ih =>
      intro hnodup hbounds d hT hS
      have hcc : c < cols := hbounds c (List.mem_cons_self ..)
      simp only [List.foldl_cons]
      rw [hT c (List.mem_cons_self ..), hS c (List.mem_cons_self ..)]
      apply ih hnodup.tail (fun c' hc' ↦ hbounds c' (List.mem_cons_of_mem _ hc'))
      · intro c' hc'
        have hne : c ≠ c' := fun h ↦ (List.nodup_cons.mp hnodup).1 (h ▸ hc')
        rw [getD_setD_ne _ (by omega)]
        exact hT c' (List.mem_cons_of_mem _ hc')
      · intro c' hc'
        have hcc' : c' < cols := hbounds c' (List.mem_cons_of_mem _ hc')
        rw [getD_setD_ne _ (row_col_index_ne hts hcc hcc')]
        exact hS c' (List.mem_cons_of_mem _ hc')

/-- The in-place add-scaled row produces the same backing array as the copying version,
when the target and source rows are distinct. -/
theorem addScaledRowData_eq [Field F] (M : DenseMatrix F) (target source : Nat)
    (factor : F) (hts : target ≠ source) :
    addScaledRowData M.cols target source factor M.data =
      (addScaledRow M target source factor).data := by
  have h := foldl_addScaled_self_eq_const M.cols target source factor M.data hts
    (List.range' 0 M.cols) (List.nodup_range' (s := 0) (n := M.cols))
    (fun c hc ↦ by simpa using (List.mem_range'_1.mp hc).2)
    M.data (fun c _ ↦ rfl) (fun c _ ↦ rfl)
  simpa [addScaledRowData, addScaledRow, get, index,
    Std.Legacy.Range.forIn_eq_forIn_range'] using h

/-- A self-reading swap fold equals the constant-reading version, as long as the
accumulator still agrees with the original array on the two swapped rows. -/
private theorem foldl_swap_self_eq_const [Zero F]
    (cols rowA rowB : Nat) (data₀ : Array F) (hAB : rowA ≠ rowB) :
    ∀ (xs : List Nat), xs.Nodup → (∀ c, c ∈ xs → c < cols) →
      ∀ (d : Array F),
        (∀ c, c ∈ xs → d.getD (rowA * cols + c) 0 = data₀.getD (rowA * cols + c) 0) →
        (∀ c, c ∈ xs → d.getD (rowB * cols + c) 0 = data₀.getD (rowB * cols + c) 0) →
          List.foldl (fun d c ↦ setD (setD d (rowA * cols + c) (d.getD (rowB * cols + c) 0))
              (rowB * cols + c) (d.getD (rowA * cols + c) 0)) d xs =
            List.foldl (fun d c ↦ setD (setD d (rowA * cols + c) (data₀.getD (rowB * cols + c) 0))
              (rowB * cols + c) (data₀.getD (rowA * cols + c) 0)) d xs := by
  intro xs
  induction xs with
  | nil => intro _ _ d _ _; rfl
  | cons c xs ih =>
      intro hnodup hbounds d hA hB
      have hcc : c < cols := hbounds c (List.mem_cons_self ..)
      simp only [List.foldl_cons]
      rw [hA c (List.mem_cons_self ..), hB c (List.mem_cons_self ..)]
      apply ih hnodup.tail (fun c' hc' ↦ hbounds c' (List.mem_cons_of_mem _ hc'))
      · intro c' hc'
        have hne : c ≠ c' := fun h ↦ (List.nodup_cons.mp hnodup).1 (h ▸ hc')
        have hcc' : c' < cols := hbounds c' (List.mem_cons_of_mem _ hc')
        rw [getD_setD_ne _ (row_col_index_ne hAB.symm hcc hcc'), getD_setD_ne _ (by omega)]
        exact hA c' (List.mem_cons_of_mem _ hc')
      · intro c' hc'
        have hne : c ≠ c' := fun h ↦ (List.nodup_cons.mp hnodup).1 (h ▸ hc')
        have hcc' : c' < cols := hbounds c' (List.mem_cons_of_mem _ hc')
        rw [getD_setD_ne _ (by omega), getD_setD_ne _ (row_col_index_ne hAB hcc hcc')]
        exact hB c' (List.mem_cons_of_mem _ hc')

/-- The in-place row swap produces the same backing array as the copying swap. -/
theorem swapRowsData_eq [Zero F] (M : DenseMatrix F) (rowA rowB : Nat) :
    swapRowsData M.cols rowA rowB M.data = (swapRows M rowA rowB).data := by
  by_cases hAB : rowA = rowB
  · simp [swapRowsData, swapRows, hAB]
  · have h := foldl_swap_self_eq_const M.cols rowA rowB M.data hAB
      (List.range' 0 M.cols) (List.nodup_range' (s := 0) (n := M.cols))
      (fun c hc ↦ by simpa using (List.mem_range'_1.mp hc).2)
      M.data (fun c _ ↦ rfl) (fun c _ ↦ rfl)
    simpa [swapRowsData, swapRows, hAB, get, index,
      Std.Legacy.Range.forIn_eq_forIn_range'] using h

/-- The in-place pivot search agrees with the copying one. -/
theorem findPivotRowData_eq [Zero F] [BEq F] (M : DenseMatrix F) (startRow col : Nat) :
    findPivotRowData M.rows M.cols startRow col M.data = findPivotRow M startRow col := by
  simp only [findPivotRowData, findPivotRow, get, index]

/-- The in-place elimination loop tracks the copying one entry-for-entry. -/
private theorem forIn_eliminate_eq [Field F] (cols pivotRow pivotCol : Nat) :
    ∀ (xs : List Nat) (out : DenseMatrix F), out.cols = cols →
      (Id.run (forIn xs out.data fun row r ↦
          if row = pivotRow then pure (ForInStep.yield r)
          else pure (ForInStep.yield
            (addScaledRowData cols row pivotRow (-(r.getD (row * cols + pivotCol) 0)) r))))
        = (Id.run (forIn xs out fun row r ↦
            if row = pivotRow then pure (ForInStep.yield r)
            else pure (ForInStep.yield
              (addScaledRow r row pivotRow (-(r.get row pivotCol)))))).data := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons row xs ih =>
      intro out hcols
      by_cases hr : row = pivotRow
      · simpa [List.forIn_cons, hr] using ih out hcols
      · have hget : out.data.getD (row * cols + pivotCol) 0 = out.get row pivotCol := by
          simp [get, index, hcols]
        have hbridge := addScaledRowData_eq out row pivotRow (-(out.get row pivotCol)) hr
        rw [hcols] at hbridge
        have hcols' : (addScaledRow out row pivotRow (-(out.get row pivotCol))).cols = cols := by
          rw [← hcols]; rfl
        have hih := ih (addScaledRow out row pivotRow (-(out.get row pivotCol))) hcols'
        rw [← hbridge] at hih
        simpa [List.forIn_cons, hr, ← Array.getD_eq_getD_getElem?, hget] using hih

/-- The in-place normalize-and-eliminate step produces the same backing array. -/
theorem normalizeAndEliminateData_eq [Field F] [BEq F] (M : DenseMatrix F)
    (pivotRow pivotCol : Nat) :
    normalizeAndEliminateData M.rows M.cols pivotRow pivotCol M.data
      = (normalizeAndEliminate M pivotRow pivotCol).data := by
  have hpiv : M.data.getD (pivotRow * M.cols + pivotCol) 0 = M.get pivotRow pivotCol := by
    simp [get, index]
  unfold normalizeAndEliminateData normalizeAndEliminate
  rw [hpiv]
  by_cases hp : M.get pivotRow pivotCol == 0
  · simp [hp]
  · simp only [hp, if_false, Bool.false_eq_true]
    have hstart : scaleRowData M.cols pivotRow (M.get pivotRow pivotCol)⁻¹ M.data
        = (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).data :=
      scaleRowData_eq M pivotRow _
    have hcols : (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).cols = M.cols := by
      rw [scaleRow]
    have heli := forIn_eliminate_eq M.cols pivotRow pivotCol
      (List.range' 0 (Std.Legacy.Range.size [:M.rows]))
      (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) hcols
    rw [hstart]
    simpa [Std.Legacy.Range.forIn_eq_forIn_range'] using heli

/-- The in-place reduction loop tracks the copying reduction loop, returning the
same reduced backing array and the same pivot columns. -/
theorem rrefLoopData_eq [Field F] [BEq F] :
    ∀ (fuel col row : Nat) (M : DenseMatrix F) (pivots : Array Nat),
      rrefLoopData fuel M.rows M.cols col row M.data pivots
        = ((rrefLoop fuel col row M pivots).matrix.data,
           (rrefLoop fuel col row M pivots).pivots) := by
  intro fuel
  induction fuel with
  | zero => intro col row M pivots; rfl
  | succ fuel ih =>
      intro col row M pivots
      rw [rrefLoopData, rrefLoop, findPivotRowData_eq]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard, if_true]
        cases hpiv : findPivotRow M row col with
        | none => simpa using ih (col + 1) row M pivots
        | some pivotRow =>
            simp only
            rw [swapRowsData_eq]
            rw [show M.rows = (swapRows M pivotRow row).rows from (swapRows_rows _ _ _).symm,
                show M.cols = (swapRows M pivotRow row).cols from (swapRows_cols _ _ _).symm,
                normalizeAndEliminateData_eq]
            rw [show (swapRows M pivotRow row).rows
                  = (normalizeAndEliminate (swapRows M pivotRow row) row col).rows from
                  (normalizeAndEliminate_rows _ _ _).symm,
                show (swapRows M pivotRow row).cols
                  = (normalizeAndEliminate (swapRows M pivotRow row) row col).cols from
                  (normalizeAndEliminate_cols _ _ _).symm]
            exact ih (col + 1) (row + 1)
              (normalizeAndEliminate (swapRows M pivotRow row) row col) (pivots.push col)
      · simp only [hguard, if_false, Bool.false_eq_true]

/-- The in-place RREF equals the copying RREF. -/
theorem rrefInPlace_eq [Field F] [BEq F] (M : DenseMatrix F) : rrefInPlace M = rref M := by
  obtain ⟨rows, cols, data⟩ := M
  have key := rrefLoopData_eq (cols + 1) 0 0 (⟨rows, cols, data⟩ : DenseMatrix F) #[]
  simp only at key
  simp only [rrefInPlace, rref]
  rw [key]
  set N := rrefLoop (cols + 1) 0 0 (⟨rows, cols, data⟩ : DenseMatrix F) #[] with hN
  have hr : N.matrix.rows = rows := rrefLoop_rows _ _ _ _ _
  have hc : N.matrix.cols = cols := rrefLoop_cols _ _ _ _ _
  rw [← hr, ← hc]

/-- The in-place homogeneous-kernel witness equals the copying witness. -/
theorem homogeneousWitnessInPlace_eq [Field F] [BEq F] (M : DenseMatrix F) :
    homogeneousWitnessInPlace M = homogeneousWitness M := by
  simp only [homogeneousWitnessInPlace, homogeneousWitness,
    homogeneousKernelBasisInPlace, homogeneousKernelBasis, rrefInPlace_eq, rref_cols]

end DenseMatrix

end CompPoly
