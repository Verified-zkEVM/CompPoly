/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.RowOps
import Init.Data.List.Monadic
import Init.Data.Range.Lemmas
import Mathlib.Tactic.Ring

/-!
# Dense Row-Operation Correctness

Correctness lemmas for executable dense row operations.
-/

namespace CompPoly

namespace DenseMatrix

theorem index_lt_of_lt [Zero F] {M : DenseMatrix F} (hM : WellFormed M)
    {row col : Nat} (hrow : row < M.rows) (hcol : col < M.cols) :
    M.index row col < M.data.size := by
  unfold WellFormed at hM
  rw [hM]
  unfold index
  calc
    row * M.cols + col < row * M.cols + M.cols := Nat.add_lt_add_left hcol _
    _ = (row + 1) * M.cols := by rw [Nat.succ_mul]
    _ ≤ M.rows * M.cols := Nat.mul_le_mul_right M.cols hrow

theorem get_setD_index_same [Zero F] {M : DenseMatrix F} {data : Array F}
    {row col : Nat} (hidx : M.index row col < data.size) (value : F) :
    (setD data (M.index row col) value).getD (M.index row col) 0 = value := by
  unfold setD
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hidx]
  rfl

theorem get_setD_index_ne [Zero F] (M : DenseMatrix F) (data : Array F)
    {row col row' col' : Nat} (hcol : col < M.cols) (hcol' : col' < M.cols)
    (hne : row ≠ row' ∨ col ≠ col') (value : F) :
    (setD data (M.index row col) value).getD (M.index row' col') 0 =
      data.getD (M.index row' col') 0 := by
  unfold setD
  by_cases hidx : M.index row col = M.index row' col'
  · have hsame : row = row' ∧ col = col' := by
      unfold index at hidx
      have hcols : 0 < M.cols := Nat.lt_of_le_of_lt (Nat.zero_le col') hcol'
      have hrow : row = row' := by
        have hdiv := congrArg (fun n => n / M.cols) hidx
        rw [Nat.mul_comm row M.cols, Nat.mul_comm row' M.cols,
          Nat.add_comm (M.cols * row) col, Nat.add_comm (M.cols * row') col'] at hdiv
        change (col + M.cols * row) / M.cols =
          (col' + M.cols * row') / M.cols at hdiv
        rw [Nat.add_mul_div_left col row hcols,
          Nat.add_mul_div_left col' row' hcols,
          Nat.div_eq_of_lt hcol, Nat.div_eq_of_lt hcol',
          Nat.zero_add, Nat.zero_add] at hdiv
        exact hdiv
      have hcolEq : col = col' := by
        have hmod := congrArg (fun n => n % M.cols) hidx
        rw [Nat.mul_comm row M.cols, Nat.mul_comm row' M.cols,
          Nat.add_comm (M.cols * row) col, Nat.add_comm (M.cols * row') col'] at hmod
        change (col + M.cols * row) % M.cols =
          (col' + M.cols * row') % M.cols at hmod
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hcol, Nat.mod_eq_of_lt hcol'] at hmod
        exact hmod
      exact ⟨hrow, hcolEq⟩
    cases hne with
    | inl hr => exact (hr hsame.1).elim
    | inr hc => exact (hc hsame.2).elim
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hidx]

theorem get_setD_index_ne_same_row [Zero F] (M : DenseMatrix F) (data : Array F)
    {row col col' : Nat} (hcol : col < M.cols) (hcol' : col' < M.cols)
    (hne : col ≠ col') (value : F) :
    (setD data (M.index row col) value).getD (M.index row col') 0 =
      data.getD (M.index row col') 0 :=
  get_setD_index_ne M data hcol hcol' (Or.inr hne) value

theorem get_setD_index_ne_same_col [Zero F] (M : DenseMatrix F) (data : Array F)
    {row row' col : Nat} (hcol : col < M.cols)
    (hne : row ≠ row') (value : F) :
    (setD data (M.index row col) value).getD (M.index row' col) 0 =
      data.getD (M.index row' col) 0 :=
  get_setD_index_ne M data hcol hcol (Or.inl hne) value

theorem list_foldl_array_size_of_eq {α β : Type*}
    (f : Array α → β → Array α)
    (h : ∀ data x, (f data x).size = data.size) :
    ∀ (xs : List β) (data : Array α), (xs.foldl f data).size = data.size := by
  intro xs
  induction xs with
  | nil =>
      intro data
      rfl
  | cons x xs ih =>
      intro data
      simp only [List.foldl_cons]
      rw [ih, h]

theorem swapRows_cols [Zero F]
    (M : DenseMatrix F) (rowA rowB : Nat) :
    (swapRows M rowA rowB).cols = M.cols := by
  unfold swapRows
  split <;> rfl

theorem swapRows_rows [Zero F]
    (M : DenseMatrix F) (rowA rowB : Nat) :
    (swapRows M rowA rowB).rows = M.rows := by
  unfold swapRows
  split <;> rfl

theorem swapRows_wf [Zero F] {M : DenseMatrix F} (hM : WellFormed M)
    (rowA rowB : Nat) : WellFormed (swapRows M rowA rowB) := by
  unfold swapRows
  split
  · exact hM
  · simpa [WellFormed, setD, Std.Legacy.Range.forIn_eq_forIn_range',
      list_foldl_array_size_of_eq] using hM

theorem swapRows_get_of_row_ne [Zero F] {M : DenseMatrix F}
    {rowA rowB row col : Nat} (hcol : col < M.cols)
    (hA : rowA ≠ row) (hB : rowB ≠ row) :
    (swapRows M rowA rowB).get row col = M.get row col := by
  by_cases hsame : rowA = rowB
  · simp [swapRows, hsame]
  · have hfold : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) →
      data.getD (M.index row col) 0 = M.data.getD (M.index row col) 0 →
      (List.foldl
          (fun data c =>
            setD (setD data (M.index rowA c) (M.get rowB c))
              (M.index rowB c) (M.get rowA c))
          data xs).getD (M.index row col) 0 =
        M.data.getD (M.index row col) 0 := by
      intro xs
      induction xs with
      | nil =>
          intro data _ hget
          exact hget
      | cons c xs ih =>
          intro data hxs hget
          simp only [List.foldl_cons]
          apply ih
          · intro d hd
            exact hxs d (by simp [hd])
          · rw [get_setD_index_ne M
                (setD data (M.index rowA c) (M.get rowB c))
                (hxs c (by simp)) hcol (Or.inl hB)]
            rw [get_setD_index_ne M data (hxs c (by simp)) hcol (Or.inl hA)]
            exact hget
    simpa [swapRows, hsame, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
      Array.getD_eq_getD_getElem?] using
      hfold (List.range' 0 M.cols) M.data
        (by
          intro c hc
          simpa using (List.mem_range'_1.mp hc).2)
        rfl

theorem swapRows_get_left [Zero F] {M : DenseMatrix F}
    (hM : WellFormed M) {rowA rowB col : Nat}
    (hrowA : rowA < M.rows) (hcol : col < M.cols) :
    (swapRows M rowA rowB).get rowA col = M.get rowB col := by
  by_cases hsame : rowA = rowB
  · simp [swapRows, hsame]
  · have hfold_not : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) → col ∉ xs →
      data.getD (M.index rowA col) 0 =
        (List.foldl
          (fun data c =>
            setD (setD data (M.index rowA c) (M.get rowB c))
              (M.index rowB c) (M.get rowA c))
          data xs).getD (M.index rowA col) 0 := by
      intro xs
      induction xs with
      | nil =>
          intro data _ _
          rfl
      | cons c xs ih =>
          intro data hxs hnot
          have hcne : c ≠ col := by
            intro hc
            apply hnot
            simp [hc]
          have hnotTail : col ∉ xs := by
            intro hmem
            apply hnot
            simp [hmem]
          simp only [List.foldl_cons]
          rw [← ih]
          · rw [get_setD_index_ne M
                (setD data (M.index rowA c) (M.get rowB c))
                (hxs c (by simp)) hcol (Or.inl (by intro h; exact hsame h.symm))]
            rw [get_setD_index_ne_same_row M data (hxs c (by simp)) hcol hcne]
          · intro d hd
            exact hxs d (by simp [hd])
          · exact hnotTail
    have hfold_mem : ∀ (xs : List Nat) (data : Array F),
        data.size = M.data.size →
        (∀ c, c ∈ xs → c < M.cols) → xs.Nodup → col ∈ xs →
        (List.foldl
            (fun data c =>
              setD (setD data (M.index rowA c) (M.get rowB c))
                (M.index rowB c) (M.get rowA c))
            data xs).getD (M.index rowA col) 0 =
          M.data.getD (M.index rowB col) 0 := by
      intro xs
      induction xs with
      | nil =>
          intro data _ _ _ hmem
          simp at hmem
      | cons c xs ih =>
          intro data hsize hxs hnodup hmem
          have hxsTail : ∀ d, d ∈ xs → d < M.cols := by
            intro d hd
            exact hxs d (by simp [hd])
          have hnodupTail : xs.Nodup := hnodup.tail
          by_cases hc : c = col
          · subst c
            simp only [List.foldl_cons]
            have hidx : M.index rowA col < data.size := by
              rw [hsize]
              exact index_lt_of_lt hM hrowA hcol
            have hset :
                (setD (setD data (M.index rowA col) (M.get rowB col))
                    (M.index rowB col) (M.get rowA col)).getD (M.index rowA col) 0 =
                  M.data.getD (M.index rowB col) 0 := by
              rw [get_setD_index_ne M
                (setD data (M.index rowA col) (M.get rowB col))
                hcol hcol (Or.inl (by intro h; exact hsame h.symm))]
              rw [get_setD_index_same hidx]
              rfl
            have hnotTail : col ∉ xs := (List.nodup_cons.mp hnodup).1
            rw [← hfold_not xs
              (setD (setD data (M.index rowA col) (M.get rowB col))
                (M.index rowB col) (M.get rowA col))]
            · exact hset
            · exact hxsTail
            · exact hnotTail
          · have hmemTail : col ∈ xs := by
              have hcolne : col ≠ c := by intro h; exact hc h.symm
              simpa [List.mem_cons, hcolne] using hmem
            simp only [List.foldl_cons]
            apply ih
            · simp [setD, hsize]
            · exact hxsTail
            · exact hnodupTail
            · exact hmemTail
    simpa [swapRows, hsame, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
      Array.getD_eq_getD_getElem?] using
      hfold_mem (List.range' 0 M.cols) M.data rfl
        (by
          intro c hc
          simpa using (List.mem_range'_1.mp hc).2)
        (List.nodup_range' (s := 0) (n := M.cols))
        (by simp [hcol])

theorem swapRows_get_right [Zero F] {M : DenseMatrix F}
    (hM : WellFormed M) {rowA rowB col : Nat}
    (hrowB : rowB < M.rows) (hcol : col < M.cols) :
    (swapRows M rowA rowB).get rowB col = M.get rowA col := by
  by_cases hsame : rowA = rowB
  · simp [swapRows, hsame]
  · have hfold_not : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) → col ∉ xs →
      data.getD (M.index rowB col) 0 =
        (List.foldl
          (fun data c =>
            setD (setD data (M.index rowA c) (M.get rowB c))
              (M.index rowB c) (M.get rowA c))
          data xs).getD (M.index rowB col) 0 := by
      intro xs
      induction xs with
      | nil =>
          intro data _ _
          rfl
      | cons c xs ih =>
          intro data hxs hnot
          have hcne : c ≠ col := by
            intro hc
            apply hnot
            simp [hc]
          have hnotTail : col ∉ xs := by
            intro hmem
            apply hnot
            simp [hmem]
          simp only [List.foldl_cons]
          rw [← ih]
          · rw [get_setD_index_ne_same_row M
                (setD data (M.index rowA c) (M.get rowB c))
                (hxs c (by simp)) hcol hcne]
            rw [get_setD_index_ne M data (hxs c (by simp)) hcol (Or.inl hsame)]
          · intro d hd
            exact hxs d (by simp [hd])
          · exact hnotTail
    have hfold_mem : ∀ (xs : List Nat) (data : Array F),
        data.size = M.data.size →
        (∀ c, c ∈ xs → c < M.cols) → xs.Nodup → col ∈ xs →
        (List.foldl
            (fun data c =>
              setD (setD data (M.index rowA c) (M.get rowB c))
                (M.index rowB c) (M.get rowA c))
            data xs).getD (M.index rowB col) 0 =
          M.data.getD (M.index rowA col) 0 := by
      intro xs
      induction xs with
      | nil =>
          intro data _ _ _ hmem
          simp at hmem
      | cons c xs ih =>
          intro data hsize hxs hnodup hmem
          have hxsTail : ∀ d, d ∈ xs → d < M.cols := by
            intro d hd
            exact hxs d (by simp [hd])
          have hnodupTail : xs.Nodup := hnodup.tail
          by_cases hc : c = col
          · subst c
            simp only [List.foldl_cons]
            have hidx : M.index rowB col < (setD data (M.index rowA col)
                (M.get rowB col)).size := by
              simp [setD, hsize, index_lt_of_lt hM hrowB hcol]
            have hset :
                (setD (setD data (M.index rowA col) (M.get rowB col))
                    (M.index rowB col) (M.get rowA col)).getD (M.index rowB col) 0 =
                  M.data.getD (M.index rowA col) 0 := by
              rw [get_setD_index_same hidx]
              rfl
            have hnotTail : col ∉ xs := (List.nodup_cons.mp hnodup).1
            rw [← hfold_not xs
              (setD (setD data (M.index rowA col) (M.get rowB col))
                (M.index rowB col) (M.get rowA col))]
            · exact hset
            · exact hxsTail
            · exact hnotTail
          · have hmemTail : col ∈ xs := by
              have hcolne : col ≠ c := by intro h; exact hc h.symm
              simpa [List.mem_cons, hcolne] using hmem
            simp only [List.foldl_cons]
            apply ih
            · simp [setD, hsize]
            · exact hxsTail
            · exact hnodupTail
            · exact hmemTail
    simpa [swapRows, hsame, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
      Array.getD_eq_getD_getElem?] using
      hfold_mem (List.range' 0 M.cols) M.data rfl
        (by
          intro c hc
          simpa using (List.mem_range'_1.mp hc).2)
        (List.nodup_range' (s := 0) (n := M.cols))
        (by simp [hcol])

theorem list_forIn_addScaledRow_rows [Field F]
    (rows : List Nat) (pivotRow pivotCol : Nat) (out : DenseMatrix F) :
    (Id.run (forIn rows out fun row r =>
      if row = pivotRow then
        pure (ForInStep.yield r)
      else
        pure (ForInStep.yield
          (addScaledRow r row pivotRow (-(r.get row pivotCol)))) :
      Id (DenseMatrix F))).rows = out.rows := by
  induction rows generalizing out with
  | nil => simp
  | cons row rows ih =>
      by_cases hrow : row = pivotRow
      · simpa [List.forIn_cons, hrow] using ih out
      · have hih := ih (addScaledRow out row pivotRow (-(out.get row pivotCol)))
        simpa [List.forIn_cons, hrow, addScaledRow] using hih

theorem list_forIn_addScaledRow_cols [Field F]
    (rows : List Nat) (pivotRow pivotCol : Nat) (out : DenseMatrix F) :
    (Id.run (forIn rows out fun row r =>
      if row = pivotRow then
        pure (ForInStep.yield r)
      else
        pure (ForInStep.yield
          (addScaledRow r row pivotRow (-(r.get row pivotCol)))) :
      Id (DenseMatrix F))).cols = out.cols := by
  induction rows generalizing out with
  | nil => simp
  | cons row rows ih =>
      by_cases hrow : row = pivotRow
      · simpa [List.forIn_cons, hrow] using ih out
      · have hih := ih (addScaledRow out row pivotRow (-(out.get row pivotCol)))
        simpa [List.forIn_cons, hrow, addScaledRow] using hih

theorem normalizeAndEliminate_cols [Field F] [BEq F]
    (M : DenseMatrix F) (pivotRow pivotCol : Nat) :
    (normalizeAndEliminate M pivotRow pivotCol).cols = M.cols := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · simp [hp]
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simpa [scaleRow] using
      (list_forIn_addScaledRow_cols
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        pivotRow pivotCol (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹))

theorem normalizeAndEliminate_rows [Field F] [BEq F]
    (M : DenseMatrix F) (pivotRow pivotCol : Nat) :
    (normalizeAndEliminate M pivotRow pivotCol).rows = M.rows := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · simp [hp]
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simpa [scaleRow] using
      (list_forIn_addScaledRow_rows
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        pivotRow pivotCol (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹))

theorem scaleRow_get_of_row_ne [Field F] {M : DenseMatrix F}
    {r row col : Nat} (factor : F) (hcol : col < M.cols) (hneq : r ≠ row) :
    (scaleRow M r factor).get row col = M.get row col := by
  have hfold : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) →
      data.getD (M.index row col) 0 = M.data.getD (M.index row col) 0 →
      (List.foldl (fun data c => setD data (M.index r c) (factor * M.get r c))
          data xs).getD (M.index row col) 0 =
        M.data.getD (M.index row col) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro data _ hget
        exact hget
    | cons c xs ih =>
        intro data hxs hget
        simp only [List.foldl_cons]
        apply ih
        · intro d hd
          exact hxs d (by simp [hd])
        · rw [get_setD_index_ne M data (hxs c (by simp)) hcol (Or.inl hneq)]
          exact hget
  simpa [scaleRow, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
    Array.getD_eq_getD_getElem?] using
    hfold (List.range' 0 M.cols) M.data
      (by
        intro c hc
        simpa using (List.mem_range'_1.mp hc).2)
      rfl

theorem scaleRow_wf [Field F] {M : DenseMatrix F} (hM : WellFormed M)
    (row : Nat) (factor : F) : WellFormed (scaleRow M row factor) := by
  simpa [scaleRow, WellFormed, setD, Std.Legacy.Range.forIn_eq_forIn_range',
    list_foldl_array_size_of_eq] using hM

theorem scaleRow_get_same [Field F] {M : DenseMatrix F}
    (hM : WellFormed M) {r col : Nat} (hr : r < M.rows) (hcol : col < M.cols)
    (factor : F) :
    (scaleRow M r factor).get r col = factor * M.get r col := by
  have hfold_not : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) → col ∉ xs →
      data.getD (M.index r col) 0 =
        (List.foldl (fun data c => setD data (M.index r c) (factor * M.get r c))
          data xs).getD (M.index r col) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro data _ _
        rfl
    | cons c xs ih =>
        intro data hxs hnot
        have hcne : c ≠ col := by
          intro hc
          apply hnot
          simp [hc]
        have hnotTail : col ∉ xs := by
          intro hmem
          apply hnot
          simp [hmem]
        simp only [List.foldl_cons]
        rw [← ih]
        · rw [get_setD_index_ne_same_row M data (hxs c (by simp)) hcol hcne]
        · intro d hd
          exact hxs d (by simp [hd])
        · exact hnotTail
  have hfold_mem : ∀ (xs : List Nat) (data : Array F),
      data.size = M.data.size →
      (∀ c, c ∈ xs → c < M.cols) → xs.Nodup → col ∈ xs →
      (List.foldl (fun data c => setD data (M.index r c) (factor * M.get r c))
          data xs).getD (M.index r col) 0 =
        factor * M.data.getD (M.index r col) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro data _ _ _ hmem
        simp at hmem
    | cons c xs ih =>
        intro data hsize hxs hnodup hmem
        have hxsTail : ∀ d, d ∈ xs → d < M.cols := by
          intro d hd
          exact hxs d (by simp [hd])
        have hnodupTail : xs.Nodup := hnodup.tail
        by_cases hc : c = col
        · subst c
          simp only [List.foldl_cons]
          have hidx : M.index r col < data.size := by
            rw [hsize]
            exact index_lt_of_lt hM hr hcol
          have hset :
              (setD data (M.index r col) (factor * M.get r col)).getD
                  (M.index r col) 0 =
                factor * M.data.getD (M.index r col) 0 := by
            rw [get_setD_index_same hidx]
            rfl
          have hnotTail : col ∉ xs := (List.nodup_cons.mp hnodup).1
          rw [← hfold_not xs (setD data (M.index r col) (factor * M.get r col))]
          · exact hset
          · exact hxsTail
          · exact hnotTail
        · have hmemTail : col ∈ xs := by
            have hcolne : col ≠ c := by intro h; exact hc h.symm
            simpa [List.mem_cons, hcolne] using hmem
          simp only [List.foldl_cons]
          apply ih
          · simp [setD, hsize]
          · exact hxsTail
          · exact hnodupTail
          · exact hmemTail
  simpa [scaleRow, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
    Array.getD_eq_getD_getElem?] using
    hfold_mem (List.range' 0 M.cols) M.data rfl
      (by
        intro c hc
        simpa using (List.mem_range'_1.mp hc).2)
      (List.nodup_range' (s := 0) (n := M.cols))
      (by simp [hcol])

theorem addScaledRow_get_of_row_ne [Field F] {M : DenseMatrix F}
    {target source row col : Nat} (factor : F) (hcol : col < M.cols)
    (hneq : target ≠ row) :
    (addScaledRow M target source factor).get row col = M.get row col := by
  have hfold : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) →
      data.getD (M.index row col) 0 = M.data.getD (M.index row col) 0 →
      (List.foldl
          (fun data c =>
            setD data (M.index target c) (M.get target c + factor * M.get source c))
          data xs).getD (M.index row col) 0 =
        M.data.getD (M.index row col) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro data _ hget
        exact hget
    | cons c xs ih =>
        intro data hxs hget
        simp only [List.foldl_cons]
        apply ih
        · intro d hd
          exact hxs d (by simp [hd])
        · rw [get_setD_index_ne M data (hxs c (by simp)) hcol (Or.inl hneq)]
          exact hget
  simpa [addScaledRow, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
    Array.getD_eq_getD_getElem?] using
    hfold (List.range' 0 M.cols) M.data
      (by
        intro c hc
        simpa using (List.mem_range'_1.mp hc).2)
      rfl

theorem addScaledRow_wf [Field F] {M : DenseMatrix F} (hM : WellFormed M)
    (target source : Nat) (factor : F) : WellFormed (addScaledRow M target source factor) := by
  simpa [addScaledRow, WellFormed, setD, Std.Legacy.Range.forIn_eq_forIn_range',
    list_foldl_array_size_of_eq] using hM

theorem addScaledRow_get_same [Field F] {M : DenseMatrix F}
    (hM : WellFormed M) {target source col : Nat}
    (htarget : target < M.rows) (hcol : col < M.cols) (factor : F) :
    (addScaledRow M target source factor).get target col =
      M.get target col + factor * M.get source col := by
  have hfold_not : ∀ (xs : List Nat) (data : Array F),
      (∀ c, c ∈ xs → c < M.cols) → col ∉ xs →
      data.getD (M.index target col) 0 =
        (List.foldl
          (fun data c =>
            setD data (M.index target c) (M.get target c + factor * M.get source c))
          data xs).getD (M.index target col) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro data _ _
        rfl
    | cons c xs ih =>
        intro data hxs hnot
        have hcne : c ≠ col := by
          intro hc
          apply hnot
          simp [hc]
        have hnotTail : col ∉ xs := by
          intro hmem
          apply hnot
          simp [hmem]
        simp only [List.foldl_cons]
        rw [← ih]
        · rw [get_setD_index_ne_same_row M data (hxs c (by simp)) hcol hcne]
        · intro d hd
          exact hxs d (by simp [hd])
        · exact hnotTail
  have hfold_mem : ∀ (xs : List Nat) (data : Array F),
      data.size = M.data.size →
      (∀ c, c ∈ xs → c < M.cols) → xs.Nodup → col ∈ xs →
      (List.foldl
          (fun data c =>
            setD data (M.index target c) (M.get target c + factor * M.get source c))
          data xs).getD (M.index target col) 0 =
        M.data.getD (M.index target col) 0 + factor * M.data.getD (M.index source col) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro data _ _ _ hmem
        simp at hmem
    | cons c xs ih =>
        intro data hsize hxs hnodup hmem
        have hxsTail : ∀ d, d ∈ xs → d < M.cols := by
          intro d hd
          exact hxs d (by simp [hd])
        have hnodupTail : xs.Nodup := hnodup.tail
        by_cases hc : c = col
        · subst c
          simp only [List.foldl_cons]
          have hidx : M.index target col < data.size := by
            rw [hsize]
            exact index_lt_of_lt hM htarget hcol
          have hset :
              (setD data (M.index target col)
                  (M.get target col + factor * M.get source col)).getD
                  (M.index target col) 0 =
                M.data.getD (M.index target col) 0 +
                  factor * M.data.getD (M.index source col) 0 := by
            rw [get_setD_index_same hidx]
            rfl
          have hnotTail : col ∉ xs := (List.nodup_cons.mp hnodup).1
          rw [← hfold_not xs
            (setD data (M.index target col)
              (M.get target col + factor * M.get source col))]
          · exact hset
          · exact hxsTail
          · exact hnotTail
        · have hmemTail : col ∈ xs := by
            have hcolne : col ≠ c := by intro h; exact hc h.symm
            simpa [List.mem_cons, hcolne] using hmem
          simp only [List.foldl_cons]
          apply ih
          · simp [setD, hsize]
          · exact hxsTail
          · exact hnodupTail
          · exact hmemTail
  simpa [addScaledRow, get, index, Std.Legacy.Range.forIn_eq_forIn_range',
    Array.getD_eq_getD_getElem?] using
    hfold_mem (List.range' 0 M.cols) M.data rfl
      (by
        intro c hc
        simpa using (List.mem_range'_1.mp hc).2)
      (List.nodup_range' (s := 0) (n := M.cols))
      (by simp [hcol])

theorem dotRow_ext_rows [Semiring F] {M N : DenseMatrix F}
    {rowN rowM : Nat} {v : Array F} (hcols : N.cols = M.cols)
    (hget : ∀ col, col < M.cols → N.get rowN col = M.get rowM col) :
    N.dotRow rowN v = M.dotRow rowM v := by
  unfold dotRow
  rw [hcols]
  have hfold : ∀ (xs : List Nat) (acc : F),
      (∀ col, col ∈ xs → col < M.cols) →
      xs.foldl (fun acc col => acc + N.get rowN col * v.getD col 0) acc =
        xs.foldl (fun acc col => acc + M.get rowM col * v.getD col 0) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        rfl
    | cons col xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        rw [hget col (hxs col (by simp))]
        apply ih
        intro c hc
        exact hxs c (by simp [hc])
  exact hfold (List.range M.cols) 0 (by
    intro c hc
    exact List.mem_range.mp hc)

theorem dotRow_scaleRow_same [Field F] {M : DenseMatrix F}
    (hM : WellFormed M) {row : Nat} (hrow : row < M.rows)
    (factor : F) (v : Array F) :
    (scaleRow M row factor).dotRow row v = factor * M.dotRow row v := by
  unfold dotRow
  change
    (List.range M.cols).foldl
        (fun acc col => acc + (scaleRow M row factor).get row col * v.getD col 0) 0 =
      factor *
        (List.range M.cols).foldl
          (fun acc col => acc + M.get row col * v.getD col 0) 0
  have hfold : ∀ (xs : List Nat) (accScaled accBase : F),
      (∀ c, c ∈ xs → c < M.cols) →
      accScaled = factor * accBase →
      xs.foldl
          (fun acc col => acc + (scaleRow M row factor).get row col * v.getD col 0)
          accScaled =
        factor *
          xs.foldl (fun acc col => acc + M.get row col * v.getD col 0) accBase := by
    intro xs
    induction xs with
    | nil =>
        intro accScaled accBase _ hacc
        simpa using hacc
    | cons c xs ih =>
        intro accScaled accBase hxs hacc
        simp only [List.foldl_cons]
        rw [scaleRow_get_same hM hrow (hxs c (by simp)) factor]
        apply ih
        · intro d hd
          exact hxs d (by simp [hd])
        · rw [hacc]
          ring
  exact hfold (List.range M.cols) 0 0
    (by
      intro c hc
      exact List.mem_range.mp hc)
    (by simp)

theorem dotRow_addScaledRow_same [Field F] {M : DenseMatrix F}
    (hM : WellFormed M) {target source : Nat} (htarget : target < M.rows)
    (factor : F) (v : Array F) :
    (addScaledRow M target source factor).dotRow target v =
      M.dotRow target v + factor * M.dotRow source v := by
  unfold dotRow
  change
    (List.range M.cols).foldl
        (fun acc col =>
          acc + (addScaledRow M target source factor).get target col * v.getD col 0) 0 =
      (List.range M.cols).foldl
          (fun acc col => acc + M.get target col * v.getD col 0) 0 +
        factor *
          (List.range M.cols).foldl
            (fun acc col => acc + M.get source col * v.getD col 0) 0
  have hfold : ∀ (xs : List Nat) (accNew accTarget accSource : F),
      (∀ c, c ∈ xs → c < M.cols) →
      accNew = accTarget + factor * accSource →
      xs.foldl
          (fun acc col =>
            acc + (addScaledRow M target source factor).get target col * v.getD col 0)
          accNew =
        xs.foldl (fun acc col => acc + M.get target col * v.getD col 0) accTarget +
          factor *
            xs.foldl (fun acc col => acc + M.get source col * v.getD col 0) accSource := by
    intro xs
    induction xs with
    | nil =>
        intro accNew accTarget accSource _ hacc
        simpa using hacc
    | cons c xs ih =>
        intro accNew accTarget accSource hxs hacc
        simp only [List.foldl_cons]
        rw [addScaledRow_get_same hM htarget (hxs c (by simp)) factor]
        apply ih
        · intro d hd
          exact hxs d (by simp [hd])
        · rw [hacc]
          ring
  exact hfold (List.range M.cols) 0 0 0
    (by
      intro c hc
      exact List.mem_range.mp hc)
    (by simp)

theorem dotRow_swapRows_left [Semiring F] {M : DenseMatrix F}
    (hM : WellFormed M) {rowA rowB : Nat} (hrowA : rowA < M.rows) (v : Array F) :
    (swapRows M rowA rowB).dotRow rowA v = M.dotRow rowB v := by
  exact dotRow_ext_rows (M := M) (N := swapRows M rowA rowB)
    (rowN := rowA) (rowM := rowB)
    (by exact swapRows_cols M rowA rowB)
    (fun col hcol => swapRows_get_left hM hrowA hcol)

theorem dotRow_swapRows_right [Semiring F] {M : DenseMatrix F}
    (hM : WellFormed M) {rowA rowB : Nat} (hrowB : rowB < M.rows) (v : Array F) :
    (swapRows M rowA rowB).dotRow rowB v = M.dotRow rowA v := by
  exact dotRow_ext_rows (M := M) (N := swapRows M rowA rowB)
    (rowN := rowB) (rowM := rowA)
    (by exact swapRows_cols M rowA rowB)
    (fun col hcol => swapRows_get_right hM hrowB hcol)

theorem dotRow_swapRows_of_ne [Semiring F] {M : DenseMatrix F}
    {rowA rowB row : Nat} (hrowA : rowA ≠ row) (hrowB : rowB ≠ row)
    (v : Array F) :
    (swapRows M rowA rowB).dotRow row v = M.dotRow row v := by
  exact dotRow_ext_rows (M := M) (N := swapRows M rowA rowB)
    (rowN := row) (rowM := row)
    (by exact swapRows_cols M rowA rowB)
    (fun col hcol => swapRows_get_of_row_ne hcol hrowA hrowB)

theorem dotRow_scaleRow_of_ne [Field F] {M : DenseMatrix F}
    {scale row : Nat} (factor : F) (hneq : scale ≠ row) (v : Array F) :
    (scaleRow M scale factor).dotRow row v = M.dotRow row v := by
  exact dotRow_ext_rows (M := M) (N := scaleRow M scale factor)
    (rowN := row) (rowM := row)
    (by simp [scaleRow])
    (fun col hcol => scaleRow_get_of_row_ne factor hcol hneq)

theorem dotRow_addScaledRow_of_ne [Field F] {M : DenseMatrix F}
    {target source row : Nat} (factor : F) (hneq : target ≠ row) (v : Array F) :
    (addScaledRow M target source factor).dotRow row v = M.dotRow row v := by
  exact dotRow_ext_rows (M := M) (N := addScaledRow M target source factor)
    (rowN := row) (rowM := row)
    (by simp [addScaledRow])
    (fun col hcol => addScaledRow_get_of_row_ne factor hcol hneq)

theorem isHomogeneousSolution_swapRows_of_solution [Field F]
    {M : DenseMatrix F} {v : Array F} {rowA rowB : Nat}
    (hM : WellFormed M) (hrowA : rowA < M.rows) (hrowB : rowB < M.rows)
    (hsol : IsHomogeneousSolution M v) :
    IsHomogeneousSolution (swapRows M rowA rowB) v := by
  intro row hrow
  have hrowM : row < M.rows := by simpa [swapRows_rows] using hrow
  by_cases hA : row = rowA
  · subst row
    rw [dotRow_swapRows_left (M := M) (rowA := rowA) (rowB := rowB)
      hM hrowA v]
    exact hsol rowB hrowB
  · by_cases hB : row = rowB
    · subst row
      rw [dotRow_swapRows_right (M := M) (rowA := rowA) (rowB := rowB)
        hM hrowB v]
      exact hsol rowA hrowA
    · rw [dotRow_swapRows_of_ne (M := M) (rowA := rowA) (rowB := rowB)
        (row := row) (by intro h; exact hA h.symm) (by intro h; exact hB h.symm) v]
      exact hsol row hrowM

theorem isHomogeneousSolution_scaleRow_of_solution [Field F]
    {M : DenseMatrix F} {v : Array F} {target : Nat} (hM : WellFormed M)
    (htarget : target < M.rows) (factor : F)
    (hsol : IsHomogeneousSolution M v) :
    IsHomogeneousSolution (scaleRow M target factor) v := by
  intro row hrow
  have hrowM : row < M.rows := by simpa [scaleRow] using hrow
  by_cases htargetRow : target = row
  · subst row
    rw [dotRow_scaleRow_same hM htarget factor v]
    rw [hsol target htarget]
    simp
  · rw [dotRow_scaleRow_of_ne (M := M) (scale := target) (row := row)
      factor htargetRow v]
    exact hsol row hrowM

theorem isHomogeneousSolution_addScaledRow_of_solution [Field F]
    {M : DenseMatrix F} {v : Array F} {target source : Nat}
    (hM : WellFormed M) (htarget : target < M.rows) (hsource : source < M.rows)
    (factor : F) (hsol : IsHomogeneousSolution M v) :
    IsHomogeneousSolution (addScaledRow M target source factor) v := by
  intro row hrow
  have hrowM : row < M.rows := by simpa [addScaledRow] using hrow
  by_cases htargetRow : target = row
  · subst row
    rw [dotRow_addScaledRow_same hM htarget factor v]
    rw [hsol target htarget, hsol source hsource]
    simp
  · rw [dotRow_addScaledRow_of_ne (M := M) (target := target) (source := source)
      (row := row) factor htargetRow v]
    exact hsol row hrowM

theorem isHomogeneousSolution_of_swapRows_solution [Field F]
    {M : DenseMatrix F} {v : Array F} {rowA rowB : Nat}
    (hM : WellFormed M) (hrowA : rowA < M.rows) (hrowB : rowB < M.rows)
    (hsol : IsHomogeneousSolution (swapRows M rowA rowB) v) :
    IsHomogeneousSolution M v := by
  intro row hrow
  by_cases hA : row = rowA
  · subst row
    have hrowB' : rowB < (swapRows M rowA rowB).rows := by
      simpa [swapRows_rows] using hrowB
    have hdot := hsol rowB hrowB'
    rw [dotRow_swapRows_right (M := M) (rowA := rowA) (rowB := rowB)
      hM hrowB v] at hdot
    exact hdot
  · by_cases hB : row = rowB
    · subst row
      have hrowA' : rowA < (swapRows M rowA rowB).rows := by
        simpa [swapRows_rows] using hrowA
      have hdot := hsol rowA hrowA'
      rw [dotRow_swapRows_left (M := M) (rowA := rowA) (rowB := rowB)
        hM hrowA v] at hdot
      exact hdot
    · have hrow' : row < (swapRows M rowA rowB).rows := by
        simpa [swapRows_rows] using hrow
      have hdot := hsol row hrow'
      rw [dotRow_swapRows_of_ne (M := M) (rowA := rowA) (rowB := rowB)
        (row := row) (by intro h; exact hA h.symm) (by intro h; exact hB h.symm) v] at hdot
      exact hdot

theorem isHomogeneousSolution_of_scaleRow_solution [Field F]
    {M : DenseMatrix F} {v : Array F} {target : Nat} (hM : WellFormed M)
    (htarget : target < M.rows) {factor : F} (hfactor : factor ≠ 0)
    (hsol : IsHomogeneousSolution (scaleRow M target factor) v) :
    IsHomogeneousSolution M v := by
  intro row hrow
  by_cases htargetRow : target = row
  · subst row
    have htarget' : target < (scaleRow M target factor).rows := by
      simpa [scaleRow] using htarget
    have hdot := hsol target htarget'
    rw [dotRow_scaleRow_same hM htarget factor v] at hdot
    exact (mul_eq_zero.mp hdot).resolve_left hfactor
  · have hrow' : row < (scaleRow M target factor).rows := by
      simpa [scaleRow] using hrow
    have hdot := hsol row hrow'
    rw [dotRow_scaleRow_of_ne (M := M) (scale := target) (row := row)
      factor htargetRow v] at hdot
    exact hdot

theorem isHomogeneousSolution_of_addScaledRow_solution [Field F]
    {M : DenseMatrix F} {v : Array F} {target source : Nat}
    (hM : WellFormed M) (htarget : target < M.rows) (hsource : source < M.rows)
    (hts : target ≠ source) (factor : F)
    (hsol : IsHomogeneousSolution (addScaledRow M target source factor) v) :
    IsHomogeneousSolution M v := by
  intro row hrow
  by_cases htargetRow : target = row
  · subst row
    have htarget' : target < (addScaledRow M target source factor).rows := by
      simpa [addScaledRow] using htarget
    have hsource' : source < (addScaledRow M target source factor).rows := by
      simpa [addScaledRow] using hsource
    have hsourceDot := hsol source hsource'
    rw [dotRow_addScaledRow_of_ne (M := M) (target := target) (source := source)
      (row := source) factor hts v] at hsourceDot
    have htargetDot := hsol target htarget'
    rw [dotRow_addScaledRow_same hM htarget factor v] at htargetDot
    rw [hsourceDot, mul_zero, add_zero] at htargetDot
    exact htargetDot
  · have hrow' : row < (addScaledRow M target source factor).rows := by
      simpa [addScaledRow] using hrow
    have hdot := hsol row hrow'
    rw [dotRow_addScaledRow_of_ne (M := M) (target := target) (source := source)
      (row := row) factor htargetRow v] at hdot
    exact hdot

end DenseMatrix

end CompPoly
