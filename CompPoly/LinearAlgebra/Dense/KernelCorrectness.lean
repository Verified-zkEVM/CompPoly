/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.Kernel
import CompPoly.LinearAlgebra.Dense.RrefShape
import Mathlib.Data.Finset.Card

/-!
# Dense Homogeneous-Kernel Correctness

Correctness contracts for executable dense homogeneous-kernel witnesses.
-/

namespace CompPoly

namespace DenseMatrix

private theorem containsNat_eq_true_iff {xs : Array Nat} {x : Nat} :
    containsNat xs x = true ↔ x ∈ xs.toList := by
  unfold containsNat
  rw [Array.any_eq_true']
  constructor
  · rintro ⟨y, hy, hbeq⟩
    have hyx : y = x := beq_iff_eq.mp hbeq
    simpa [hyx] using Array.mem_def.mp hy
  · intro hx
    refine ⟨x, Array.mem_def.mpr hx, ?_⟩
    exact beq_iff_eq.mpr rfl

private theorem containsNat_eq_true_iff_exists {xs : Array Nat} {x : Nat} :
    containsNat xs x = true ↔ ∃ i, i < xs.size ∧ xs.getD i 0 = x := by
  constructor
  · intro h
    have hxList := containsNat_eq_true_iff.mp h
    rcases List.mem_iff_get.mp hxList with ⟨⟨i, hi⟩, hget⟩
    refine ⟨i, ?_, ?_⟩
    · exact hi
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      simpa using hget
  · rintro ⟨i, hi, hgetD⟩
    apply containsNat_eq_true_iff.mpr
    rw [← Array.mem_def]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at hgetD
    rw [← hgetD]
    exact Array.getElem_mem (xs := xs) hi

private theorem containsNat_getD_ne {xs : Array Nat} {x i : Nat}
    (hcontains : containsNat xs x = false) (hi : i < xs.size) :
    xs.getD i 0 ≠ x := by
  intro hget
  have htrue : containsNat xs x = true :=
    containsNat_eq_true_iff_exists.mpr ⟨i, hi, hget⟩
  simp [hcontains] at htrue

private theorem all_columns_pivot_of_no_free_columns {pivots : Array Nat} {cols : Nat}
    (hfree : (freeColumns cols pivots).size = 0) :
    ∀ c, c < cols → containsNat pivots c = true := by
  intro c hc
  by_cases hcontains : containsNat pivots c = true
  · exact hcontains
  · exfalso
    have hfalse : containsNat pivots c = false := by
      cases hv : containsNat pivots c <;> simp [hv] at hcontains ⊢
    have hmem : c ∈ (List.range cols).filter fun col => !(containsNat pivots col) := by
      rw [List.mem_filter]
      constructor
      · exact List.mem_range.mpr hc
      · simp [hfalse]
    have hlist : c ∈ (freeColumns cols pivots).toList := by
      simpa [freeColumns] using hmem
    have hlen : (freeColumns cols pivots).toList.length = 0 := by
      simpa using hfree
    have hnil : (freeColumns cols pivots).toList = [] :=
      List.eq_nil_of_length_eq_zero hlen
    rw [hnil] at hlist
    simp at hlist

private theorem pivots_size_ge_cols_of_no_free_columns {pivots : Array Nat} {cols : Nat}
    (hfree : (freeColumns cols pivots).size = 0) : cols ≤ pivots.size := by
  classical
  have hall := all_columns_pivot_of_no_free_columns hfree
  have hsub : Finset.range cols ⊆ pivots.toList.toFinset := by
    intro c hc
    have hcList : c ∈ pivots.toList :=
      containsNat_eq_true_iff.mp (hall c (Finset.mem_range.mp hc))
    simpa using hcList
  have hcard := Finset.card_le_card hsub
  have hpivCard := List.toFinset_card_le pivots.toList
  have hcols : (Finset.range cols).card = cols := Finset.card_range cols
  have hpivlen : pivots.toList.length = pivots.size := by simp
  omega

theorem homogeneousWitness_eq_none_iff [Field F] [BEq F] (M : DenseMatrix F) :
    homogeneousWitness M = none ↔ (homogeneousKernelBasis M).size = 0 := by
  unfold homogeneousWitness
  by_cases h : (homogeneousKernelBasis M).size = 0
  · simp [h]
  · simp [h]

/-- A matrix with more columns than rows has an executable homogeneous witness. -/
theorem homogeneousWitness_exists_of_rows_lt_cols [Field F] [BEq F] [LawfulBEq F]
    (M : DenseMatrix F) (h : M.rows < M.cols) :
    ∃ v, homogeneousWitness M = some v := by
  cases hw : homogeneousWitness M with
  | some v =>
      exact ⟨v, rfl⟩
  | none =>
      have hbasis := (homogeneousWitness_eq_none_iff M).mp hw
      have hfree : (freeColumns M.cols (rref M).pivots).size = 0 := by
        simpa [homogeneousKernelBasis] using hbasis
      have hcols_le_pivots := pivots_size_ge_cols_of_no_free_columns hfree
      have hpivots_le_rows := rref_pivots_size_le_rows M
      omega

private theorem basisVectorForFreeColumn_size [Field F] [BEq F]
    (A : DenseMatrix F) (pivots : Array Nat) (free : Nat) :
    (basisVectorForFreeColumn A pivots free).size = A.cols := by
  simp [basisVectorForFreeColumn]

private theorem freeColumns_mem_lt {cols : Nat} {pivots : Array Nat} {x : Nat}
    (h : x ∈ freeColumns cols pivots) : x < cols := by
  have hlist : x ∈ (freeColumns cols pivots).toList := Array.mem_def.mp h
  unfold freeColumns at hlist
  simp at hlist
  exact hlist.1

private theorem freeColumns_mem_not_contains {cols : Nat} {pivots : Array Nat} {x : Nat}
    (h : x ∈ freeColumns cols pivots) : containsNat pivots x = false := by
  have hlist : x ∈ (freeColumns cols pivots).toList := Array.mem_def.mp h
  unfold freeColumns at hlist
  simp at hlist
  exact hlist.2

private theorem list_find?_some_mem {α : Type*} {p : α → Bool} {xs : List α} {x : α}
    (h : xs.find? p = some x) : x ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons y ys ih =>
      by_cases hp : p y = true
      · simp [List.find?, hp] at h
        subst x
        simp
      · simp [List.find?, hp] at h
        exact List.mem_cons.mpr (Or.inr (ih h))

private theorem pivotRowOfColumn?_some_prop {pivots : Array Nat} {col row : Nat}
    (h : pivotRowOfColumn? pivots col = some row) :
    row < pivots.size ∧ pivots.getD row 0 = col := by
  unfold pivotRowOfColumn? at h
  have hmem := list_find?_some_mem h
  have hpred := List.find?_some h
  exact ⟨List.mem_range.mp hmem, beq_iff_eq.mp hpred⟩

private theorem pivotRowOfColumn?_eq_some_of_getD {pivots : Array Nat}
    (hstrict : PivotColumnsStrict pivots) {row : Nat} (hrow : row < pivots.size) :
    pivotRowOfColumn? pivots (pivots.getD row 0) = some row := by
  unfold pivotRowOfColumn?
  have hexists : ((List.range pivots.size).find?
      (fun r => pivots.getD r 0 == pivots.getD row 0)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨row, List.mem_range.mpr hrow, ?_⟩
    exact beq_iff_eq.mpr rfl
  cases hfind : (List.range pivots.size).find?
      (fun r => pivots.getD r 0 == pivots.getD row 0) with
  | none =>
      have hnone := List.find?_eq_none.mp hfind row (List.mem_range.mpr hrow)
      have hpred : (pivots.getD row 0 == pivots.getD row 0) = true :=
        beq_iff_eq.mpr rfl
      exact (hnone hpred).elim
  | some r =>
      have hmem := list_find?_some_mem hfind
      have hr : r < pivots.size := List.mem_range.mp hmem
      have hpred := List.find?_some hfind
      have heq : pivots.getD r 0 = pivots.getD row 0 := beq_iff_eq.mp hpred
      have hrrow : r = row := by
        by_contra hne
        exact pivotColumnsStrict_getD_ne hstrict hr hrow hne heq
      subst r
      rfl

private theorem pivotRow_basisVectorForFreeColumn_term [Field F] [BEq F]
    {A : DenseMatrix F} {pivots : Array Nat} {row free c : Nat}
    (hshape : PivotColumnsShaped A pivots) (hstrict : PivotColumnsStrict pivots)
    (hrow : row < pivots.size) (hfree : free < A.cols)
    (hnotFree : containsNat pivots free = false) (hc : c < A.cols) :
    A.get row c * (basisVectorForFreeColumn A pivots free).getD c 0 =
      if c = free then A.get row free
      else if c = pivots.getD row 0 then -A.get row free else 0 := by
  have hrowA : row < A.rows := (hshape row hrow).1
  have hpivotCol : pivots.getD row 0 < A.cols := (hshape row hrow).2.1
  by_cases hcfree : c = free
  · subst c
    have hcoord : (basisVectorForFreeColumn A pivots free).getD free 0 = 1 := by
      simp [basisVectorForFreeColumn, hfree]
    simp [hcoord]
  · by_cases hcpivot : c = pivots.getD row 0
    · subst c
      have hcoord :
          (basisVectorForFreeColumn A pivots free).getD (pivots.getD row 0) 0 =
            -A.get row free := by
        have hpiv_ne_free : ¬(pivots.getD row 0 == free) := by
          intro hb
          have heq : pivots.getD row 0 = free := beq_iff_eq.mp hb
          exact containsNat_getD_ne hnotFree hrow heq
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_getElem]
        · have hoptEq : pivots[row]?.getD 0 = pivots.getD row 0 := by
            rw [Array.getD_eq_getD_getElem?]
          have hnotOpt : ¬pivots[row]?.getD 0 = free := by
            intro h
            apply hcfree
            rw [← hoptEq]
            exact h
          have hfindOpt : pivotRowOfColumn? pivots (pivots[row]?.getD 0) = some row := by
            rw [hoptEq]
            exact pivotRowOfColumn?_eq_some_of_getD hstrict hrow
          simp [basisVectorForFreeColumn, hnotOpt, hfindOpt]
        · simpa [basisVectorForFreeColumn] using hpivotCol
      have hA : A.get row (pivots.getD row 0) = 1 :=
        by simpa using (hshape row hrow).2.2 row hrowA
      have hnotOpt : ¬pivots[row]?.getD 0 = free := by
        intro h
        apply hcfree
        simpa [Array.getD_eq_getD_getElem?] using h
      rw [hcoord, hA]
      simp [hnotOpt]
    · cases hp : pivotRowOfColumn? pivots c with
      | none =>
          have hcoord : (basisVectorForFreeColumn A pivots free).getD c 0 = 0 := by
            have hc_ne_free : ¬(c == free) := by
              intro hb
              exact hcfree (beq_iff_eq.mp hb)
            rw [Array.getD_eq_getD_getElem?]
            rw [Array.getElem?_eq_getElem]
            · simp [basisVectorForFreeColumn, hcfree, hp]
            · simpa [basisVectorForFreeColumn] using hc
          rw [hcoord]
          have hnotPivotOpt : ¬c = pivots[row]?.getD 0 := by
            intro h
            apply hcpivot
            simpa [Array.getD_eq_getD_getElem?] using h
          simp [hcfree, hnotPivotOpt]
      | some j =>
          have hj := pivotRowOfColumn?_some_prop hp
          have hjrow : j ≠ row := by
            intro h
            subst j
            exact hcpivot hj.2.symm
          have hA : A.get row c = 0 := by
            rw [← hj.2]
            have hshape_j := hshape j hj.1
            rw [hshape_j.2.2 row hrowA, if_neg (by intro h; exact hjrow h.symm)]
          rw [hA]
          have hnotPivotOpt : ¬c = pivots[row]?.getD 0 := by
            intro h
            apply hcpivot
            simpa [Array.getD_eq_getD_getElem?] using h
          simp [hcfree, hnotPivotOpt]

private theorem foldl_range_two_special [AddCommGroup F] {free pivot : Nat}
    (hne : free ≠ pivot) (x : F) :
    ∀ start len (init : F),
      (List.range' start len).foldl
          (fun acc c => acc + if c = free then x else if c = pivot then -x else 0) init =
        init + (if start ≤ free ∧ free < start + len then x else 0) +
          (if start ≤ pivot ∧ pivot < start + len then -x else 0) := by
  intro start len init
  revert start init
  induction len with
  | zero =>
      intro start init
      have hfreeFalse : ¬(start ≤ free ∧ free < start) := by omega
      have hpivotFalse : ¬(start ≤ pivot ∧ pivot < start) := by omega
      simp [hfreeFalse, hpivotFalse]
  | succ len ih =>
      intro start init
      rw [List.range']
      simp only [List.foldl_cons]
      rw [ih (start + 1)
        (init + if start = free then x else if start = pivot then -x else 0)]
      by_cases hsf : start = free
      · subst free
        have hstartNotIn : ¬(start + 1 ≤ start ∧ start < start + 1 + len) := by omega
        have hstartIn : start ≤ start ∧ start < start + (len + 1) := by omega
        rw [if_neg hstartNotIn, if_pos hstartIn]
        simp only [↓reduceIte, add_zero]
        by_cases hpivotIn : start + 1 ≤ pivot ∧ pivot < start + 1 + len
        · have hstartPivot : start ≤ pivot ∧ pivot < start + (len + 1) := by omega
          simp [hpivotIn, hstartPivot]
        · have hstartPivotFalse : ¬(start ≤ pivot ∧ pivot < start + (len + 1)) := by omega
          simp [hpivotIn, hstartPivotFalse]
      · by_cases hsp : start = pivot
        · subst pivot
          simp [hsf]
          by_cases hfreeIn : start + 1 ≤ free ∧ free < start + 1 + len
          · have hstartFree : start ≤ free ∧ free < start + (len + 1) := by omega
            simp [hfreeIn, hstartFree]
          · have hstartFreeFalse : ¬(start ≤ free ∧ free < start + (len + 1)) := by omega
            simp [hfreeIn, hstartFreeFalse]
        · simp [hsf, hsp]
          by_cases hfreeIn : start + 1 ≤ free ∧ free < start + 1 + len
          · have hstartFree : start ≤ free ∧ free < start + (len + 1) := by omega
            simp [hfreeIn, hstartFree]
            by_cases hpivotIn : start + 1 ≤ pivot ∧ pivot < start + 1 + len
            · have hstartPivot : start ≤ pivot ∧ pivot < start + (len + 1) := by omega
              simp [hpivotIn, hstartPivot]
            · have hstartPivotFalse : ¬(start ≤ pivot ∧ pivot < start + (len + 1)) := by omega
              simp [hpivotIn, hstartPivotFalse]
          · have hstartFreeFalse : ¬(start ≤ free ∧ free < start + (len + 1)) := by omega
            simp [hfreeIn, hstartFreeFalse]
            by_cases hpivotIn : start + 1 ≤ pivot ∧ pivot < start + 1 + len
            · have hstartPivot : start ≤ pivot ∧ pivot < start + (len + 1) := by omega
              simp [hpivotIn, hstartPivot]
            · have hstartPivotFalse : ¬(start ≤ pivot ∧ pivot < start + (len + 1)) := by omega
              simp [hpivotIn, hstartPivotFalse]

private theorem dotRow_basisVectorForFreeColumn_pivot [Field F] [BEq F]
    {A : DenseMatrix F} {pivots : Array Nat} {row free : Nat}
    (hshape : PivotColumnsShaped A pivots) (hstrict : PivotColumnsStrict pivots)
    (hrow : row < pivots.size) (hfree : free < A.cols)
    (hnotFree : containsNat pivots free = false) :
    A.dotRow row (basisVectorForFreeColumn A pivots free) = 0 := by
  unfold dotRow
  rw [List.range_eq_range']
  let pivot := pivots.getD row 0
  let x := A.get row free
  have hpivot : pivot < A.cols := by
    unfold pivot
    exact (hshape row hrow).2.1
  have hfree_ne_pivot : free ≠ pivot := by
    intro h
    exact containsNat_getD_ne hnotFree hrow h.symm
  have hfold : ∀ (xs : List Nat) (acc : F),
      (∀ c, c ∈ xs → c < A.cols) →
      xs.foldl
          (fun acc col =>
            acc + A.get row col * (basisVectorForFreeColumn A pivots free).getD col 0)
          acc =
        xs.foldl
          (fun acc col => acc + if col = free then x else if col = pivot then -x else 0)
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        rfl
    | cons c xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        rw [pivotRow_basisVectorForFreeColumn_term hshape hstrict hrow hfree hnotFree
          (hxs c (by simp))]
        unfold x pivot
        exact ih _ (by
          intro d hd
          exact hxs d (by simp [hd]))
  rw [hfold]
  · rw [foldl_range_two_special (F := F) (free := free) (pivot := pivot)
      hfree_ne_pivot x 0 A.cols 0]
    have hfreeIn : 0 ≤ free ∧ free < 0 + A.cols := by omega
    have hpivotIn : 0 ≤ pivot ∧ pivot < 0 + A.cols := by omega
    simp [hfreeIn, hpivotIn, hfree, hpivot]
  · intro c hc
    have h := (List.mem_range'_1.mp hc).2
    omega

private theorem foldl_range_one_special [AddCommMonoid F] {pivot : Nat} (x : F) :
    ∀ start len (init : F),
      (List.range' start len).foldl
          (fun acc c => acc + if c = pivot then x else 0) init =
        init + if start ≤ pivot ∧ pivot < start + len then x else 0 := by
  intro start len init
  revert start init
  induction len with
  | zero =>
      intro start init
      have hpivotFalse : ¬(start ≤ pivot ∧ pivot < start) := by omega
      simp [hpivotFalse]
  | succ len ih =>
      intro start init
      rw [List.range']
      simp only [List.foldl_cons]
      rw [ih (start + 1) (init + if start = pivot then x else 0)]
      by_cases hsp : start = pivot
      · subst pivot
        simp
      · simp [hsp]
        by_cases hpivotIn : start + 1 ≤ pivot ∧ pivot < start + 1 + len
        · have hstartPivot : start ≤ pivot ∧ pivot < start + (len + 1) := by omega
          simp [hpivotIn, hstartPivot]
        · have hstartPivotFalse : ¬(start ≤ pivot ∧ pivot < start + (len + 1)) := by omega
          simp [hpivotIn, hstartPivotFalse]

private theorem dotRow_eq_getD_of_all_pivots [Field F] [BEq F]
    {A : DenseMatrix F} {pivots : Array Nat} {row : Nat} {v : Array F}
    (hshape : PivotColumnsShaped A pivots) (hstrict : PivotColumnsStrict pivots)
    (hrow : row < pivots.size)
    (hall : ∀ c, c < A.cols → containsNat pivots c = true) :
    A.dotRow row v = v.getD (pivots.getD row 0) 0 := by
  unfold dotRow
  rw [List.range_eq_range']
  let pivot := pivots.getD row 0
  let x := v.getD pivot 0
  have hrowA : row < A.rows := (hshape row hrow).1
  have hpivot : pivot < A.cols := by
    unfold pivot
    exact (hshape row hrow).2.1
  have hfold : ∀ (xs : List Nat) (acc : F),
      (∀ c, c ∈ xs → c < A.cols) →
      xs.foldl (fun acc c => acc + A.get row c * v.getD c 0) acc =
        xs.foldl (fun acc c => acc + if c = pivot then x else 0) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        rfl
    | cons c xs ih =>
        intro acc hxs
        have hc : c < A.cols := hxs c (by simp)
        rcases containsNat_eq_true_iff_exists.mp (hall c hc) with ⟨j, hj, hjc⟩
        have hshape_j := hshape j hj
        have hArow : A.get row c = if row = j then 1 else 0 := by
          rw [← hjc]
          exact hshape_j.2.2 row hrowA
        simp only [List.foldl_cons]
        by_cases hrj : row = j
        · subst j
          have hcPivot : c = pivot := by
            unfold pivot
            exact hjc.symm
          rw [hArow, if_pos rfl, hcPivot]
          simp [x]
          simpa [x] using ih (acc + x) (by
            intro d hd
            exact hxs d (by simp [hd]))
        · have hcNePivot : c ≠ pivot := by
            intro hcEq
            unfold pivot at hcEq
            have hdup : pivots.getD j 0 = pivots.getD row 0 := by
              rw [hjc, hcEq]
            exact pivotColumnsStrict_getD_ne hstrict hj hrow (by
              intro h
              exact hrj h.symm) hdup
          rw [hArow, if_neg hrj, if_neg hcNePivot]
          simp only [zero_mul, add_zero]
          simpa [x] using ih acc (by
            intro d hd
            exact hxs d (by simp [hd]))
  have hmemRange : ∀ c, c ∈ List.range' 0 A.cols → c < A.cols := by
    intro c hc
    have h := (List.mem_range'_1.mp hc).2
    omega
  rw [hfold (List.range' 0 A.cols) 0 hmemRange]
  rw [foldl_range_one_special (F := F) (pivot := pivot) x 0 A.cols 0]
  have hpivotIn : 0 ≤ pivot ∧ pivot < 0 + A.cols := by omega
  rw [if_pos hpivotIn]
  simp only [zero_add]
  unfold x pivot
  rfl

private theorem dotRow_eq_zero_of_row_zero [Semiring F]
    {A : DenseMatrix F} {row : Nat} {v : Array F}
    (hzero : ∀ col, col < A.cols → A.get row col = 0) :
    A.dotRow row v = 0 := by
  unfold dotRow
  have hfold : ∀ (xs : List Nat) (acc : F),
      (∀ col, col ∈ xs → col < A.cols) →
      xs.foldl (fun acc col => acc + A.get row col * v.getD col 0) acc = acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        rfl
    | cons col xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        rw [hzero col (hxs col (by simp))]
        simp only [zero_mul, add_zero]
        exact ih acc (by
          intro c hc
          exact hxs c (by simp [hc]))
  exact hfold (List.range A.cols) 0 (by
    intro col hcol
    exact List.mem_range.mp hcol)

private theorem basisVectorForFreeColumn_isHomogeneousSolution_rref
    [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {free : Nat}
    (hfree : free < M.cols) (hnotFree : containsNat (rref M).pivots free = false) :
    IsHomogeneousSolution (rref M).matrix
      (basisVectorForFreeColumn (rref M).matrix (rref M).pivots free) := by
  intro row hrowR
  by_cases hpivRow : row < (rref M).pivots.size
  · have hshape := rref_pivotColumnsShaped M hM
    have hstrict := rref_pivotColumnsStrict M
    have hfreeR : free < (rref M).matrix.cols := by
      simpa [rref_cols] using hfree
    exact dotRow_basisVectorForFreeColumn_pivot hshape hstrict hpivRow hfreeR hnotFree
  · have hproc := rref_processedColumnsZeroBelow M hM
    apply dotRow_eq_zero_of_row_zero
    intro col hcol
    exact hproc row col (by omega) hrowR (by
      simpa [rref_cols] using hcol)

private theorem homogeneousKernelBasis_getD_zero_size [Field F] [BEq F]
    (M : DenseMatrix F) (h : ¬ homogeneousKernelBasis M = #[]) :
    ((homogeneousKernelBasis M)[0]?.getD #[]).size = M.cols := by
  let R := rref M
  have hcols : R.matrix.cols = M.cols := by
    simpa [R] using rref_cols M
  change ((Array.map (basisVectorForFreeColumn R.matrix R.pivots)
      (freeColumns M.cols R.pivots))[0]?.getD #[]).size = M.cols
  change ¬ Array.map (basisVectorForFreeColumn R.matrix R.pivots)
      (freeColumns M.cols R.pivots) = #[] at h
  generalize hfree : freeColumns M.cols R.pivots = frees
  rcases frees with ⟨xs⟩
  cases xs with
  | nil =>
      exfalso
      exact h (by simp [hfree])
  | cons _free _xs =>
      simp [basisVectorForFreeColumn_size, hcols]

private theorem homogeneousKernelBasis_getD_zero_nonzero [Field F] [BEq F]
    (M : DenseMatrix F) (h : ¬ homogeneousKernelBasis M = #[]) :
    NonzeroVector ((homogeneousKernelBasis M)[0]?.getD #[]) := by
  let R := rref M
  have hcols : R.matrix.cols = M.cols := by
    simpa [R] using rref_cols M
  change NonzeroVector
    ((Array.map (basisVectorForFreeColumn R.matrix R.pivots)
      (freeColumns M.cols R.pivots))[0]?.getD #[])
  change ¬ Array.map (basisVectorForFreeColumn R.matrix R.pivots)
      (freeColumns M.cols R.pivots) = #[] at h
  generalize hfree : freeColumns M.cols R.pivots = frees
  rcases frees with ⟨xs⟩
  cases xs with
  | nil =>
      exfalso
      exact h (by simp [hfree])
  | cons free _xs =>
      have hmem : free ∈ (freeColumns M.cols R.pivots).toList := by
        simp [hfree]
      have hlt : free < M.cols := by
        unfold freeColumns at hmem
        simp at hmem
        exact hmem.1
      have hltR : free < R.matrix.cols := by omega
      refine ⟨free, ?_, ?_⟩
      · simp [basisVectorForFreeColumn, hltR]
      · simp [basisVectorForFreeColumn, hltR]

/-- Any homogeneous witness returned by the executable kernel search has matrix-column width. -/
theorem homogeneousWitness_width [Field F] [BEq F]
    {M : DenseMatrix F} {v : Array F} (h : homogeneousWitness M = some v) :
    VectorWidth M v := by
  rw [homogeneousWitness] at h
  simp at h
  unfold VectorWidth
  rw [← h.2]
  exact homogeneousKernelBasis_getD_zero_size M h.1

/-- Any homogeneous witness returned by the executable kernel search is nonzero. -/
theorem homogeneousWitness_nonzero [Field F] [BEq F]
    {M : DenseMatrix F} {v : Array F} (h : homogeneousWitness M = some v) :
    NonzeroVector v := by
  rw [homogeneousWitness] at h
  simp at h
  rw [← h.2]
  exact homogeneousKernelBasis_getD_zero_nonzero M h.1

/-- Soundness of the homogeneous witness returned by Gaussian elimination. -/
theorem homogeneousWitness_sound [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (h : homogeneousWitness M = some v) :
    VectorWidth M v /\ IsHomogeneousSolution M v /\ NonzeroVector v := by
  refine ⟨homogeneousWitness_width h, ?_, homogeneousWitness_nonzero h⟩
  unfold homogeneousWitness at h
  by_cases hb : (homogeneousKernelBasis M).size = 0
  · simp [hb] at h
  · simp [hb] at h
    subst v
    let R := rref M
    let frees := freeColumns M.cols R.pivots
    have hfrees_pos : 0 < frees.size := by
      have hbpos : 0 < (homogeneousKernelBasis M).size := Nat.pos_of_ne_zero hb
      simpa [homogeneousKernelBasis, R, frees] using hbpos
    let free := frees.getD 0 0
    have hfree_mem : free ∈ frees := by
      unfold free
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfrees_pos]
      exact Array.getElem_mem (xs := frees) hfrees_pos
    have hfree_lt : free < M.cols := by
      exact freeColumns_mem_lt hfree_mem
    have hnot : containsNat R.pivots free = false := by
      exact freeColumns_mem_not_contains hfree_mem
    apply isHomogeneousSolution_of_rref hM
    change IsHomogeneousSolution R.matrix
      (((Array.map (basisVectorForFreeColumn R.matrix R.pivots) frees)[0]?).getD #[])
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hfrees_pos]
    change IsHomogeneousSolution R.matrix
      (basisVectorForFreeColumn R.matrix R.pivots frees[0])
    have hfree_eq : frees[0] = free := by
      unfold free
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfrees_pos]
    rw [hfree_eq]
    exact basisVectorForFreeColumn_isHomogeneousSolution_rref hM hfree_lt (by simpa [R] using hnot)

/-- If no homogeneous witness is returned, the homogeneous kernel is trivial. -/
theorem homogeneousWitness_none_complete [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) (h : homogeneousWitness M = none) :
    forall v, VectorWidth M v -> IsHomogeneousSolution M v -> Not (NonzeroVector v) := by
  intro v hvw hsol hnz
  have hbasis : (homogeneousKernelBasis M).size = 0 := (homogeneousWitness_eq_none_iff M).mp h
  have hfree : (freeColumns M.cols (rref M).pivots).size = 0 := by
    simpa [homogeneousKernelBasis] using hbasis
  have hallM : ∀ c, c < M.cols → containsNat (rref M).pivots c = true :=
    all_columns_pivot_of_no_free_columns hfree
  rcases hnz with ⟨i, hi, hne⟩
  have hiM : i < M.cols := by
    rw [← hvw]
    exact hi
  rcases containsNat_eq_true_iff_exists.mp (hallM i hiM) with ⟨row, hrow, hpiv⟩
  have hshape := rref_pivotColumnsShaped M hM
  have hstrict := rref_pivotColumnsStrict M
  have hrowR : row < (rref M).matrix.rows := (hshape row hrow).1
  have hallR : ∀ c, c < (rref M).matrix.cols → containsNat (rref M).pivots c = true := by
    intro c hc
    exact hallM c (by simpa [rref_cols] using hc)
  have hdot := dotRow_eq_getD_of_all_pivots
    (A := (rref M).matrix) (pivots := (rref M).pivots) (row := row) (v := v)
    hshape hstrict hrow hallR
  have hsolR := isHomogeneousSolution_rref hM hsol
  have hzero := hsolR row hrowR
  rw [hdot] at hzero
  rw [hpiv] at hzero
  exact hne hzero

end DenseMatrix

end CompPoly
