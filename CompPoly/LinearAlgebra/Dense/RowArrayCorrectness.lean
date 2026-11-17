/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

module

public import CompPoly.LinearAlgebra.Dense.RowArray
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Row-Array Homogeneous-Kernel Correctness

Soundness and completeness of the row-array RREF kernel
`homogeneousKernelBasisRows`: every emitted vector is orthogonal to the input
rows, and every orthogonal vector is an `F`-linear combination of the emitted
basis, with coefficients read off at the free columns.
-/

@[expose] public section

namespace CompPoly

namespace DenseMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Row-array kernel soundness

Soundness of the row-array RREF kernel:
every vector produced by `homogeneousKernelBasisRows rows cols` has size
`cols` and is orthogonal (over the first `cols` coordinates) to every input
row. -/

/-! ## Generic array access lemmas -/

section ArrayAccess

variable {α : Type*}

/-- `getD` at an out-of-bounds index returns the default. -/
theorem array_getD_of_le' (xs : Array α) (d : α) {i : Nat}
    (h : xs.size ≤ i) : xs.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-- `getD` at an in-bounds index returns the indexed element. -/
theorem array_getD_of_lt' (xs : Array α) (d : α) {i : Nat}
    (h : i < xs.size) : xs.getD i d = xs[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- `getD` after `setIfInBounds` in coordinates. -/
theorem array_getD_setIfInBounds (xs : Array α) (j : Nat) (a : α)
    (i : Nat) (d : α) :
    (xs.setIfInBounds j a).getD i d =
      if j = i ∧ j < xs.size then a else xs.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hji : j = i
  · subst hji
    by_cases hj : j < xs.size
    · simp [hj]
    · simp [hj, Array.getD_eq_getD_getElem?]
  · simp [hji, Array.getD_eq_getD_getElem?]

private theorem array_getD_push (xs : Array α) (a : α) (i : Nat) (d : α) :
    (xs.push a).getD i d =
      if i = xs.size then a else xs.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases hi : i = xs.size
  · simp [hi]
  · simp [hi, Array.getD_eq_getD_getElem?]

end ArrayAccess

/-! ## Coordinate access helpers -/

section Coordinates

variable {F : Type*}

private theorem array_getD_eq_zero_of_le [Zero F] {r : Array F} {k : Nat}
    (h : r.size ≤ k) : r.getD k 0 = 0 :=
  array_getD_of_le' r 0 h

private theorem array_getD_eq_getElem [Zero F] {r : Array F} {k : Nat}
    (h : k < r.size) : r.getD k 0 = r[k] :=
  array_getD_of_lt' r 0 h

/-- Coordinatewise description of `addScaledScalarRow`. -/
theorem addScaledScalarRow_getD [Field F] (target source : Array F)
    (factor : F) (k : Nat) :
    (addScaledScalarRow target source factor).getD k 0 =
      target.getD k 0 + factor * source.getD k 0 := by
  unfold addScaledScalarRow
  by_cases hk : k < max target.size source.size
  · rw [array_getD_eq_getElem (by simpa using hk)]
    simp [List.getElem_toArray]
  · rw [array_getD_eq_zero_of_le (by simpa using Nat.le_of_not_lt hk)]
    have htarget : target.getD k 0 = 0 :=
      array_getD_eq_zero_of_le (by omega)
    have hsource : source.getD k 0 = 0 :=
      array_getD_eq_zero_of_le (by omega)
    rw [htarget, hsource, mul_zero, add_zero]

/-- Coordinatewise description of `normalizeScalarRow` at a nonzero pivot. -/
theorem normalizeScalarRow_getD [Field F] [BEq F] [LawfulBEq F]
    (row : Array F) (pivotCol : Nat) (hpivot : row.getD pivotCol 0 ≠ 0)
    (k : Nat) :
    (normalizeScalarRow row pivotCol).getD k 0 =
      row.getD k 0 / row.getD pivotCol 0 := by
  unfold normalizeScalarRow
  rw [ite_eq_right (by simpa using hpivot)]
  by_cases hk : k < row.size
  · rw [array_getD_eq_getElem (by simpa using hk), array_getD_eq_getElem hk]
    simp
  · rw [array_getD_eq_zero_of_le (by simpa using Nat.le_of_not_lt hk),
      array_getD_eq_zero_of_le (Nat.le_of_not_lt hk), zero_div]

end Coordinates

/-! ## Scalar dot products and orthogonality -/

section Dot

variable {F : Type*}

/-- Dot product of the first `cols` coordinates of two scalar rows, with
zero defaults beyond the stored lengths. -/
def scalarDot [Field F] (cols : Nat) (r v : Array F) : F :=
  ∑ k ∈ Finset.range cols, r.getD k 0 * v.getD k 0

/-- The empty row is orthogonal to everything. -/
theorem scalarDot_empty [Field F] (cols : Nat) (v : Array F) :
    scalarDot cols (#[] : Array F) v = 0 := by
  unfold scalarDot
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [array_getD_eq_zero_of_le (by simp), zero_mul]

/-- `scalarDot` is additive along `addScaledScalarRow`. -/
theorem scalarDot_addScaledScalarRow [Field F] (cols : Nat)
    (target source v : Array F) (factor : F) :
    scalarDot cols (addScaledScalarRow target source factor) v =
      scalarDot cols target v + factor * scalarDot cols source v := by
  unfold scalarDot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [addScaledScalarRow_getD]
  ring

/-- A row recovers from its normalization by rescaling with the pivot. -/
theorem scalarDot_eq_pivot_mul_normalize [Field F] [BEq F] [LawfulBEq F]
    (cols : Nat) (row v : Array F) (pivotCol : Nat)
    (hpivot : row.getD pivotCol 0 ≠ 0) :
    scalarDot cols row v =
      row.getD pivotCol 0 * scalarDot cols (normalizeScalarRow row pivotCol) v := by
  unfold scalarDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [normalizeScalarRow_getD row pivotCol hpivot]
  field_simp

/-- Orthogonality of `v` to every row of a row-array matrix, expressed via
total `getD` access so that out-of-range indices are harmless. -/
def OrthRows [Field F] (cols : Nat) (rows : Array (Array F)) (v : Array F) :
    Prop :=
  ∀ i, scalarDot cols (rows.getD i #[]) v = 0

end Dot

/-! ## Elementary-step characterizations -/

section Steps

variable {F : Type*}

/-- Swapping rows preserves the row count. -/
theorem swapScalarRows_size (rows : Array (Array F)) (a b : Nat) :
    (swapScalarRows rows a b).size = rows.size := by
  simp [swapScalarRows, Array.size_setIfInBounds]

/-- Rows of `swapScalarRows rows a b`: rows `a` and `b` are exchanged. -/
theorem swapScalarRows_getD (rows : Array (Array F)) {a b : Nat}
    (ha : a < rows.size) (hb : b < rows.size) (i : Nat) :
    (swapScalarRows rows a b).getD i #[] =
      if i = b then rows.getD a #[]
      else if i = a then rows.getD b #[]
      else rows.getD i #[] := by
  unfold swapScalarRows
  rw [array_getD_setIfInBounds, Array.size_setIfInBounds,
    array_getD_setIfInBounds]
  by_cases hib : i = b
  · subst hib
    simp [hb]
  · by_cases hia : i = a
    · subst hia
      have hba : ¬b = i := fun h ↦ hib h.symm
      simp [hba, hib, ha]
    · have hba : ¬b = i := fun h ↦ hib h.symm
      have haa : ¬a = i := fun h ↦ hia h.symm
      simp [hba, haa, hib, hia]

private theorem findScalarPivotRow_eq_some [Field F] [BEq F] [LawfulBEq F]
    {rows : Array (Array F)} {startRow col p : Nat}
    (h : findScalarPivotRow rows startRow col = some p) :
    startRow ≤ p ∧ p < rows.size ∧ (rows.getD p #[]).getD col 0 ≠ 0 := by
  unfold findScalarPivotRow at h
  have hmem := List.mem_of_find?_eq_some h
  have hbounds := List.mem_range'_1.mp hmem
  have hpred := List.find?_some h
  refine ⟨hbounds.1, by omega, ?_⟩
  exact bne_iff_ne.mp hpred

private theorem findScalarPivotRow_eq_none [Field F] [BEq F] [LawfulBEq F]
    {rows : Array (Array F)} {startRow col : Nat}
    (h : findScalarPivotRow rows startRow col = none) :
    ∀ i, startRow ≤ i → (rows.getD i #[]).getD col 0 = 0 := by
  intro i hi
  by_cases hsize : i < rows.size
  · have hmem : i ∈ List.range' startRow (rows.size - startRow) :=
      List.mem_range'_1.mpr ⟨hi, by omega⟩
    have hfail := List.find?_eq_none.mp h i hmem
    simpa using hfail
  · rw [array_getD_of_le' rows #[] (Nat.le_of_not_lt hsize)]
    exact array_getD_of_le' _ _ (by simp)

end Steps

/-! ## Backward span: row operations are invertible -/

section Backward

variable {F : Type*}

/-- The elimination step performed for each row inside
`normalizeAndEliminateScalarRows`, lifted to a top-level definition so that
fold lemmas can be stated about it. -/
private def elimStep [Field F] [BEq F] (pivotRow : Nat)
    (pivotVector : Array F) (pivotCol : Nat) (rows : Array (Array F))
    (row : Nat) : Array (Array F) :=
  if row == pivotRow then
    rows
  else if -((rows.getD row #[]).getD pivotCol 0) == 0 then
    rows
  else
    rows.setIfInBounds row
      (addScaledScalarRow (rows.getD row #[]) pivotVector
        (-((rows.getD row #[]).getD pivotCol 0)))

private theorem normalizeAndEliminateScalarRows_eq_foldl [Field F] [BEq F]
    [LawfulBEq F] (rows : Array (Array F)) (pivotRow pivotCol : Nat)
    (h : (rows.getD pivotRow #[]).getD pivotCol 0 ≠ 0) :
    normalizeAndEliminateScalarRows rows pivotRow pivotCol =
      (List.range
          (rows.setIfInBounds pivotRow
            (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)).size).foldl
        (elimStep pivotRow
          (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol) pivotCol)
        (rows.setIfInBounds pivotRow
          (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)) := by
  unfold normalizeAndEliminateScalarRows elimStep
  rw [ite_eq_right (by simpa using h)]

private theorem elimStep_size [Field F] [BEq F] (pivotRow : Nat)
    (pivotVector : Array F) (pivotCol : Nat) (rows : Array (Array F))
    (row : Nat) :
    (elimStep pivotRow pivotVector pivotCol rows row).size = rows.size := by
  unfold elimStep
  by_cases hrp : (row == pivotRow) = true
  · rw [ite_eq_left hrp]
  · rw [ite_eq_right hrp]
    by_cases hfac : (-((rows.getD row #[]).getD pivotCol 0) == 0) = true
    · rw [ite_eq_left hfac]
    · rw [ite_eq_right hfac]
      exact Array.size_setIfInBounds

private theorem foldl_elimStep_size [Field F] [BEq F] (pivotRow : Nat)
    (pivotVector : Array F) (pivotCol : Nat) :
    ∀ (l : List Nat) (acc : Array (Array F)),
      (l.foldl (elimStep pivotRow pivotVector pivotCol) acc).size = acc.size := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih, elimStep_size]

/-- Normalizing and eliminating preserves the row count. -/
theorem normalizeAndEliminateScalarRows_size [Field F] [BEq F] [LawfulBEq F]
    (rows : Array (Array F)) (pivotRow pivotCol : Nat) :
    (normalizeAndEliminateScalarRows rows pivotRow pivotCol).size = rows.size := by
  by_cases h : (rows.getD pivotRow #[]).getD pivotCol 0 = 0
  · unfold normalizeAndEliminateScalarRows
    rw [ite_eq_left (beq_iff_eq.mpr h)]
  · rw [normalizeAndEliminateScalarRows_eq_foldl rows pivotRow pivotCol h,
      foldl_elimStep_size, Array.size_setIfInBounds]

private theorem elimStep_getD_pivotRow [Field F] [BEq F] (pivotRow : Nat)
    (pivotVector : Array F) (pivotCol : Nat) (rows : Array (Array F))
    (row : Nat) :
    (elimStep pivotRow pivotVector pivotCol rows row).getD pivotRow #[] =
      rows.getD pivotRow #[] := by
  unfold elimStep
  by_cases hrp : (row == pivotRow) = true
  · rw [ite_eq_left hrp]
  · rw [ite_eq_right hrp]
    by_cases hfac : (-((rows.getD row #[]).getD pivotCol 0) == 0) = true
    · rw [ite_eq_left hfac]
    · rw [ite_eq_right hfac]
      have hne : ¬(row = pivotRow ∧ row < rows.size) := by
        intro hc
        exact hrp (beq_iff_eq.mpr hc.1)
      rw [array_getD_setIfInBounds, ite_eq_right hne]

private theorem foldl_elimStep_getD_pivotRow [Field F] [BEq F]
    (pivotRow : Nat) (pivotVector : Array F) (pivotCol : Nat) :
    ∀ (l : List Nat) (acc : Array (Array F)),
      ((l.foldl (elimStep pivotRow pivotVector pivotCol) acc).getD
          pivotRow #[]) = acc.getD pivotRow #[] := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih, elimStep_getD_pivotRow]

private theorem orthRows_of_elimStep [Field F] [BEq F] [LawfulBEq F]
    {cols pivotRow pivotCol : Nat} {pivotVector v : Array F}
    {rows : Array (Array F)} {a : Nat}
    (hpv : scalarDot cols pivotVector v = 0)
    (h : OrthRows cols (elimStep pivotRow pivotVector pivotCol rows a) v) :
    OrthRows cols rows v := by
  unfold elimStep at h
  by_cases hap : (a == pivotRow) = true
  · rwa [ite_eq_left hap] at h
  · rw [ite_eq_right hap] at h
    by_cases hfac : (-((rows.getD a #[]).getD pivotCol 0) == 0) = true
    · rwa [ite_eq_left hfac] at h
    · rw [ite_eq_right hfac] at h
      intro i
      by_cases hia : i = a
      · subst hia
        have hi := h i
        rw [array_getD_setIfInBounds] at hi
        by_cases hsize : i < rows.size
        · rw [ite_eq_left ⟨rfl, hsize⟩, scalarDot_addScaledScalarRow, hpv,
            mul_zero, add_zero] at hi
          exact hi
        · have hne : ¬(i = i ∧ i < rows.size) := fun hc ↦ hsize hc.2
          rwa [ite_eq_right hne] at hi
      · have hi := h i
        have hne : ¬(a = i ∧ a < rows.size) := fun hc ↦ hia hc.1.symm
        rwa [array_getD_setIfInBounds, ite_eq_right hne] at hi

private theorem orthRows_of_foldl_elimStep [Field F] [BEq F] [LawfulBEq F]
    {cols pivotRow pivotCol : Nat} {pivotVector v : Array F}
    (hpv : scalarDot cols pivotVector v = 0) :
    ∀ (l : List Nat) (acc : Array (Array F)),
      OrthRows cols (l.foldl (elimStep pivotRow pivotVector pivotCol) acc) v →
        OrthRows cols acc v := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons a l ih =>
      intro acc h
      rw [List.foldl_cons] at h
      exact orthRows_of_elimStep hpv (ih _ h)

private theorem orthRows_of_normalizeAndEliminate [Field F] [BEq F]
    [LawfulBEq F] {cols : Nat} {rows : Array (Array F)}
    {pivotRow pivotCol : Nat} {v : Array F} (hpr : pivotRow < rows.size)
    (h : OrthRows cols (normalizeAndEliminateScalarRows rows pivotRow pivotCol)
      v) :
    OrthRows cols rows v := by
  by_cases hpivot : (rows.getD pivotRow #[]).getD pivotCol 0 = 0
  · unfold normalizeAndEliminateScalarRows at h
    rwa [ite_eq_left (by simpa using hpivot)] at h
  · rw [normalizeAndEliminateScalarRows_eq_foldl rows pivotRow pivotCol hpivot]
      at h
    have hpv_entry :
        (rows.setIfInBounds pivotRow
            (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)).getD
          pivotRow #[] =
          normalizeScalarRow (rows.getD pivotRow #[]) pivotCol := by
      rw [array_getD_setIfInBounds, ite_eq_left ⟨rfl, hpr⟩]
    have hpv : scalarDot cols
        (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol) v = 0 := by
      have hp := h pivotRow
      rwa [foldl_elimStep_getD_pivotRow, hpv_entry] at hp
    have h₁ := orthRows_of_foldl_elimStep hpv _ _ h
    intro i
    by_cases hip : i = pivotRow
    · subst hip
      rw [scalarDot_eq_pivot_mul_normalize cols _ v pivotCol hpivot, hpv,
        mul_zero]
    · have hi := h₁ i
      have hne : ¬(pivotRow = i ∧ pivotRow < rows.size) :=
        fun hc ↦ hip hc.1.symm
      rwa [array_getD_setIfInBounds, ite_eq_right hne] at hi

private theorem orthRows_of_scalarRrefRowsLoop [Field F] [BEq F] [LawfulBEq F]
    {cols : Nat} {v : Array F} :
    ∀ (fuel col row : Nat) (rows : Array (Array F)) (pivots : Array Nat),
      OrthRows cols
          (scalarRrefRowsLoop cols fuel col row rows pivots).rows v →
        OrthRows cols rows v := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row rows pivots h
      exact h
  | succ fuel ih =>
      intro col row rows pivots h
      simp only [scalarRrefRowsLoop] at h
      split at h
      · exact h
      · rename_i hguard
        have hrow : row < rows.size := by
          simp only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq,
            not_or, not_le] at hguard
          exact hguard.2
        cases hfind : findScalarPivotRow rows row col with
        | none =>
            rw [hfind] at h
            exact ih _ _ _ _ h
        | some p =>
            rw [hfind] at h
            obtain ⟨hp_le, hp_lt, _⟩ := findScalarPivotRow_eq_some hfind
            have hreduced := ih _ _ _ _ h
            have hswapped : OrthRows cols (swapScalarRows rows p row) v :=
              orthRows_of_normalizeAndEliminate
                (by rwa [swapScalarRows_size]) hreduced
            intro i
            by_cases hib : i = row
            · subst hib
              have hs := hswapped p
              rw [swapScalarRows_getD rows hp_lt hrow] at hs
              by_cases hpr : p = i
              · rwa [ite_eq_left hpr, hpr] at hs
              · rwa [ite_eq_right hpr, ite_eq_left rfl] at hs
            · by_cases hia : i = p
              · subst hia
                have hs := hswapped row
                rwa [swapScalarRows_getD rows hp_lt hrow, ite_eq_left rfl] at hs
              · have hs := hswapped i
                rwa [swapScalarRows_getD rows hp_lt hrow, ite_eq_right hib,
                  ite_eq_right hia] at hs

/-- Orthogonality to all rows of the final RREF matrix transfers back to all
rows of the original matrix: every row operation is invertible. -/
theorem orthRows_of_scalarRrefRows [Field F] [BEq F] [LawfulBEq F]
    {cols : Nat} {rows : Array (Array F)} {v : Array F}
    (h : OrthRows cols (scalarRrefRows rows cols).rows v) :
    OrthRows cols rows v :=
  orthRows_of_scalarRrefRowsLoop _ _ _ _ _ h

end Backward

/-! ## Forward RREF shape invariants -/

section Forward

variable {F : Type*}

private theorem elimStep_getD_other [Field F] [BEq F] {pivotRow : Nat}
    {pivotVector : Array F} {pivotCol : Nat} {rows : Array (Array F)}
    {a i : Nat} (hia : i ≠ a) :
    (elimStep pivotRow pivotVector pivotCol rows a).getD i #[] =
      rows.getD i #[] := by
  unfold elimStep
  by_cases hap : (a == pivotRow) = true
  · rw [ite_eq_left hap]
  · rw [ite_eq_right hap]
    by_cases hfac : (-((rows.getD a #[]).getD pivotCol 0) == 0) = true
    · rw [ite_eq_left hfac]
    · rw [ite_eq_right hfac]
      have hne : ¬(a = i ∧ a < rows.size) := fun hc ↦ hia hc.1.symm
      rw [array_getD_setIfInBounds, ite_eq_right hne]

private theorem elimStep_getD_self_entry [Field F] [BEq F] [LawfulBEq F]
    (pivotRow : Nat) (pivotVector : Array F) (pivotCol : Nat)
    (rows : Array (Array F)) (a k : Nat) :
    ((elimStep pivotRow pivotVector pivotCol rows a).getD a #[]).getD k 0 =
      if a = pivotRow then
        (rows.getD a #[]).getD k 0
      else
        (rows.getD a #[]).getD k 0 -
          (rows.getD a #[]).getD pivotCol 0 * pivotVector.getD k 0 := by
  unfold elimStep
  by_cases hap : (a == pivotRow) = true
  · rw [ite_eq_left hap, ite_eq_left (beq_iff_eq.mp hap)]
  · have hap' : ¬a = pivotRow := by simpa using hap
    rw [ite_eq_right hap, ite_eq_right hap']
    by_cases hfac : (-((rows.getD a #[]).getD pivotCol 0) == 0) = true
    · have hzero : (rows.getD a #[]).getD pivotCol 0 = 0 :=
        neg_eq_zero.mp (beq_iff_eq.mp hfac)
      rw [ite_eq_left hfac, hzero, zero_mul, sub_zero]
    · rw [ite_eq_right hfac]
      by_cases hsize : a < rows.size
      · rw [array_getD_setIfInBounds, ite_eq_left ⟨rfl, hsize⟩,
          addScaledScalarRow_getD, neg_mul, ← sub_eq_add_neg]
      · have hne : ¬(a = a ∧ a < rows.size) := fun hc ↦ hsize hc.2
        rw [array_getD_setIfInBounds, ite_eq_right hne,
          array_getD_of_le' rows #[] (Nat.le_of_not_lt hsize)]
        have h0 : ∀ j, (#[] : Array F).getD j 0 = 0 :=
          fun j ↦ array_getD_of_le' _ _ (by simp)
        rw [h0, h0, zero_mul, sub_zero]

private theorem foldl_elimStep_getD_entry [Field F] [BEq F] [LawfulBEq F]
    (pivotRow : Nat) (pivotVector : Array F) (pivotCol : Nat) :
    ∀ (l : List Nat), l.Nodup →
      ∀ (acc : Array (Array F)) (i k : Nat),
        (((l.foldl (elimStep pivotRow pivotVector pivotCol) acc).getD
            i #[]).getD k 0) =
          if i ∈ l ∧ i ≠ pivotRow then
            (acc.getD i #[]).getD k 0 -
              (acc.getD i #[]).getD pivotCol 0 * pivotVector.getD k 0
          else
            (acc.getD i #[]).getD k 0 := by
  intro l
  induction l with
  | nil =>
      intro _ acc i k
      have hne : ¬(i ∈ ([] : List Nat) ∧ i ≠ pivotRow) := by simp
      rw [List.foldl_nil, ite_eq_right hne]
  | cons a l ih =>
      intro hnodup acc i k
      obtain ⟨ha_notin, hl⟩ := List.nodup_cons.mp hnodup
      rw [List.foldl_cons, ih hl]
      by_cases hia : i = a
      · subst hia
        have hnot : ¬(i ∈ l ∧ i ≠ pivotRow) := fun hc ↦ ha_notin hc.1
        rw [ite_eq_right hnot, elimStep_getD_self_entry]
        by_cases hip : i = pivotRow
        · have hnot2 : ¬(i ∈ i :: l ∧ i ≠ pivotRow) := fun hc ↦ hc.2 hip
          rw [ite_eq_left hip, ite_eq_right hnot2]
        · rw [ite_eq_right hip, ite_eq_left ⟨by simp, hip⟩]
      · rw [elimStep_getD_other hia]
        by_cases hil : i ∈ l ∧ i ≠ pivotRow
        · rw [ite_eq_left hil, ite_eq_left ⟨List.mem_cons_of_mem a hil.1, hil.2⟩]
        · have hnot : ¬(i ∈ a :: l ∧ i ≠ pivotRow) := by
            intro hc
            rcases List.mem_cons.mp hc.1 with h | h
            · exact hia h
            · exact hil ⟨h, hc.2⟩
          rw [ite_eq_right hil, ite_eq_right hnot]

/-- Entries of `normalizeAndEliminateScalarRows`: the pivot row is divided by
the pivot, and every other row loses its pivot-column multiple of the normalized
pivot row. -/
theorem normalizeAndEliminateScalarRows_getD_entry [Field F] [BEq F]
    [LawfulBEq F] (rows : Array (Array F)) (pivotRow pivotCol : Nat)
    (hpr : pivotRow < rows.size)
    (hpivot : (rows.getD pivotRow #[]).getD pivotCol 0 ≠ 0) (i k : Nat) :
    ((normalizeAndEliminateScalarRows rows pivotRow pivotCol).getD
        i #[]).getD k 0 =
      if i = pivotRow then
        (rows.getD pivotRow #[]).getD k 0 /
          (rows.getD pivotRow #[]).getD pivotCol 0
      else
        (rows.getD i #[]).getD k 0 -
          (rows.getD i #[]).getD pivotCol 0 *
            ((rows.getD pivotRow #[]).getD k 0 /
              (rows.getD pivotRow #[]).getD pivotCol 0) := by
  rw [normalizeAndEliminateScalarRows_eq_foldl rows pivotRow pivotCol hpivot,
    foldl_elimStep_getD_entry pivotRow _ pivotCol _ List.nodup_range]
  have hrows₁_pr :
      (rows.setIfInBounds pivotRow
          (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)).getD
        pivotRow #[] =
        normalizeScalarRow (rows.getD pivotRow #[]) pivotCol := by
    rw [array_getD_setIfInBounds, ite_eq_left ⟨rfl, hpr⟩]
  have hpv_getD := normalizeScalarRow_getD (rows.getD pivotRow #[]) pivotCol
    hpivot
  by_cases hip : i = pivotRow
  · subst hip
    have hnot : ¬(i ∈ List.range
        (rows.setIfInBounds i
          (normalizeScalarRow (rows.getD i #[]) pivotCol)).size ∧ i ≠ i) :=
      fun hc ↦ hc.2 rfl
    rw [ite_eq_right hnot, ite_eq_left rfl, hrows₁_pr, hpv_getD]
  · rw [ite_eq_right hip]
    have hrows₁_i :
        (rows.setIfInBounds pivotRow
            (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)).getD
          i #[] = rows.getD i #[] := by
      have hne : ¬(pivotRow = i ∧ pivotRow < rows.size) :=
        fun hc ↦ hip hc.1.symm
      rw [array_getD_setIfInBounds, ite_eq_right hne]
    by_cases hisize : i < rows.size
    · have hmem : i ∈ List.range
          (rows.setIfInBounds pivotRow
            (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)).size := by
        rw [List.mem_range, Array.size_setIfInBounds]
        exact hisize
      rw [ite_eq_left ⟨hmem, hip⟩, hrows₁_i, hpv_getD]
    · have hnot : ¬(i ∈ List.range
          (rows.setIfInBounds pivotRow
            (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol)).size ∧
          i ≠ pivotRow) := by
        intro hc
        have := List.mem_range.mp hc.1
        rw [Array.size_setIfInBounds] at this
        exact hisize this
      rw [ite_eq_right hnot, hrows₁_i,
        array_getD_of_le' rows #[] (Nat.le_of_not_lt hisize)]
      have h0 : ∀ j, (#[] : Array F).getD j 0 = 0 :=
        fun j ↦ array_getD_of_le' _ _ (by simp)
      rw [h0, h0, zero_mul, sub_zero]

/-- Shape contract satisfied by the result of `scalarRrefRows`: recorded
pivot columns are strictly increasing and below `cols`, each pivot column is
a unit column with its one in the corresponding pivot row, and every row at
or beyond the pivot count vanishes on all columns below `cols`. -/
structure ScalarRrefSpec [Field F] (cols : Nat)
    (R : ScalarRrefResult (F := F)) : Prop where
  mono : ∀ s t, s < t → t < R.pivots.size →
    R.pivots.getD s 0 < R.pivots.getD t 0
  pivots_lt : ∀ t, t < R.pivots.size → R.pivots.getD t 0 < cols
  unit : ∀ t, t < R.pivots.size → ∀ i,
    (R.rows.getD i #[]).getD (R.pivots.getD t 0) 0 = if i = t then 1 else 0
  tail_zero : ∀ i, R.pivots.size ≤ i → ∀ k, k < cols →
    (R.rows.getD i #[]).getD k 0 = 0

private theorem scalarRrefRowsLoop_spec [Field F] [BEq F] [LawfulBEq F]
    {cols : Nat} :
    ∀ (fuel col row : Nat) (rows : Array (Array F)) (pivots : Array Nat),
      cols < col + fuel →
      row = pivots.size →
      (∀ s t, s < t → t < pivots.size →
        pivots.getD s 0 < pivots.getD t 0) →
      (∀ t, t < pivots.size → pivots.getD t 0 < col) →
      (∀ t, t < pivots.size → pivots.getD t 0 < cols) →
      (∀ t, t < pivots.size → ∀ i,
        (rows.getD i #[]).getD (pivots.getD t 0) 0 = if i = t then 1 else 0) →
      (∀ i, row ≤ i → ∀ k, k < col → (rows.getD i #[]).getD k 0 = 0) →
      ScalarRrefSpec cols (scalarRrefRowsLoop cols fuel col row rows pivots) := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row rows pivots hfuel hrow hmono _hltcol hltcols hunit hzero
      exact ⟨hmono, hltcols, hunit, fun i hi k hk ↦
        hzero i (le_of_eq_of_le hrow hi) k (Nat.lt_trans hk hfuel)⟩
  | succ fuel ih =>
      intro col row rows pivots hfuel hrow hmono hltcol hltcols hunit hzero
      simp only [scalarRrefRowsLoop]
      split
      · rename_i hguard
        have hguard' : cols ≤ col ∨ rows.size ≤ row := by
          simpa [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq] using hguard
        refine ⟨hmono, hltcols, hunit, ?_⟩
        intro i hi k hk
        have hi' : pivots.size ≤ i := hi
        rcases hguard' with hcase | hcase
        · exact hzero i (le_of_eq_of_le hrow hi') k (by omega)
        · have hsize : rows.size ≤ i := by omega
          rw [array_getD_of_le' rows #[] hsize]
          exact array_getD_of_le' _ _ (by simp)
      · rename_i hguard
        have hguard' : col < cols ∧ row < rows.size := by
          simpa [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or,
            not_le] using hguard
        obtain ⟨hcol, hrowlt⟩ := hguard'
        cases hfind : findScalarPivotRow rows row col with
        | none =>
            apply ih (col + 1) row rows pivots (by omega) hrow hmono
              (fun t ht ↦ Nat.lt_succ_of_lt (hltcol t ht)) hltcols hunit
            intro i hi k hk
            by_cases hkcol : k < col
            · exact hzero i hi k hkcol
            · have hk_eq : k = col := by omega
              subst hk_eq
              exact findScalarPivotRow_eq_none hfind i hi
        | some p =>
            obtain ⟨hp_le, hp_lt, hp_ne⟩ := findScalarPivotRow_eq_some hfind
            show ScalarRrefSpec cols (scalarRrefRowsLoop cols fuel (col + 1)
              (row + 1)
              (normalizeAndEliminateScalarRows (swapScalarRows rows p row)
                row col)
              (pivots.push col))
            have hgetD := swapScalarRows_getD rows hp_lt hrowlt
            have hsize := swapScalarRows_size rows p row
            generalize hS : swapScalarRows rows p row = S at hgetD hsize ⊢
            have hS_zero : ∀ i, row ≤ i → ∀ k, k < col →
                (S.getD i #[]).getD k 0 = 0 := by
              intro i hi k hk
              rw [hgetD i]
              by_cases hir : i = row
              · rw [ite_eq_left hir]
                exact hzero p hp_le k hk
              · rw [ite_eq_right hir]
                by_cases hip : i = p
                · rw [ite_eq_left hip]
                  exact hzero row (le_refl row) k hk
                · rw [ite_eq_right hip]
                  exact hzero i hi k hk
            have hS_unit : ∀ t, t < pivots.size → ∀ i,
                (S.getD i #[]).getD (pivots.getD t 0) 0 =
                  if i = t then 1 else 0 := by
              intro t ht i
              rw [hgetD i]
              by_cases hir : i = row
              · rw [ite_eq_left hir, hzero p hp_le _ (hltcol t ht),
                  ite_eq_right (by omega : ¬i = t)]
              · rw [ite_eq_right hir]
                by_cases hip : i = p
                · rw [ite_eq_left hip, hzero row (le_refl row) _ (hltcol t ht)]
                  have hit : ¬i = t := by omega
                  rw [ite_eq_right hit]
                · rw [ite_eq_right hip]
                  exact hunit t ht i
            have hS_pivot : (S.getD row #[]).getD col 0 ≠ 0 := by
              rw [hgetD row, ite_eq_left rfl]
              exact hp_ne
            have hE := normalizeAndEliminateScalarRows_getD_entry S row col
              (by omega) hS_pivot
            apply ih (col + 1) (row + 1) _ (pivots.push col) (by omega)
            · rw [Array.size_push]
              omega
            · intro s t hst ht
              rw [Array.size_push] at ht
              rw [array_getD_push, array_getD_push]
              by_cases hts : t = pivots.size
              · rw [ite_eq_left hts, ite_eq_right (by omega : ¬s = pivots.size)]
                exact hltcol s (by omega)
              · rw [ite_eq_right hts, ite_eq_right (by omega : ¬s = pivots.size)]
                exact hmono s t hst (by omega)
            · intro t ht
              rw [Array.size_push] at ht
              rw [array_getD_push]
              by_cases hts : t = pivots.size
              · rw [ite_eq_left hts]
                exact Nat.lt_succ_self col
              · rw [ite_eq_right hts]
                exact Nat.lt_succ_of_lt (hltcol t (by omega))
            · intro t ht
              rw [Array.size_push] at ht
              rw [array_getD_push]
              by_cases hts : t = pivots.size
              · rw [ite_eq_left hts]
                exact hcol
              · rw [ite_eq_right hts]
                exact hltcols t (by omega)
            · intro t ht i
              rw [Array.size_push] at ht
              rw [array_getD_push]
              by_cases hts : t = pivots.size
              · rw [ite_eq_left hts, hE i col]
                by_cases hir : i = row
                · rw [ite_eq_left hir, div_self hS_pivot,
                    ite_eq_left (by omega : i = t)]
                · rw [ite_eq_right hir, div_self hS_pivot, mul_one, sub_self,
                    ite_eq_right (by omega : ¬i = t)]
              · rw [ite_eq_right hts]
                have ht' : t < pivots.size := by omega
                have hSrow_c : (S.getD row #[]).getD (pivots.getD t 0) 0 = 0 := by
                  rw [hgetD row, ite_eq_left rfl]
                  exact hzero p hp_le _ (hltcol t ht')
                rw [hE i (pivots.getD t 0)]
                by_cases hir : i = row
                · rw [ite_eq_left hir, hSrow_c, zero_div,
                    ite_eq_right (by omega : ¬i = t)]
                · rw [ite_eq_right hir, hSrow_c, zero_div, mul_zero, sub_zero]
                  exact hS_unit t ht' i
            · intro i hi k hk
              rw [hE i k, ite_eq_right (by omega : ¬i = row)]
              by_cases hkc : k < col
              · rw [hS_zero i (by omega) k hkc,
                  hS_zero row (le_refl row) k hkc, zero_div, mul_zero,
                  sub_zero]
              · have hk_eq : k = col := by omega
                subst hk_eq
                rw [div_self hS_pivot, mul_one, sub_self]

/-- The row-array RREF driver satisfies the RREF shape contract. -/
theorem scalarRrefRows_spec [Field F] [BEq F] [LawfulBEq F]
    (rows : Array (Array F)) (cols : Nat) :
    ScalarRrefSpec cols (scalarRrefRows rows cols) := by
  unfold scalarRrefRows
  apply scalarRrefRowsLoop_spec (cols + 1) 0 0 rows #[] (by omega) rfl
  · intro s t _ ht
    simp at ht
  · intro t ht
    simp at ht
  · intro t ht
    simp at ht
  · intro t ht
    simp at ht
  · intro i _ k hk
    omega

end Forward

/-! ## Kernel basis vectors -/

section Kernel

variable {F : Type*}

private theorem containsNat_false_getD_ne {xs : Array Nat} {x : Nat}
    (h : DenseMatrix.containsNat xs x = false) :
    ∀ t, t < xs.size → xs.getD t 0 ≠ x := by
  intro t ht heq
  have htrue : DenseMatrix.containsNat xs x = true := by
    unfold DenseMatrix.containsNat
    rw [Array.any_eq_true]
    refine ⟨t, ht, ?_⟩
    rw [← array_getD_of_lt' xs 0 ht, heq]
    exact beq_iff_eq.mpr rfl
  rw [h] at htrue
  exact Bool.false_ne_true htrue

/-- A free column is below `cols` and is not a recorded pivot column. -/
theorem freeColumns_mem {cols : Nat} {pivots : Array Nat} {free : Nat}
    (h : free ∈ (freeColumns cols pivots).toList) :
    free < cols ∧ ∀ t, t < pivots.size → pivots.getD t 0 ≠ free := by
  unfold freeColumns at h
  rw [List.toList_toArray, List.mem_filter] at h
  refine ⟨List.mem_range.mp h.1, ?_⟩
  have hfalse : DenseMatrix.containsNat pivots free = false := by
    simpa using h.2
  exact containsNat_false_getD_ne hfalse

/-- `pivotRowOfColumn?` returns an in-range index whose recorded pivot is the
requested column. -/
theorem pivotRowOfColumn?_some {pivots : Array Nat} {col t : Nat}
    (h : pivotRowOfColumn? pivots col = some t) :
    t < pivots.size ∧ pivots.getD t 0 = col := by
  unfold pivotRowOfColumn? at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  exact ⟨List.mem_range.mp hmem, beq_iff_eq.mp hpred⟩

private theorem pivotRowOfColumn?_eq_some_of_mono {pivots : Array Nat}
    (hmono : ∀ s t, s < t → t < pivots.size →
      pivots.getD s 0 < pivots.getD t 0)
    {t : Nat} (ht : t < pivots.size) :
    pivotRowOfColumn? pivots (pivots.getD t 0) = some t := by
  cases hfind : pivotRowOfColumn? pivots (pivots.getD t 0) with
  | none =>
      exfalso
      unfold pivotRowOfColumn? at hfind
      exact List.find?_eq_none.mp hfind t (List.mem_range.mpr ht)
        (beq_iff_eq.mpr rfl)
  | some r =>
      obtain ⟨hr, hreq⟩ := pivotRowOfColumn?_some hfind
      have hrt : r = t := by
        rcases Nat.lt_trichotomy r t with hlt | heq | hgt
        · exact absurd hreq (Nat.ne_of_lt (hmono r t hlt ht))
        · exact heq
        · exact absurd hreq.symm (Nat.ne_of_lt (hmono t r hgt hr))
      rw [hrt]

private theorem pivotRowOfColumn?_eq_none {pivots : Array Nat} {k : Nat}
    (h : ∀ t, t < pivots.size → pivots.getD t 0 ≠ k) :
    pivotRowOfColumn? pivots k = none := by
  unfold pivotRowOfColumn?
  rw [List.find?_eq_none]
  intro x hx
  simpa using h x (List.mem_range.mp hx)

/-- Each row-array kernel basis vector has `cols` entries. -/
theorem basisVectorForFreeColumnRows_size [Field F]
    (rows : Array (Array F)) (pivots : Array Nat) (cols free : Nat) :
    (basisVectorForFreeColumnRows rows pivots cols free).size = cols := by
  unfold basisVectorForFreeColumnRows
  exact Array.size_ofFn

private theorem basisVectorForFreeColumnRows_getD_free [Field F]
    (rows : Array (Array F)) (pivots : Array Nat) (cols : Nat) {free : Nat}
    (hfree : free < cols) :
    (basisVectorForFreeColumnRows rows pivots cols free).getD free 0 = 1 := by
  unfold basisVectorForFreeColumnRows
  rw [array_getD_of_lt' _ 0 (by rw [Array.size_ofFn]; exact hfree),
    Array.getElem_ofFn]
  dsimp only
  rw [ite_eq_left (beq_iff_eq.mpr rfl)]

private theorem basisVectorForFreeColumnRows_getD_none [Field F]
    (rows : Array (Array F)) (pivots : Array Nat) (cols free : Nat) {k : Nat}
    (hk : k < cols) (hkf : ¬k = free)
    (hnone : pivotRowOfColumn? pivots k = none) :
    (basisVectorForFreeColumnRows rows pivots cols free).getD k 0 = 0 := by
  unfold basisVectorForFreeColumnRows
  rw [array_getD_of_lt' _ 0 (by rw [Array.size_ofFn]; exact hk),
    Array.getElem_ofFn]
  dsimp only
  rw [ite_eq_right (by simpa using hkf)]
  simp only [hnone]

private theorem basisVectorForFreeColumnRows_getD_some [Field F]
    (rows : Array (Array F)) (pivots : Array Nat) (cols free : Nat) {k t : Nat}
    (hk : k < cols) (hkf : ¬k = free)
    (hsome : pivotRowOfColumn? pivots k = some t) :
    (basisVectorForFreeColumnRows rows pivots cols free).getD k 0 =
      -((rows.getD t #[]).getD free 0) := by
  unfold basisVectorForFreeColumnRows
  rw [array_getD_of_lt' _ 0 (by rw [Array.size_ofFn]; exact hk),
    Array.getElem_ofFn]
  dsimp only
  rw [ite_eq_right (by simpa using hkf)]
  simp only [hsome]

private theorem scalarDot_basisVector [Field F] [BEq F] [LawfulBEq F]
    {cols : Nat} {R : ScalarRrefResult (F := F)}
    (hspec : ScalarRrefSpec cols R) {free : Nat} (hfree : free < cols)
    (hfreeNot : ∀ t, t < R.pivots.size → R.pivots.getD t 0 ≠ free)
    (i : Nat) :
    scalarDot cols (R.rows.getD i #[])
      (basisVectorForFreeColumnRows R.rows R.pivots cols free) = 0 := by
  by_cases hi : i < R.pivots.size
  · have hterm : ∀ k ∈ Finset.range cols,
        (R.rows.getD i #[]).getD k 0 *
            (basisVectorForFreeColumnRows R.rows R.pivots cols
              free).getD k 0 =
          (if k = free then (R.rows.getD i #[]).getD free 0 else 0) +
            (if k = R.pivots.getD i 0 then
              -((R.rows.getD i #[]).getD free 0) else 0) := by
      intro k hk
      have hk' : k < cols := Finset.mem_range.mp hk
      by_cases hkf : k = free
      · subst hkf
        have hkp : ¬k = R.pivots.getD i 0 := fun h ↦ hfreeNot i hi h.symm
        rw [basisVectorForFreeColumnRows_getD_free R.rows R.pivots cols hk',
          ite_eq_left rfl, ite_eq_right hkp, mul_one, add_zero]
      · rw [ite_eq_right hkf, zero_add]
        by_cases hkpiv : ∃ t, t < R.pivots.size ∧ R.pivots.getD t 0 = k
        · obtain ⟨t, ht, htk⟩ := hkpiv
          have hsome : pivotRowOfColumn? R.pivots k = some t := by
            rw [← htk]
            exact pivotRowOfColumn?_eq_some_of_mono hspec.mono ht
          rw [basisVectorForFreeColumnRows_getD_some R.rows R.pivots cols
            free hk' hkf hsome]
          rw [← htk, hspec.unit t ht i]
          by_cases hit : i = t
          · subst hit
            rw [ite_eq_left rfl, ite_eq_left rfl, one_mul]
          · rw [ite_eq_right hit, zero_mul]
            have hne : ¬R.pivots.getD t 0 = R.pivots.getD i 0 := by
              intro heq
              rcases Nat.lt_trichotomy t i with hlt | heq' | hgt
              · exact absurd heq (Nat.ne_of_lt (hspec.mono t i hlt hi))
              · exact hit heq'.symm
              · exact absurd heq.symm (Nat.ne_of_lt (hspec.mono i t hgt ht))
            rw [ite_eq_right hne]
        · have hnone : pivotRowOfColumn? R.pivots k = none :=
            pivotRowOfColumn?_eq_none fun t ht heq ↦ hkpiv ⟨t, ht, heq⟩
          have hne : ¬k = R.pivots.getD i 0 := fun h ↦ hkpiv ⟨i, hi, h.symm⟩
          rw [basisVectorForFreeColumnRows_getD_none R.rows R.pivots cols
            free hk' hkf hnone, mul_zero, ite_eq_right hne]
    unfold scalarDot
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_ite_eq_of_mem' (Finset.range cols) free _
        (Finset.mem_range.mpr hfree),
      Finset.sum_ite_eq_of_mem' (Finset.range cols) (R.pivots.getD i 0) _
        (Finset.mem_range.mpr (hspec.pivots_lt i hi)),
      add_neg_cancel]
  · have hi' : R.pivots.size ≤ i := Nat.le_of_not_lt hi
    unfold scalarDot
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [hspec.tail_zero i hi' k (Finset.mem_range.mp hk), zero_mul]

end Kernel

/-! ## Main soundness theorems -/

section Main

variable {F : Type*}

/-- Every vector produced by `homogeneousKernelBasisRows rows cols` has
exactly `cols` stored coordinates. -/
theorem homogeneousKernelBasisRows_size [Field F] [BEq F] [LawfulBEq F]
    {rows : Array (Array F)} {cols : Nat} {v : Array F}
    (hv : v ∈ (homogeneousKernelBasisRows rows cols).toList) :
    v.size = cols := by
  simp only [homogeneousKernelBasisRows] at hv
  rw [Array.toList_map, List.mem_map] at hv
  obtain ⟨free, _, rfl⟩ := hv
  exact basisVectorForFreeColumnRows_size _ _ _ _

/-- **Soundness of the row-array kernel.**  Every vector produced by
`homogeneousKernelBasisRows rows cols` is orthogonal, over the coordinates
`0, …, cols - 1`, to every row of the input matrix.  No width hypothesis on
the input rows is needed because the dot product only inspects the first
`cols` coordinates (with zero defaults). -/
theorem homogeneousKernelBasisRows_dot_eq_zero [Field F] [BEq F] [LawfulBEq F]
    {rows : Array (Array F)} {cols : Nat} {v : Array F}
    (hv : v ∈ (homogeneousKernelBasisRows rows cols).toList)
    {r : Array F} (hr : r ∈ rows.toList) :
    ∑ k ∈ Finset.range cols, r.getD k 0 * v.getD k 0 = 0 := by
  simp only [homogeneousKernelBasisRows] at hv
  rw [Array.toList_map, List.mem_map] at hv
  obtain ⟨free, hfree_mem, rfl⟩ := hv
  obtain ⟨hfree_lt, hfree_not⟩ := freeColumns_mem hfree_mem
  have hspec := scalarRrefRows_spec rows cols
  have horthR : OrthRows cols (scalarRrefRows rows cols).rows
      (basisVectorForFreeColumnRows (scalarRrefRows rows cols).rows
        (scalarRrefRows rows cols).pivots cols free) :=
    fun i ↦ scalarDot_basisVector hspec hfree_lt hfree_not i
  have horth := orthRows_of_scalarRrefRows horthR
  obtain ⟨j, hj, hrj⟩ := List.mem_iff_getElem.mp hr
  have hj' : j < rows.size := by simpa using hj
  have hr_eq : rows.getD j #[] = r := by
    rw [array_getD_of_lt' rows #[] hj', ← Array.getElem_toList hj']
    exact hrj
  have hdot := horth j
  rw [hr_eq] at hdot
  exact hdot

/-! ### Forward span: row operations preserve orthogonality -/

private theorem orthRows_elimStep_forward [Field F] [BEq F]
    {cols pivotRow pivotCol : Nat} {pivotVector v : Array F}
    {rows : Array (Array F)} {a : Nat}
    (hpv : scalarDot cols pivotVector v = 0)
    (h : OrthRows cols rows v) :
    OrthRows cols (elimStep pivotRow pivotVector pivotCol rows a) v := by
  unfold elimStep
  by_cases hap : (a == pivotRow) = true
  · rw [ite_eq_left hap]
    exact h
  · rw [ite_eq_right hap]
    by_cases hfac : (-((rows.getD a #[]).getD pivotCol 0) == 0) = true
    · rw [ite_eq_left hfac]
      exact h
    · rw [ite_eq_right hfac]
      intro i
      rw [array_getD_setIfInBounds]
      by_cases hcond : a = i ∧ a < rows.size
      · rw [ite_eq_left hcond, scalarDot_addScaledScalarRow, h a, hpv, mul_zero,
          add_zero]
      · rw [ite_eq_right hcond]
        exact h i

private theorem orthRows_foldl_elimStep_forward [Field F] [BEq F]
    {cols pivotRow pivotCol : Nat} {pivotVector v : Array F}
    (hpv : scalarDot cols pivotVector v = 0) :
    ∀ (l : List Nat) (acc : Array (Array F)),
      OrthRows cols acc v →
        OrthRows cols (l.foldl (elimStep pivotRow pivotVector pivotCol) acc)
          v := by
  intro l
  induction l with
  | nil =>
      intro acc h
      exact h
  | cons a l ih =>
      intro acc h
      rw [List.foldl_cons]
      exact ih _ (orthRows_elimStep_forward hpv h)

private theorem orthRows_normalizeAndEliminate_forward [Field F] [BEq F]
    [LawfulBEq F] {cols : Nat} {rows : Array (Array F)}
    {pivotRow pivotCol : Nat} {v : Array F} (h : OrthRows cols rows v) :
    OrthRows cols (normalizeAndEliminateScalarRows rows pivotRow pivotCol)
      v := by
  by_cases hpivot : (rows.getD pivotRow #[]).getD pivotCol 0 = 0
  · unfold normalizeAndEliminateScalarRows
    rw [ite_eq_left (by simpa using hpivot)]
    exact h
  · rw [normalizeAndEliminateScalarRows_eq_foldl rows pivotRow pivotCol hpivot]
    have hpv : scalarDot cols
        (normalizeScalarRow (rows.getD pivotRow #[]) pivotCol) v = 0 := by
      have h0 := h pivotRow
      rw [scalarDot_eq_pivot_mul_normalize cols _ v pivotCol hpivot] at h0
      exact (mul_eq_zero.mp h0).resolve_left hpivot
    refine orthRows_foldl_elimStep_forward hpv _ _ ?_
    intro i
    rw [array_getD_setIfInBounds]
    by_cases hcond : pivotRow = i ∧ pivotRow < rows.size
    · rw [ite_eq_left hcond]
      exact hpv
    · rw [ite_eq_right hcond]
      exact h i

private theorem orthRows_swapScalarRows_forward [Field F] {cols : Nat}
    {rows : Array (Array F)} {a b : Nat} (ha : a < rows.size)
    (hb : b < rows.size) {v : Array F} (h : OrthRows cols rows v) :
    OrthRows cols (swapScalarRows rows a b) v := by
  intro i
  rw [swapScalarRows_getD rows ha hb]
  by_cases hib : i = b
  · rw [ite_eq_left hib]
    exact h a
  · rw [ite_eq_right hib]
    by_cases hia : i = a
    · rw [ite_eq_left hia]
      exact h b
    · rw [ite_eq_right hia]
      exact h i

private theorem orthRows_scalarRrefRowsLoop_forward [Field F] [BEq F]
    [LawfulBEq F] {cols : Nat} {v : Array F} :
    ∀ (fuel col row : Nat) (rows : Array (Array F)) (pivots : Array Nat),
      OrthRows cols rows v →
        OrthRows cols (scalarRrefRowsLoop cols fuel col row rows pivots).rows
          v := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row rows pivots h
      exact h
  | succ fuel ih =>
      intro col row rows pivots h
      simp only [scalarRrefRowsLoop]
      split
      · exact h
      · rename_i hguard
        have hrow : row < rows.size := by
          simp only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq,
            not_or, not_le] at hguard
          exact hguard.2
        cases hfind : findScalarPivotRow rows row col with
        | none => exact ih _ _ _ _ h
        | some p =>
            obtain ⟨_, hp_lt, _⟩ := findScalarPivotRow_eq_some hfind
            exact ih _ _ _ _
              (orthRows_normalizeAndEliminate_forward
                (orthRows_swapScalarRows_forward hp_lt hrow h))

private theorem orthRows_scalarRrefRows_forward [Field F] [BEq F] [LawfulBEq F]
    {cols : Nat} {rows : Array (Array F)} {v : Array F}
    (h : OrthRows cols rows v) :
    OrthRows cols (scalarRrefRows rows cols).rows v :=
  orthRows_scalarRrefRowsLoop_forward _ _ _ _ _ h

/-! ### Free-column bookkeeping for the completeness theorem -/

/-- In-range entries of `freeColumns` are members of it. -/
theorem freeColumns_getD_mem {cols : Nat} {pivots : Array Nat}
    {i : Nat} (hi : i < (freeColumns cols pivots).size) :
    (freeColumns cols pivots).getD i 0 ∈
      (freeColumns cols pivots).toList := by
  rw [array_getD_of_lt' _ 0 hi, ← Array.getElem_toList (by simpa using hi)]
  exact List.getElem_mem _

private theorem freeColumns_getD_inj {cols : Nat} {pivots : Array Nat}
    {i j : Nat} (hi : i < (freeColumns cols pivots).size)
    (hj : j < (freeColumns cols pivots).size)
    (h : (freeColumns cols pivots).getD i 0 =
      (freeColumns cols pivots).getD j 0) :
    i = j := by
  rw [array_getD_of_lt' _ 0 hi, array_getD_of_lt' _ 0 hj] at h
  unfold freeColumns at hi hj h
  rw [List.getElem_toArray, List.getElem_toArray] at h
  have hnodup : ((List.range cols).filter
      fun col ↦ !(DenseMatrix.containsNat pivots col)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  exact (List.Nodup.getElem_inj_iff hnodup).mp h

private theorem containsNat_true_exists {xs : Array Nat} {x : Nat}
    (h : DenseMatrix.containsNat xs x = true) :
    ∃ t, t < xs.size ∧ xs.getD t 0 = x := by
  unfold DenseMatrix.containsNat at h
  rw [Array.any_eq_true] at h
  obtain ⟨t, ht, hbeq⟩ := h
  refine ⟨t, ht, ?_⟩
  rw [array_getD_of_lt' xs 0 ht]
  exact beq_iff_eq.mp hbeq

private theorem freeColumns_or_pivot {cols : Nat} {pivots : Array Nat}
    {k : Nat} (hk : k < cols) :
    (∃ j, j < (freeColumns cols pivots).size ∧
        (freeColumns cols pivots).getD j 0 = k) ∨
      ∃ t, t < pivots.size ∧ pivots.getD t 0 = k := by
  cases hc : DenseMatrix.containsNat pivots k with
  | true => exact Or.inr (containsNat_true_exists hc)
  | false =>
      left
      have hmem : k ∈ (freeColumns cols pivots).toList := by
        unfold freeColumns
        rw [List.toList_toArray, List.mem_filter]
        refine ⟨List.mem_range.mpr hk, ?_⟩
        rw [hc]
        rfl
      obtain ⟨j, hj, hjk⟩ := List.mem_iff_getElem.mp hmem
      have hj' : j < (freeColumns cols pivots).size := by
        simpa using hj
      refine ⟨j, hj', ?_⟩
      rw [array_getD_of_lt' _ 0 hj', ← Array.getElem_toList hj]
      exact hjk

/-- The basis vector of the `i`-th free column is one at that column and zero at
every other free column. -/
theorem basisVector_getD_freeColumn [Field F]
    (rows : Array (Array F)) (pivots : Array Nat) (cols : Nat) {i j : Nat}
    (hi : i < (freeColumns cols pivots).size)
    (hj : j < (freeColumns cols pivots).size) :
    (basisVectorForFreeColumnRows rows pivots cols
        ((freeColumns cols pivots).getD i 0)).getD
      ((freeColumns cols pivots).getD j 0) 0 =
      if j = i then 1 else 0 := by
  obtain ⟨hjlt, hjnot⟩ := freeColumns_mem (freeColumns_getD_mem hj)
  by_cases hij : j = i
  · rw [ite_eq_left hij, hij]
    exact basisVectorForFreeColumnRows_getD_free rows pivots cols
      (freeColumns_mem (freeColumns_getD_mem hi)).1
  · rw [ite_eq_right hij]
    exact basisVectorForFreeColumnRows_getD_none rows pivots cols _ hjlt
      (fun hc ↦ hij (freeColumns_getD_inj hj hi hc))
      (pivotRowOfColumn?_eq_none hjnot)

/-- Coordinatewise completeness of the kernel basis vectors against a fixed
RREF result: any vector orthogonal to the RREF rows agrees, below `cols`,
with the combination of basis vectors whose coefficients are its values at
the free columns. -/
private theorem kernelBasis_complete_aux [Field F] [BEq F] [LawfulBEq F]
    {cols : Nat} {R : ScalarRrefResult (F := F)}
    (hspec : ScalarRrefSpec cols R) {v : Array F}
    (horthR : OrthRows cols R.rows v) :
    ∀ k, k < cols →
      v.getD k 0 =
        ∑ i ∈ Finset.range (freeColumns cols R.pivots).size,
          v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
            (basisVectorForFreeColumnRows R.rows R.pivots cols
              ((freeColumns cols R.pivots).getD i 0)).getD k 0 := by
  have hfree_coord : ∀ j, j < (freeColumns cols R.pivots).size →
      v.getD ((freeColumns cols R.pivots).getD j 0) 0 =
        ∑ i ∈ Finset.range (freeColumns cols R.pivots).size,
          v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
            (basisVectorForFreeColumnRows R.rows R.pivots cols
              ((freeColumns cols R.pivots).getD i 0)).getD
              ((freeColumns cols R.pivots).getD j 0) 0 := by
    intro j hj
    have h0 : ∀ i ∈ Finset.range (freeColumns cols R.pivots).size,
        i ≠ j →
          v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
            (basisVectorForFreeColumnRows R.rows R.pivots cols
              ((freeColumns cols R.pivots).getD i 0)).getD
              ((freeColumns cols R.pivots).getD j 0) 0 = 0 := by
      intro i hi hij
      rw [basisVector_getD_freeColumn R.rows R.pivots cols
        (Finset.mem_range.mp hi) hj, ite_eq_right (fun hc ↦ hij hc.symm), mul_zero]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj) h0,
      basisVector_getD_freeColumn R.rows R.pivots cols hj hj, ite_eq_left rfl,
      mul_one]
  intro k hk
  rcases freeColumns_or_pivot (pivots := R.pivots) hk with
    ⟨j, hj, hjk⟩ | ⟨t, ht, htk⟩
  · rw [← hjk]
    exact hfree_coord j hj
  · have hrow_v := horthR t
    unfold scalarDot at hrow_v
    have hrow_b : ∀ i, i < (freeColumns cols R.pivots).size →
        ∑ k' ∈ Finset.range cols, (R.rows.getD t #[]).getD k' 0 *
          (basisVectorForFreeColumnRows R.rows R.pivots cols
            ((freeColumns cols R.pivots).getD i 0)).getD k' 0 =
          0 := by
      intro i hi
      obtain ⟨hilt, hinot⟩ := freeColumns_mem (freeColumns_getD_mem hi)
      have hb := scalarDot_basisVector hspec hilt hinot t
      unfold scalarDot at hb
      exact hb
    have hsum : ∑ k' ∈ Finset.range cols,
        (R.rows.getD t #[]).getD k' 0 *
          (v.getD k' 0 -
            ∑ i ∈ Finset.range (freeColumns cols R.pivots).size,
              v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
                (basisVectorForFreeColumnRows R.rows R.pivots cols
                  ((freeColumns cols R.pivots).getD i 0)).getD
                  k' 0) = 0 := by
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, hrow_v, zero_sub, neg_eq_zero]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hswap : ∀ k' : Nat,
          (R.rows.getD t #[]).getD k' 0 *
            (v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
              (basisVectorForFreeColumnRows R.rows R.pivots cols
                ((freeColumns cols R.pivots).getD i 0)).getD
                k' 0) =
          v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
            ((R.rows.getD t #[]).getD k' 0 *
              (basisVectorForFreeColumnRows R.rows R.pivots cols
                ((freeColumns cols R.pivots).getD i 0)).getD
                k' 0) :=
        fun k' ↦ mul_left_comm _ _ _
      rw [Finset.sum_congr rfl fun k' _ ↦ hswap k', ← Finset.mul_sum,
        hrow_b i (Finset.mem_range.mp hi), mul_zero]
    have hothers : ∀ k' ∈ Finset.range cols, k' ≠ R.pivots.getD t 0 →
        (R.rows.getD t #[]).getD k' 0 *
          (v.getD k' 0 -
            ∑ i ∈ Finset.range (freeColumns cols R.pivots).size,
              v.getD ((freeColumns cols R.pivots).getD i 0) 0 *
                (basisVectorForFreeColumnRows R.rows R.pivots cols
                  ((freeColumns cols R.pivots).getD i 0)).getD
                  k' 0) = 0 := by
      intro k' hk' hne
      rcases freeColumns_or_pivot (pivots := R.pivots)
          (Finset.mem_range.mp hk') with ⟨j, hj, hjk'⟩ | ⟨s, hs, hsk'⟩
      · rw [← hjk', ← hfree_coord j hj, sub_self, mul_zero]
      · have hst : ¬t = s := fun hc ↦ hne (by rw [hc]; exact hsk'.symm)
        rw [← hsk', hspec.unit s hs t, ite_eq_right hst, zero_mul]
    rw [Finset.sum_eq_single_of_mem (R.pivots.getD t 0)
        (Finset.mem_range.mpr (hspec.pivots_lt t ht)) hothers,
      hspec.unit t ht t, ite_eq_left rfl, one_mul, sub_eq_zero] at hsum
    rw [← htk]
    exact hsum

/-- The row-array kernel basis has one vector per free column. -/
theorem homogeneousKernelBasisRows_size_eq [Field F] [BEq F]
    [LawfulBEq F] (rows : Array (Array F)) (cols : Nat) :
    (homogeneousKernelBasisRows rows cols).size =
      (freeColumns cols (scalarRrefRows rows cols).pivots).size := by
  simp only [homogeneousKernelBasisRows, Array.size_map]

/-- The `i`-th row-array kernel basis vector is the basis vector of the `i`-th
free column. -/
theorem homogeneousKernelBasisRows_getD_eq [Field F] [BEq F]
    [LawfulBEq F] (rows : Array (Array F)) (cols : Nat) {i : Nat}
    (hi : i <
      (freeColumns cols (scalarRrefRows rows cols).pivots).size) :
    (homogeneousKernelBasisRows rows cols).getD i #[] =
      basisVectorForFreeColumnRows (scalarRrefRows rows cols).rows
        (scalarRrefRows rows cols).pivots cols
        ((freeColumns cols
          (scalarRrefRows rows cols).pivots).getD i 0) := by
  simp only [homogeneousKernelBasisRows]
  rw [array_getD_of_lt' _ #[] (by rw [Array.size_map]; exact hi),
    Array.getElem_map, array_getD_of_lt' _ 0 hi]

/-- **Completeness of the row-array kernel.**  Every vector orthogonal to
all input rows over the coordinates `0, …, cols - 1` is, coordinatewise below
`cols`, the `F`-linear combination of the emitted kernel basis vectors whose
coefficients are the values of the vector at the corresponding free
columns. -/
theorem homogeneousKernelBasisRows_complete [Field F] [BEq F] [LawfulBEq F]
    (rows : Array (Array F)) (cols : Nat) {v : Array F}
    (hv : ∀ r ∈ rows.toList,
      ∑ k ∈ Finset.range cols, r.getD k 0 * v.getD k 0 = 0) :
    ∀ k, k < cols →
      v.getD k 0 =
        ∑ i ∈ Finset.range (homogeneousKernelBasisRows rows cols).size,
          v.getD ((freeColumns cols
              (scalarRrefRows rows cols).pivots).getD i 0) 0 *
            ((homogeneousKernelBasisRows rows cols).getD i #[]).getD k 0 := by
  have horth : OrthRows cols rows v := by
    intro i
    by_cases hi : i < rows.size
    · have hmem : rows[i] ∈ rows.toList := by
        rw [← Array.getElem_toList (by simpa using hi)]
        exact List.getElem_mem _
      have h0 := hv rows[i] hmem
      unfold scalarDot
      rw [array_getD_of_lt' rows #[] hi]
      exact h0
    · rw [array_getD_of_le' rows #[] (Nat.le_of_not_lt hi)]
      exact scalarDot_empty cols v
  have hmain := kernelBasis_complete_aux (scalarRrefRows_spec rows cols)
    (orthRows_scalarRrefRows_forward horth)
  intro k hk
  rw [homogeneousKernelBasisRows_size_eq rows cols, hmain k hk]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [homogeneousKernelBasisRows_getD_eq rows cols (Finset.mem_range.mp hi)]

end Main

end DenseMatrix

end CompPoly
