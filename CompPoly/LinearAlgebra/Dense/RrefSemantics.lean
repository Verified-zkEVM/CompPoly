/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.RowOpsCorrectness
import Init.Data.List.Monadic
import Init.Data.Range.Lemmas
import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Dense RREF Semantic Correctness

Semantic preservation and reflection lemmas for dense row reduction.
-/

namespace CompPoly

namespace DenseMatrix

def findPivotRowStep [Zero F] [BEq F] (M : DenseMatrix F) (col : Nat)
    (out : Option Nat) (row : Nat) : Option Nat :=
  if out.isNone && !(M.get row col == 0) then some row else out

theorem list_forIn_yield_eq_foldl {α β : Type*}
    (xs : List α) (init : β) (f : β → α → β) :
    (Id.run (forIn xs init fun x acc => pure (ForInStep.yield (f acc x))) : β) =
      xs.foldl f init := by
  induction xs generalizing init with
  | nil =>
      simp
  | cons x xs ih =>
      simp

theorem findPivotRowStep_fold_some [Zero F] [BEq F]
    (M : DenseMatrix F) (col : Nat) (xs : List Nat) (pivot : Nat) :
    xs.foldl (findPivotRowStep M col) (some pivot) = some pivot := by
  induction xs generalizing pivot with
  | nil => rfl
  | cons row xs ih =>
      simp [List.foldl, findPivotRowStep, ih]

theorem list_forIn_findPivotRowStep_eq_foldl [Zero F] [BEq F]
    (M : DenseMatrix F) (col : Nat) (xs : List Nat) (out : Option Nat) :
    (Id.run (forIn xs out fun row out =>
      if out = none ∧ (M.get row col == 0) = false then
        pure (ForInStep.yield (some row))
      else
        pure (ForInStep.yield out)) : Option Nat) =
      xs.foldl (findPivotRowStep M col) out := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons row xs ih =>
      by_cases h : out = none ∧ (M.get row col == 0) = false
      · rcases h with ⟨hout, hne⟩
        subst out
        have hstep : findPivotRowStep M col none row = some row := by
          simp [findPivotRowStep, hne]
        simpa [List.forIn_cons, List.foldl_cons, hne, hstep] using ih (some row)
      · have hstep : findPivotRowStep M col out row = out := by
          cases hout : out with
          | none =>
              by_cases hne : (M.get row col == 0) = false
              · exfalso
                exact h ⟨hout, hne⟩
              · simp [findPivotRowStep, hne]
          | some p =>
              simp [findPivotRowStep]
        simpa [List.forIn_cons, List.foldl_cons, h, hstep] using ih out

theorem findPivotRow_fold_mem [Zero F] [BEq F]
    (M : DenseMatrix F) (col : Nat) {xs : List Nat} {pivot : Nat}
    (h : xs.foldl (findPivotRowStep M col) none = some pivot) :
    pivot ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons row xs ih =>
      change List.foldl (findPivotRowStep M col)
        (findPivotRowStep M col none row) xs = some pivot at h
      by_cases hne : (M.get row col == 0) = false
      · have hstep : findPivotRowStep M col none row = some row := by
          simp [findPivotRowStep, hne]
        rw [hstep, findPivotRowStep_fold_some] at h
        simp at h
        subst pivot
        simp
      · have hstep : findPivotRowStep M col none row = none := by
          cases hb : M.get row col == 0 <;> simp [findPivotRowStep, hb] at hne ⊢
        rw [hstep] at h
        exact List.mem_cons.mpr (Or.inr (ih h))

theorem findPivotRow_fold_get_ne_zero [Zero F] [BEq F]
    (M : DenseMatrix F) (col : Nat) {xs : List Nat} {pivot : Nat}
    (h : xs.foldl (findPivotRowStep M col) none = some pivot) :
    (M.get pivot col == 0) = false := by
  induction xs with
  | nil =>
      simp at h
  | cons row xs ih =>
      change List.foldl (findPivotRowStep M col)
        (findPivotRowStep M col none row) xs = some pivot at h
      by_cases hne : (M.get row col == 0) = false
      · have hstep : findPivotRowStep M col none row = some row := by
          simp [findPivotRowStep, hne]
        rw [hstep, findPivotRowStep_fold_some] at h
        simp at h
        subst pivot
        exact hne
      · have hstep : findPivotRowStep M col none row = none := by
          cases hb : M.get row col == 0 <;> simp [findPivotRowStep, hb] at hne ⊢
        rw [hstep] at h
        exact ih h

theorem findPivotRow_fold_none_get_eq_zero [Zero F] [BEq F] [LawfulBEq F]
    (M : DenseMatrix F) (col : Nat) {xs : List Nat}
    (h : xs.foldl (findPivotRowStep M col) none = none) {row : Nat}
    (hrow : row ∈ xs) :
    M.get row col = 0 := by
  induction xs with
  | nil =>
      simp at hrow
  | cons r xs ih =>
      change List.foldl (findPivotRowStep M col)
        (findPivotRowStep M col none r) xs = none at h
      by_cases hne : (M.get r col == 0) = false
      · have hstep : findPivotRowStep M col none r = some r := by
          simp [findPivotRowStep, hne]
        rw [hstep, findPivotRowStep_fold_some] at h
        simp at h
      · have hstep : findPivotRowStep M col none r = none := by
          cases hb : M.get r col == 0 <;> simp [findPivotRowStep, hb] at hne ⊢
        rw [hstep] at h
        simp only [List.mem_cons] at hrow
        cases hrow with
        | inl hr =>
            subst r
            cases hb : M.get row col == 0
            · simp [hb] at hne
            · exact (beq_iff_eq.mp hb)
        | inr htail =>
            exact ih h htail

theorem findPivotRow_eq_fold [Zero F] [BEq F]
    (M : DenseMatrix F) (start col : Nat) :
    findPivotRow M start col =
      (List.range' start (M.rows - start)).foldl (findPivotRowStep M col) none := by
  simp [findPivotRow, Std.Legacy.Range.forIn_eq_forIn_range',
    list_forIn_findPivotRowStep_eq_foldl]

theorem findPivotRow_some_lt [Zero F] [BEq F]
    {M : DenseMatrix F} {start col pivot : Nat}
    (h : findPivotRow M start col = some pivot) :
    pivot < M.rows := by
  rw [findPivotRow_eq_fold] at h
  have hmem := findPivotRow_fold_mem M col h
  have hrange := List.mem_range'_1.mp hmem
  omega

theorem findPivotRow_some_ge [Zero F] [BEq F]
    {M : DenseMatrix F} {start col pivot : Nat}
    (h : findPivotRow M start col = some pivot) :
    start ≤ pivot := by
  rw [findPivotRow_eq_fold] at h
  have hmem := findPivotRow_fold_mem M col h
  have hrange := List.mem_range'_1.mp hmem
  omega

theorem findPivotRow_some_ne_zero [Zero F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} {start col pivot : Nat}
    (h : findPivotRow M start col = some pivot) :
    M.get pivot col ≠ 0 := by
  rw [findPivotRow_eq_fold] at h
  have hb := findPivotRow_fold_get_ne_zero M col h
  intro hz
  simp [hz] at hb

theorem findPivotRow_none_get_eq_zero [Zero F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} {start col row : Nat}
    (h : findPivotRow M start col = none) (hstart : start ≤ row) (hrow : row < M.rows) :
    M.get row col = 0 := by
  rw [findPivotRow_eq_fold] at h
  apply findPivotRow_fold_none_get_eq_zero M col h
  exact List.mem_range'_1.mpr (by omega)

theorem list_forIn_addScaledRow_wf [Field F]
    (rows : List Nat) {out : DenseMatrix F} (pivotRow pivotCol : Nat)
    (hout : WellFormed out) :
    WellFormed
      (Id.run (forIn rows out fun row r =>
        if row = pivotRow then
          pure (ForInStep.yield r)
        else
          pure (ForInStep.yield
            (addScaledRow r row pivotRow (-(r.get row pivotCol)))) :
        Id (DenseMatrix F))) := by
  induction rows generalizing out with
  | nil =>
      simpa
  | cons row rows ih =>
      by_cases hrow : row = pivotRow
      · simpa [List.forIn_cons, hrow] using ih (out := out) hout
      · have hstep : WellFormed (addScaledRow out row pivotRow (-(out.get row pivotCol))) :=
          addScaledRow_wf hout row pivotRow (-(out.get row pivotCol))
        simpa [List.forIn_cons, hrow] using
          ih (out := addScaledRow out row pivotRow (-(out.get row pivotCol)))
            hstep

theorem normalizeAndEliminate_wf [Field F] [BEq F]
    {M : DenseMatrix F} (hM : WellFormed M) (pivotRow pivotCol : Nat) :
    WellFormed (normalizeAndEliminate M pivotRow pivotCol) := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · simp [hp, hM]
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hscaled : WellFormed (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) :=
      scaleRow_wf hM pivotRow (M.get pivotRow pivotCol)⁻¹
    simpa [scaleRow] using
      list_forIn_addScaledRow_wf
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        pivotRow pivotCol hscaled

theorem list_forIn_addScaledRow_solution_of_solution [Field F]
    (rows : List Nat) {out : DenseMatrix F} {v : Array F}
    (pivotRow pivotCol : Nat) (hpivot : pivotRow < out.rows)
    (hout : WellFormed out) (hsol : IsHomogeneousSolution out v) :
    IsHomogeneousSolution
      (Id.run (forIn rows out fun row r =>
        if row = pivotRow then
          pure (ForInStep.yield r)
        else
          pure (ForInStep.yield
            (addScaledRow r row pivotRow (-(r.get row pivotCol)))) :
        Id (DenseMatrix F))) v := by
  induction rows generalizing out with
  | nil =>
      simpa
  | cons row rows ih =>
      by_cases hrow : row = pivotRow
      · simpa [List.forIn_cons, hrow] using
          ih (out := out) hpivot hout hsol
      · have hstepRows :
            (addScaledRow out row pivotRow (-(out.get row pivotCol))).rows = out.rows := by
          simp [addScaledRow]
        have hpivotStep : pivotRow <
            (addScaledRow out row pivotRow (-(out.get row pivotCol))).rows := by
          simpa [hstepRows] using hpivot
        have hstepWf : WellFormed (addScaledRow out row pivotRow (-(out.get row pivotCol))) :=
          addScaledRow_wf hout row pivotRow (-(out.get row pivotCol))
        have hrowLt : row < out.rows ∨ out.rows ≤ row := lt_or_ge row out.rows
        have hstepSol : IsHomogeneousSolution
            (addScaledRow out row pivotRow (-(out.get row pivotCol))) v := by
          cases hrowLt with
          | inl hrowLt =>
              exact isHomogeneousSolution_addScaledRow_of_solution hout hrowLt hpivot
                (-(out.get row pivotCol)) hsol
          | inr hrowGe =>
              intro r hr
              have hrOut : r < out.rows := by simpa [addScaledRow] using hr
              have hrow_ne_r : row ≠ r := by omega
              rw [dotRow_addScaledRow_of_ne (M := out) (target := row)
                (source := pivotRow) (row := r) (-(out.get row pivotCol)) hrow_ne_r v]
              exact hsol r hrOut
        simpa [List.forIn_cons, hrow] using
          ih (out := addScaledRow out row pivotRow (-(out.get row pivotCol)))
            hpivotStep hstepWf hstepSol

theorem list_forIn_addScaledRow_solution_reflect [Field F]
    (rows : List Nat) {out : DenseMatrix F} {v : Array F}
    (pivotRow pivotCol : Nat) (hpivot : pivotRow < out.rows)
    (hout : WellFormed out)
    (hsol :
      IsHomogeneousSolution
        (Id.run (forIn rows out fun row r =>
          if row = pivotRow then
            pure (ForInStep.yield r)
          else
            pure (ForInStep.yield
              (addScaledRow r row pivotRow (-(r.get row pivotCol)))) :
          Id (DenseMatrix F))) v) :
    IsHomogeneousSolution out v := by
  induction rows generalizing out with
  | nil =>
      simpa using hsol
  | cons row rows ih =>
      by_cases hrow : row = pivotRow
      · apply ih (out := out) hpivot hout
        simpa [List.forIn_cons, hrow] using hsol
      · have hstepRows :
            (addScaledRow out row pivotRow (-(out.get row pivotCol))).rows = out.rows := by
          simp [addScaledRow]
        have hpivotStep : pivotRow <
            (addScaledRow out row pivotRow (-(out.get row pivotCol))).rows := by
          simpa [hstepRows] using hpivot
        have hstepWf : WellFormed (addScaledRow out row pivotRow (-(out.get row pivotCol))) :=
          addScaledRow_wf hout row pivotRow (-(out.get row pivotCol))
        have hstepSol : IsHomogeneousSolution
            (addScaledRow out row pivotRow (-(out.get row pivotCol))) v := by
          apply ih (out := addScaledRow out row pivotRow (-(out.get row pivotCol)))
            hpivotStep hstepWf
          simpa [List.forIn_cons, hrow] using hsol
        by_cases hrowLt : row < out.rows
        · exact isHomogeneousSolution_of_addScaledRow_solution hout hrowLt hpivot hrow
            (-(out.get row pivotCol)) hstepSol
        · intro r hr
          have hrStep : r <
              (addScaledRow out row pivotRow (-(out.get row pivotCol))).rows := by
            simpa [addScaledRow] using hr
          have hdot := hstepSol r hrStep
          have hrow_ne_r : row ≠ r := by omega
          rw [dotRow_addScaledRow_of_ne (M := out) (target := row)
            (source := pivotRow) (row := r) (-(out.get row pivotCol)) hrow_ne_r v] at hdot
          exact hdot

theorem isHomogeneousSolution_normalizeAndEliminate_of_solution
    [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} {v : Array F} (hM : WellFormed M)
    {pivotRow pivotCol : Nat} (hpivotRow : pivotRow < M.rows)
    (hsol : IsHomogeneousSolution M v) :
    IsHomogeneousSolution (normalizeAndEliminate M pivotRow pivotCol) v := by
  unfold normalizeAndEliminate
  by_cases hp : M.get pivotRow pivotCol == 0
  · simp [hp, hsol]
  · simp only [hp]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have hscaledWf : WellFormed (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) :=
      scaleRow_wf hM pivotRow (M.get pivotRow pivotCol)⁻¹
    have hscaledSol : IsHomogeneousSolution (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) v :=
      isHomogeneousSolution_scaleRow_of_solution hM hpivotRow
        (M.get pivotRow pivotCol)⁻¹ hsol
    have hpivotScaled : pivotRow <
        (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows := by
      simpa [scaleRow] using hpivotRow
    simpa [scaleRow] using
      list_forIn_addScaledRow_solution_of_solution
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        pivotRow pivotCol hpivotScaled hscaledWf hscaledSol

theorem isHomogeneousSolution_of_normalizeAndEliminate_solution
    [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} {v : Array F} (hM : WellFormed M)
    {pivotRow pivotCol : Nat} (hpivotRow : pivotRow < M.rows)
    (hpivot : M.get pivotRow pivotCol ≠ 0)
    (hsol : IsHomogeneousSolution (normalizeAndEliminate M pivotRow pivotCol) v) :
    IsHomogeneousSolution M v := by
  unfold normalizeAndEliminate at hsol
  by_cases hp : M.get pivotRow pivotCol == 0
  · have hzero : M.get pivotRow pivotCol = 0 := beq_iff_eq.mp hp
    exact (hpivot hzero).elim
  · simp only [hp] at hsol
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hsol
    have hscaledWf : WellFormed (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) :=
      scaleRow_wf hM pivotRow (M.get pivotRow pivotCol)⁻¹
    have hpivotScaled : pivotRow <
        (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows := by
      simpa [scaleRow] using hpivotRow
    have hscaledSol : IsHomogeneousSolution
        (scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹) v := by
      apply list_forIn_addScaledRow_solution_reflect
        (List.range' 0
          (Std.Legacy.Range.size
            [:(scaleRow M pivotRow (M.get pivotRow pivotCol)⁻¹).rows]) 1)
        pivotRow pivotCol hpivotScaled hscaledWf
      simpa [scaleRow] using hsol
    exact isHomogeneousSolution_of_scaleRow_solution hM hpivotRow
      (inv_ne_zero hpivot) hscaledSol

theorem rrefLoop_cols [Field F] [BEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      ((rrefLoop fuel col row M pivots).matrix).cols = M.cols := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots
      rfl
  | succ fuel ih =>
      intro col row M pivots
      rw [rrefLoop]
      split
      · split
        · exact ih _ _ _ _
        · rename_i pivotRow _hpivot
          calc
            ((rrefLoop fuel (col + 1) (row + 1)
                (normalizeAndEliminate (swapRows M pivotRow row) row col)
                (pivots.push col)).matrix).cols
                = (normalizeAndEliminate (swapRows M pivotRow row) row col).cols := ih _ _ _ _
            _ = (swapRows M pivotRow row).cols := normalizeAndEliminate_cols _ _ _
            _ = M.cols := swapRows_cols _ _ _
      · rfl

theorem rrefLoop_rows [Field F] [BEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      ((rrefLoop fuel col row M pivots).matrix).rows = M.rows := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots
      rfl
  | succ fuel ih =>
      intro col row M pivots
      rw [rrefLoop]
      split
      · split
        · exact ih _ _ _ _
        · rename_i pivotRow _hpivot
          calc
            ((rrefLoop fuel (col + 1) (row + 1)
                (normalizeAndEliminate (swapRows M pivotRow row) row col)
                (pivots.push col)).matrix).rows
                = (normalizeAndEliminate (swapRows M pivotRow row) row col).rows := ih _ _ _ _
            _ = (swapRows M pivotRow row).rows := normalizeAndEliminate_rows _ _ _
            _ = M.rows := swapRows_rows _ _ _
      · rfl

theorem rref_cols [Field F] [BEq F]
    (M : DenseMatrix F) : (rref M).matrix.cols = M.cols := by
  unfold rref
  exact rrefLoop_cols _ _ _ _ _

theorem rref_rows [Field F] [BEq F]
    (M : DenseMatrix F) : (rref M).matrix.rows = M.rows := by
  unfold rref
  exact rrefLoop_rows _ _ _ _ _

theorem rrefLoop_wf [Field F] [BEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots,
      WellFormed M → WellFormed (rrefLoop fuel col row M pivots).matrix := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots hM
      exact hM
  | succ fuel ih =>
      intro col row M pivots hM
      rw [rrefLoop]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard]
        cases hp : findPivotRow M row col with
        | none =>
            exact ih (col + 1) row M pivots hM
        | some pivotRow =>
            have hswapped : WellFormed (swapRows M pivotRow row) :=
              swapRows_wf hM pivotRow row
            have hreduced : WellFormed
                (normalizeAndEliminate (swapRows M pivotRow row) row col) :=
              normalizeAndEliminate_wf hswapped row col
            exact ih (col + 1) (row + 1)
              (normalizeAndEliminate (swapRows M pivotRow row) row col)
              (pivots.push col) hreduced
      · simp [hguard, hM]

theorem rref_wf [Field F] [BEq F] {M : DenseMatrix F}
    (hM : WellFormed M) : WellFormed (rref M).matrix := by
  unfold rref
  exact rrefLoop_wf _ _ _ _ _ hM

theorem isHomogeneousSolution_rrefLoop_of_solution
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots {v : Array F},
      WellFormed M →
        IsHomogeneousSolution M v →
          IsHomogeneousSolution (rrefLoop fuel col row M pivots).matrix v := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots v hM hsol
      exact hsol
  | succ fuel ih =>
      intro col row M pivots v hM hsol
      rw [rrefLoop]
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard]
        cases hp : findPivotRow M row col with
        | none =>
            exact ih (col + 1) row M pivots hM hsol
        | some pivotRow =>
            have hand := Bool.and_eq_true_iff.mp hguard
            have hcol : col < M.cols := of_decide_eq_true hand.1
            have hrow : row < M.rows := of_decide_eq_true hand.2
            have hpivot : pivotRow < M.rows := findPivotRow_some_lt hp
            have hswappedWf : WellFormed (swapRows M pivotRow row) :=
              swapRows_wf hM pivotRow row
            have hswappedSol : IsHomogeneousSolution (swapRows M pivotRow row) v :=
              isHomogeneousSolution_swapRows_of_solution hM hpivot hrow hsol
            have hrowSwapped : row < (swapRows M pivotRow row).rows := by
              simpa [swapRows_rows] using hrow
            have hreducedWf : WellFormed
                (normalizeAndEliminate (swapRows M pivotRow row) row col) :=
              normalizeAndEliminate_wf hswappedWf row col
            have hreducedSol : IsHomogeneousSolution
                (normalizeAndEliminate (swapRows M pivotRow row) row col) v :=
              isHomogeneousSolution_normalizeAndEliminate_of_solution hswappedWf
                hrowSwapped hswappedSol
            exact ih (col + 1) (row + 1)
              (normalizeAndEliminate (swapRows M pivotRow row) row col)
              (pivots.push col) hreducedWf hreducedSol
      · simp [hguard, hsol]

theorem isHomogeneousSolution_rref [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (hsol : IsHomogeneousSolution M v) :
    IsHomogeneousSolution (rref M).matrix v := by
  unfold rref
  exact isHomogeneousSolution_rrefLoop_of_solution _ _ _ _ _ hM hsol

theorem isHomogeneousSolution_of_rrefLoop_solution
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ fuel col row (M : DenseMatrix F) pivots {v : Array F},
      WellFormed M →
        IsHomogeneousSolution (rrefLoop fuel col row M pivots).matrix v →
          IsHomogeneousSolution M v := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row M pivots v hM hsol
      exact hsol
  | succ fuel ih =>
      intro col row M pivots v hM hsol
      rw [rrefLoop] at hsol
      by_cases hguard : col < M.cols && row < M.rows
      · simp only [hguard] at hsol
        cases hp : findPivotRow M row col with
        | none =>
            exact ih (col + 1) row M pivots hM (by simpa [hp] using hsol)
        | some pivotRow =>
            have hand := Bool.and_eq_true_iff.mp hguard
            have hcol : col < M.cols := of_decide_eq_true hand.1
            have hrow : row < M.rows := of_decide_eq_true hand.2
            have hpivot : pivotRow < M.rows := findPivotRow_some_lt hp
            have hswappedWf : WellFormed (swapRows M pivotRow row) :=
              swapRows_wf hM pivotRow row
            have hrowSwapped : row < (swapRows M pivotRow row).rows := by
              simpa [swapRows_rows] using hrow
            have hreducedWf : WellFormed
                (normalizeAndEliminate (swapRows M pivotRow row) row col) :=
              normalizeAndEliminate_wf hswappedWf row col
            have hreducedSol : IsHomogeneousSolution
                (normalizeAndEliminate (swapRows M pivotRow row) row col) v :=
              ih (col + 1) (row + 1)
                (normalizeAndEliminate (swapRows M pivotRow row) row col)
                (pivots.push col) hreducedWf (by simpa [hp] using hsol)
            have hpivotSwap : (swapRows M pivotRow row).get row col ≠ 0 := by
              rw [swapRows_get_right hM hrow hcol]
              exact findPivotRow_some_ne_zero hp
            have hswappedSol : IsHomogeneousSolution (swapRows M pivotRow row) v :=
              isHomogeneousSolution_of_normalizeAndEliminate_solution hswappedWf
                hrowSwapped hpivotSwap hreducedSol
            exact isHomogeneousSolution_of_swapRows_solution hM hpivot hrow hswappedSol
      · simpa [hguard] using hsol

theorem isHomogeneousSolution_of_rref [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (hsol : IsHomogeneousSolution (rref M).matrix v) :
    IsHomogeneousSolution M v := by
  unfold rref at hsol
  exact isHomogeneousSolution_of_rrefLoop_solution _ _ _ _ _ hM hsol

end DenseMatrix

end CompPoly
