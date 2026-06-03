/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Selection

/-!
# Koetter Update Correctness Helpers

Degree, weak-leading, discrepancy, and size invariants for one-step and folded
Koetter updates.
-/

namespace CompPoly

namespace GuruswamiSudan

theorem koetterUpdatedEntry_pivot_natWeightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) (pivot : KoetterPivot F) :
    CBivariate.natWeightedDegree
        (koetterUpdatedEntry constraint basis pivot pivot.index) 1 (yWeight params) ≤
      CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params) + 1 := by
  unfold koetterUpdatedEntry
  rw [if_pos (by simp)]
  exact natWeightedDegree_linearXFactor_mul_le constraint.x
    (basis.getD pivot.index 0) (yWeight params)

theorem koetterUpdatedEntry_nonpivot_natWeightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) (pivot : KoetterPivot F)
    {idx : Nat} (hidxNe : ¬ idx == pivot.index) (hi : idx < basis.size)
    (hpivotDegree :
      pivot.weightedDegree =
        CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params))
    (hpivotMin : ∀ k, k < basis.size →
      koetterDiscrepancy constraint (basis.getD k 0) ≠ 0 →
        pivot.weightedDegree ≤
          CBivariate.natWeightedDegree (basis.getD k 0) 1 (yWeight params)) :
    CBivariate.natWeightedDegree
        (koetterUpdatedEntry constraint basis pivot idx) 1 (yWeight params) ≤
      CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) := by
  unfold koetterUpdatedEntry
  rw [if_neg hidxNe]
  by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
  · rw [if_pos hdelta]
  · rw [if_neg hdelta]
    have hdiscNe : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := by
      intro hzero
      have hzeroBeq : (koetterDiscrepancy constraint (basis.getD idx 0) == 0) = true := by
        rw [hzero]
        simp
      exact hdelta hzeroBeq
    have hpivotLeIdx :
        CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params) ≤
          CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) := by
      rw [← hpivotDegree]
      exact hpivotMin idx hi hdiscNe
    apply le_trans (natWeightedDegree_sub_le
      (basis.getD idx 0)
      (CBivariate.CC
          (koetterDiscrepancy constraint (basis.getD idx 0) / pivot.discrepancy) *
        basis.getD pivot.index 0) 1 (yWeight params))
    apply max_le
    · exact le_rfl
    · exact le_trans
        (natWeightedDegree_CC_mul_le
          (koetterDiscrepancy constraint (basis.getD idx 0) / pivot.discrepancy)
          (basis.getD pivot.index 0) 1 (yWeight params))
        hpivotLeIdx

theorem koetterUpdatedEntry_pivot_natWeightedDegree_le_of_selectPivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (hpivot : koetterSelectPivot params constraint basis = some pivot) :
    CBivariate.natWeightedDegree
        (koetterUpdatedEntry constraint basis pivot pivot.index) 1 (yWeight params) ≤
      pivot.weightedDegree + 1 := by
  rw [koetterSelectPivot_some_weightedDegree_eq hpivot]
  exact koetterUpdatedEntry_pivot_natWeightedDegree_le params constraint basis pivot

theorem koetterUpdatedEntry_nonpivot_natWeightedDegree_le_of_selectPivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F} {idx : Nat}
    (hpivot : koetterSelectPivot params constraint basis = some pivot)
    (hidxNe : ¬ idx == pivot.index) (hi : idx < basis.size) :
    CBivariate.natWeightedDegree
        (koetterUpdatedEntry constraint basis pivot idx) 1 (yWeight params) ≤
      CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) := by
  exact koetterUpdatedEntry_nonpivot_natWeightedDegree_le params constraint basis pivot
    hidxNe hi (koetterSelectPivot_some_weightedDegree_eq hpivot)
    (koetterSelectPivot_some_weightedDegree_le hpivot)

theorem koetterUpdatedEntry_rowLeadingAt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (hBasis : koetterBasisWeakLeading params basis)
    (hpivot : koetterSelectPivot params constraint basis = some pivot)
    {idx : Nat} (hi : idx < basis.size) :
    koetterRowLeadingAt params idx
      (koetterUpdatedEntry constraint basis pivot idx) := by
  unfold koetterUpdatedEntry
  by_cases hidx : idx == pivot.index
  · have hidxEq : idx = pivot.index := LawfulBEq.eq_of_beq hidx
    subst idx
    rw [if_pos (by simp)]
    have hpivotLt : pivot.index < basis.size :=
      koetterSelectPivot_some_index_lt hpivot
    have hPivotRow :
        koetterRowLeadingAt params pivot.index (basis.getD pivot.index 0) := by
      simpa [koetterBasisWeakLeading, Array.getD_eq_getD_getElem?] using
        hBasis pivot.index hpivotLt
    exact koetterRowLeadingAt_linearXFactor_mul constraint.x hPivotRow
  · rw [if_neg hidx]
    by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
    · rw [if_pos hdelta]
      simpa [koetterBasisWeakLeading, Array.getD_eq_getD_getElem?] using hBasis idx hi
    · rw [if_neg hdelta]
      have hdiscNe : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := by
        intro hzero
        have hzeroBeq :
            (koetterDiscrepancy constraint (basis.getD idx 0) == 0) = true := by
          rw [hzero]
          simp
        exact hdelta hzeroBeq
      have hpivotLt : pivot.index < basis.size :=
        koetterSelectPivot_some_index_lt hpivot
      have hCurrent :
          koetterRowLeadingAt params idx (basis.getD idx 0) := by
        simpa [koetterBasisWeakLeading, Array.getD_eq_getD_getElem?] using hBasis idx hi
      have hPivot :
          koetterRowLeadingAt params pivot.index (basis.getD pivot.index 0) := by
        simpa [koetterBasisWeakLeading, Array.getD_eq_getD_getElem?] using
          hBasis pivot.index hpivotLt
      have hpivotDegree := koetterSelectPivot_some_weightedDegree_eq hpivot
      have hpivotLeIdx :
          CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params) ≤
            CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) := by
        rw [← hpivotDegree]
        exact koetterSelectPivot_some_weightedDegree_le hpivot idx hi hdiscNe
      have htie :
          CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params) =
            CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) →
              pivot.index < idx := by
        intro hdegreeEq
        have hnotBetter := koetterSelectPivot_some_not_better hpivot idx hi hdiscNe
        have hcandidateDegree :
            ({ index := idx
               discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
               weightedDegree :=
                CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
              KoetterPivot F).weightedDegree = pivot.weightedDegree := by
          rw [hpivotDegree]
          exact hdegreeEq.symm
        have hpivotLeIdx' :=
          koetterPivotBetter_not_index_le_of_weightedDegree_eq hnotBetter hcandidateDegree
        have hpivotLeIdxNat : pivot.index ≤ idx := by
          simpa using hpivotLeIdx'
        have hidxNeEq : idx ≠ pivot.index := by
          intro hEq
          subst idx
          simp at hidx
        omega
      exact koetterRowLeadingAt_sub_cc_mul_of_pivot_order
        (koetterDiscrepancy constraint (basis.getD idx 0) / pivot.discrepancy)
        hCurrent hPivot hpivotLeIdx htie

theorem koetterSelectPivot_none_discrepancy_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)}
    (h : koetterSelectPivot params constraint basis = none) :
    ∀ idx, idx < basis.size → koetterDiscrepancy constraint (basis.getD idx 0) = 0 := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change (List.range basis.size).foldl step none = none at h
  have hstepNone : ∀ best idx, step best idx = none →
      best = none ∧ koetterDiscrepancy constraint (basis.getD idx 0) = 0 := by
    intro best idx hstep
    unfold step at hstep
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none => exact ⟨rfl, hzero⟩
      | some _current =>
          simp [hzero'] at hstep
    · have hzero' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none =>
          simp [hzero'] at hstep
      | some current =>
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                      (yWeight params) } :
                  KoetterPivot F)
                current = true
          · simp [hzero', hbetter] at hstep
          · simp [hzero', hbetter] at hstep
  have hfoldNoneAux : ∀ (xs : List Nat) best, xs.foldl step best = none →
      best = none ∧
        ∀ idx, idx ∈ xs → koetterDiscrepancy constraint (basis.getD idx 0) = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro best hfold
        exact ⟨hfold, by simp⟩
    | cons idx xs ih =>
        intro best hfold
        simp only [List.foldl_cons] at hfold
        rcases ih (step best idx) hfold with ⟨hstepEq, hxs⟩
        rcases hstepNone best idx hstepEq with ⟨hbest, hidxZero⟩
        refine ⟨hbest, ?_⟩
        intro j hj
        simp at hj
        cases hj with
        | inl hji =>
            subst j
            exact hidxZero
        | inr htail =>
            exact hxs j htail
  have hall := (hfoldNoneAux (List.range basis.size) none h).2
  intro idx hi
  exact hall idx (by simpa using hi)

theorem koetterUpdatedEntry_satisfies_current {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (idx : Nat)
    (hPivotDisc : pivot.discrepancy = koetterDiscrepancy constraint (basis.getD pivot.index 0))
    (hPivotNe : pivot.discrepancy ≠ 0)
    (hLower : ∀ a, constraint.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD pivot.index 0) = 0) :
    koetterDiscrepancy constraint
      (koetterUpdatedEntry constraint basis pivot idx) = 0 := by
  unfold koetterUpdatedEntry koetterDiscrepancy
  by_cases hidx : idx == pivot.index
  · have hidxEq : idx = pivot.index := beq_iff_eq.mp hidx
    rw [if_pos hidx]
    subst idx
    cases hx : constraint.xOrder with
    | zero =>
        rw [CBivariate.hasseDerivativeEval_linearXFactor_mul_zero_xOrder]
    | succ a =>
        rw [CBivariate.hasseDerivativeEval_linearXFactor_mul_succ_xOrder]
        exact hLower a hx
  · rw [if_neg hidx]
    by_cases hdelta : CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder
        constraint.x constraint.y (basis.getD idx 0) == 0
    · rw [if_pos hdelta]
      exact beq_iff_eq.mp hdelta
    · rw [if_neg hdelta]
      rw [CBivariate.hasseDerivativeEval_sub]
      rw [CBivariate.hasseDerivativeEval_CC_mul]
      rw [hPivotDisc]
      change
        CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
              constraint.y (basis.getD idx 0) -
            CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
                constraint.y (basis.getD idx 0) /
              koetterDiscrepancy constraint (basis.getD pivot.index 0) *
                koetterDiscrepancy constraint (basis.getD pivot.index 0) =
          0
      rw [div_mul_cancel₀]
      · ring
      · rw [← hPivotDisc]
        exact hPivotNe

theorem koetterUpdatedEntry_preserves_prior {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (current prior : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) {idx : Nat} (hi : idx < basis.size)
    (hpivot : pivot.index < basis.size)
    (hPrior : ∀ k, k < basis.size → koetterDiscrepancy prior (basis.getD k 0) = 0)
    (hPriorLower : ∀ k, k < basis.size → ∀ a, prior.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a prior.yOrder prior.x prior.y (basis.getD k 0) = 0) :
    koetterDiscrepancy prior (koetterUpdatedEntry current basis pivot idx) = 0 := by
  unfold koetterUpdatedEntry
  by_cases hidx : idx == pivot.index
  · rw [if_pos hidx]
    cases hx : prior.xOrder with
    | zero =>
        rw [koetterDiscrepancy, hx,
          CBivariate.hasseDerivativeEval_linearXFactor_mul_zero_xOrder_general]
        have hzero :
            CBivariate.hasseDerivativeEval 0 prior.yOrder prior.x prior.y
              (basis.getD idx 0) = 0 := by
          simpa [koetterDiscrepancy, hx] using hPrior idx hi
        rw [hzero]
        simp
    | succ a =>
        rw [koetterDiscrepancy, hx,
          CBivariate.hasseDerivativeEval_linearXFactor_mul_succ_xOrder_general]
        have hcur :
            CBivariate.hasseDerivativeEval (a + 1) prior.yOrder prior.x prior.y
              (basis.getD idx 0) = 0 := by
          simpa [koetterDiscrepancy, hx] using hPrior idx hi
        have hlower :
            CBivariate.hasseDerivativeEval a prior.yOrder prior.x prior.y
              (basis.getD idx 0) = 0 :=
          hPriorLower idx hi a hx
        rw [hcur, hlower]
        simp
  · rw [if_neg hidx]
    by_cases hdelta : koetterDiscrepancy current (basis.getD idx 0) == 0
    · rw [if_pos hdelta]
      exact hPrior idx hi
    · rw [if_neg hdelta]
      rw [koetterDiscrepancy, CBivariate.hasseDerivativeEval_sub,
        CBivariate.hasseDerivativeEval_CC_mul]
      have hidxPrior :
          CBivariate.hasseDerivativeEval prior.xOrder prior.yOrder prior.x prior.y
            (basis.getD idx 0) = 0 := by
        simpa [koetterDiscrepancy] using hPrior idx hi
      have hpivotPrior :
          CBivariate.hasseDerivativeEval prior.xOrder prior.yOrder prior.x prior.y
            (basis.getD pivot.index 0) = 0 := by
        simpa [koetterDiscrepancy] using hPrior pivot.index hpivot
      rw [hidxPrior, hpivotPrior]
      simp

theorem foldl_setIfInBounds_size {α : Type*}
    (f : Nat → α) (xs : List Nat) (arr : Array α) :
    (xs.foldl (fun out idx ↦ out.setIfInBounds idx (f idx)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons idx xs ih =>
      simp [List.foldl_cons, ih, Array.size_setIfInBounds]

theorem foldl_range_setIfInBounds_getD_of_lt_aux {α : Type*}
    (f : Nat → α) (arr : Array α) (d : α) :
    ∀ n, n ≤ arr.size → ∀ idx, idx < n →
      ((List.range n).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).getD idx d =
        f idx := by
  intro n
  induction n with
  | zero =>
      intro _hle idx hi
      omega
  | succ n ih =>
      intro hle idx hi
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hidx : idx = n
      · subst idx
        have hprefixSize :
            ((List.range n).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).size =
              arr.size :=
          foldl_setIfInBounds_size f (List.range n) arr
        have hnlt : n <
            ((List.range n).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).size := by
          rw [hprefixSize]
          omega
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hnlt]
        rfl
      · have hnidx : n ≠ idx := fun h ↦ hidx h.symm
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hnidx]
        simpa [Array.getD_eq_getD_getElem?] using ih (by omega) idx (by omega)

theorem foldl_range_setIfInBounds_getD_of_lt {α : Type*}
    (f : Nat → α) (arr : Array α) (d : α) {idx : Nat} (hi : idx < arr.size) :
    ((List.range arr.size).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).getD idx d =
      f idx :=
  foldl_range_setIfInBounds_getD_of_lt_aux f arr d arr.size (by rfl) idx hi

theorem koetterUpdateBasis_size {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) :
    (koetterUpdateBasis constraint basis pivot).size = basis.size := by
  unfold koetterUpdateBasis
  exact foldl_setIfInBounds_size
    (fun idx ↦ koetterUpdatedEntry constraint basis pivot idx) (List.range basis.size) basis

theorem koetterProcessConstraint_size {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F) :
    (koetterProcessConstraint params constraint state).basis.size = state.basis.size := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      simp
  | some pivot =>
      simp [koetterUpdateBasis_size]

theorem koetterProcessConstraints_size {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraints : Array (InterpolationConstraint F))
    (state : KoetterState F) :
    (koetterProcessConstraints params constraints state).basis.size = state.basis.size := by
  unfold koetterProcessConstraints
  rw [← Array.foldl_toList]
  induction constraints.toList generalizing state with
  | nil =>
      simp
  | cons constraint rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact koetterProcessConstraint_size params constraint state

theorem koetterUpdateBasis_getD_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) {idx : Nat} (hi : idx < basis.size) :
    (koetterUpdateBasis constraint basis pivot).getD idx 0 =
      koetterUpdatedEntry constraint basis pivot idx := by
  unfold koetterUpdateBasis
  exact foldl_range_setIfInBounds_getD_of_lt
    (fun idx ↦ koetterUpdatedEntry constraint basis pivot idx) basis 0 hi

theorem koetterUpdateBasis_weakLeading {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (hBasis : koetterBasisWeakLeading params basis)
    (hpivot : koetterSelectPivot params constraint basis = some pivot) :
    koetterBasisWeakLeading params (koetterUpdateBasis constraint basis pivot) := by
  intro idx hi
  have hsize := koetterUpdateBasis_size constraint basis pivot
  have hiOld : idx < basis.size := by
    rw [hsize] at hi
    exact hi
  have hget :
      (koetterUpdateBasis constraint basis pivot).getD idx default =
        (koetterUpdateBasis constraint basis pivot).getD idx 0 := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget, koetterUpdateBasis_getD_of_lt constraint basis pivot hiOld]
  exact koetterUpdatedEntry_rowLeadingAt hBasis hpivot hiOld

theorem koetterProcessConstraint_weakLeading {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F)
    (hBasis : koetterBasisWeakLeading params state.basis) :
    koetterBasisWeakLeading params (koetterProcessConstraint params constraint state).basis := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      simpa using hBasis
  | some pivot =>
      simp
      exact koetterUpdateBasis_weakLeading hBasis hpivot

theorem koetterProcessConstraints_weakLeading {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraints : Array (InterpolationConstraint F))
    (state : KoetterState F)
    (hBasis : koetterBasisWeakLeading params state.basis) :
    koetterBasisWeakLeading params (koetterProcessConstraints params constraints state).basis := by
  unfold koetterProcessConstraints
  rw [← Array.foldl_toList]
  induction constraints.toList generalizing state with
  | nil =>
      simpa using hBasis
  | cons constraint _rest ih =>
      simp only [List.foldl_cons]
      exact ih (koetterProcessConstraint params constraint state)
        (koetterProcessConstraint_weakLeading params constraint state hBasis)

theorem koetterProcessConstraint_satisfies_current {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F)
    (hLower : ∀ pivot, koetterSelectPivot params constraint state.basis = some pivot →
      ∀ a, constraint.xOrder = a + 1 →
        CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
          (state.basis.getD pivot.index 0) = 0) :
    ∀ idx, idx < (koetterProcessConstraint params constraint state).basis.size →
      koetterDiscrepancy constraint
        ((koetterProcessConstraint params constraint state).basis.getD idx 0) = 0 := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      intro idx hi
      simp at hi ⊢
      simpa [Array.getD_eq_getD_getElem?] using
        koetterSelectPivot_none_discrepancy_zero hpivot idx hi
  | some pivot =>
      intro idx hi
      simp at hi ⊢
      have hsize := koetterUpdateBasis_size constraint state.basis pivot
      have hiOld : idx < state.basis.size := by
        simpa [hsize] using hi
      rw [← Array.getD_eq_getD_getElem?]
      rw [koetterUpdateBasis_getD_of_lt constraint state.basis pivot hiOld]
      rcases koetterSelectPivot_some_discrepancy hpivot with ⟨hdisc, hne⟩
      exact koetterUpdatedEntry_satisfies_current constraint state.basis pivot idx hdisc hne
        (hLower pivot hpivot)

theorem koetterProcessConstraint_preserves_prior {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (current prior : InterpolationConstraint F)
    (state : KoetterState F)
    (hPrior : ∀ idx, idx < state.basis.size →
      koetterDiscrepancy prior (state.basis.getD idx 0) = 0)
    (hPriorLower : ∀ idx, idx < state.basis.size → ∀ a, prior.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a prior.yOrder prior.x prior.y
        (state.basis.getD idx 0) = 0) :
    ∀ idx, idx < (koetterProcessConstraint params current state).basis.size →
      koetterDiscrepancy prior
        ((koetterProcessConstraint params current state).basis.getD idx 0) = 0 := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params current state.basis with
  | none =>
      intro idx hi
      simp at hi ⊢
      simpa [Array.getD_eq_getD_getElem?] using hPrior idx hi
  | some pivot =>
      intro idx hi
      simp at hi ⊢
      have hsize := koetterUpdateBasis_size current state.basis pivot
      have hiOld : idx < state.basis.size := by
        simpa [hsize] using hi
      rw [← Array.getD_eq_getD_getElem?]
      rw [koetterUpdateBasis_getD_of_lt current state.basis pivot hiOld]
      exact koetterUpdatedEntry_preserves_prior current prior state.basis pivot hiOld
        (koetterSelectPivot_some_index_lt hpivot) hPrior hPriorLower

end GuruswamiSudan

end CompPoly
