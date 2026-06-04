/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Dense Guruswami-Sudan Interpolation Correctness

Correctness contracts for the dense interpolation path and its constructive
low-message branch.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- The basis-parametric interpolation matrix is built with rectangular dense storage. -/
private theorem interpolationMatrixOnBasis_wf {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial)
    (points : Array (Prod F F)) (params : GSInterpParams) :
    DenseMatrix.WellFormed (interpolationMatrixOnBasis basis points params) := by
  simp [DenseMatrix.WellFormed, interpolationMatrixOnBasis,
    interpolationConstraintMatrixOnBasis, DenseMatrix.ofFn]

/-- The interpolation matrix is built with rectangular dense storage. -/
private theorem interpolationMatrix_wf {F : Type*} [Semiring F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    DenseMatrix.WellFormed (interpolationMatrix points params) := by
  exact interpolationMatrixOnBasis_wf (interpolationMonomials params) points params

private theorem interpolationMatrixOnBasis_rows {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial)
    (points : Array (Prod F F)) (params : GSInterpParams) :
    (interpolationMatrixOnBasis basis points params).rows =
      (interpolationConstraints points params.multiplicity).size := by
  rfl

private theorem interpolationMatrix_rows {F : Type*} [Semiring F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    (interpolationMatrix points params).rows =
      (interpolationConstraints points params.multiplicity).size := by
  rfl

private theorem interpolationMatrixOnBasis_cols {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial)
    (points : Array (Prod F F)) (params : GSInterpParams) :
    (interpolationMatrixOnBasis basis points params).cols = basis.size := by
  rfl

private theorem interpolationMatrix_cols {F : Type*} [Semiring F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    (interpolationMatrix points params).cols = (interpolationMonomials params).size := by
  rfl

private theorem firstNonzeroIndex?_some_lt_ne {F : Type*} [Zero F] [BEq F] [LawfulBEq F]
    {v : Array F} {i : Nat} (h : firstNonzeroIndex? v = some i) :
    i < v.size ∧ v.getD i 0 ≠ 0 := by
  unfold firstNonzeroIndex? at h
  rcases List.find?_eq_some_iff_append.mp h with ⟨hpred, _as, _bs, hlist, _⟩
  have himem : i ∈ List.range v.size := by
    rw [hlist]
    simp
  have hlt : i < v.size := List.mem_range.mp himem
  have hne : v.getD i 0 ≠ 0 := by
    intro hzero
    simp [hzero] at hpred
  exact And.intro hlt hne

private theorem map_div_getD_of_lt {F : Type*} [Div F] [Zero F]
    (a : F) {v : Array F} {i : Nat} (hi : i < v.size) :
    (v.map fun x ↦ x / a).getD i 0 = v.getD i 0 / a := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]

theorem normalizeVector?_some_data {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {v w : Array F} (h : normalizeVector? v = some w) :
    ∃ pivot, pivot < v.size ∧ v.getD pivot 0 ≠ 0 ∧
      w = v.map (fun x ↦ x / v.getD pivot 0) ∧
      w.size = v.size ∧ w.getD pivot 0 = 1 := by
  unfold normalizeVector? at h
  cases hpivot : firstNonzeroIndex? v with
  | none =>
      simp [hpivot] at h
  | some pivot =>
      simp [hpivot] at h
      rcases h with ⟨_hpivotNeOpt, hmap⟩
      have hpivotData := firstNonzeroIndex?_some_lt_ne (v := v) hpivot
      have hpivotGet : v[pivot]?.getD 0 = v.getD pivot 0 := by
        rw [Array.getD_eq_getD_getElem?]
      have hpivotGetElem : v[pivot]?.getD 0 = v[pivot] := by
        rw [Array.getElem?_eq_getElem hpivotData.1]
        rfl
      refine ⟨pivot, hpivotData.1, hpivotData.2, ?_, ?_, ?_⟩
      · rw [← hmap, hpivotGet]
      · rw [← hmap]
        simp
      · rw [← hmap, hpivotGet]
        rw [map_div_getD_of_lt (v.getD pivot 0) hpivotData.1]
        exact div_self hpivotData.2

private def interpolationConstraintsFold {F : Type*}
    (points : Array (Prod F F)) (multiplicity : Nat) :
    Array (InterpolationConstraint F) :=
  points.toList.foldl
    (fun constraints point ↦
      (List.range' 0 multiplicity).foldl
        (fun constraints a ↦
          (List.range' 0 (multiplicity - a)).foldl
            (fun constraints b ↦
              constraints.push
                ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
                  InterpolationConstraint F))
            constraints)
        constraints)
    #[]

private theorem interpolationConstraints_eq_fold {F : Type*}
    (points : Array (Prod F F)) (multiplicity : Nat) :
    interpolationConstraints points multiplicity =
      interpolationConstraintsFold points multiplicity := by
  unfold interpolationConstraints interpolationConstraintsFold
  simp

private theorem foldl_array_mem_preserve {α β : Type*} (step : Array β → α → Array β)
    (hstep : ∀ acc x {y : β}, y ∈ acc → y ∈ step acc x) :
    ∀ (xs : List α) (acc : Array β) {y : β}, y ∈ acc → y ∈ xs.foldl step acc
  | [], _acc, _y, hy => hy
  | x :: xs, acc, _y, hy =>
      foldl_array_mem_preserve step hstep xs (step acc x) (hstep acc x hy)

private theorem foldl_array_mem_of_mem_step {α β : Type*} (step : Array β → α → Array β)
    (hpres : ∀ acc x {y : β}, y ∈ acc → y ∈ step acc x)
    {target : α} {y : β}
    (hadd : ∀ acc, y ∈ step acc target) :
    ∀ (xs : List α) (acc : Array β), target ∈ xs → y ∈ xs.foldl step acc
  | [], _acc, hmem => by simp at hmem
  | x :: xs, acc, hmem => by
      simp at hmem
      cases hmem with
      | inl hx =>
          subst x
          exact foldl_array_mem_preserve step hpres xs (step acc target) (hadd acc)
      | inr hxs =>
          exact foldl_array_mem_of_mem_step step hpres hadd xs (step acc x) hxs

private theorem foldl_array_mem_valid {α β : Type*}
    (step : Array β → α → Array β) (valid : β → Prop) (prop : α → Prop)
    (hstep : ∀ acc x y, prop x → (∀ z, z ∈ acc.toList → valid z) →
      y ∈ (step acc x).toList → valid y) :
    ∀ (xs : List α) (acc : Array β) {y : β},
      (∀ x, x ∈ xs → prop x) →
        (∀ z, z ∈ acc.toList → valid z) →
          y ∈ (xs.foldl step acc).toList → valid y
  | [], acc, y, _hprop, hacc, hy => hacc y hy
  | x :: xs, acc, y, hprop, hacc, hy => by
      apply foldl_array_mem_valid step valid prop hstep xs (step acc x)
      · intro z hz
        exact hprop z (by simp [hz])
      · intro z hz
        exact hstep acc x z (hprop x (by simp)) hacc hz
      · exact hy

private theorem interpolationConstraint_mem_point_step {F : Type*}
    {multiplicity : Nat} {point : F × F} {a b : Nat} (hab : a + b < multiplicity)
    (out : Array (InterpolationConstraint F)) :
    ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
      InterpolationConstraint F) ∈
      List.foldl
        (fun out a' ↦
          (List.range' 0 (multiplicity - a')).foldl
            (fun out b' ↦
              out.push ({ x := point.1, y := point.2, xOrder := a', yOrder := b' } :
                InterpolationConstraint F))
            out)
        out (List.range' 0 multiplicity) := by
  refine foldl_array_mem_of_mem_step
    (step := fun out a' ↦
      (List.range' 0 (multiplicity - a')).foldl
        (fun out b' ↦
          out.push ({ x := point.1, y := point.2, xOrder := a', yOrder := b' } :
            InterpolationConstraint F))
        out)
    (target := a)
    (y := ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
      InterpolationConstraint F))
    ?hpresA ?haddA (List.range' 0 multiplicity) out ?ha
  · intro acc _a' _y hy
    exact foldl_array_mem_preserve _ (by
      intro acc _b' _y hy
      exact Array.mem_push_of_mem _ hy) _ acc hy
  · intro acc
    refine foldl_array_mem_of_mem_step
      (step := fun out b' ↦
        out.push ({ x := point.1, y := point.2, xOrder := a, yOrder := b' } :
          InterpolationConstraint F))
      (target := b)
      (y := ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
        InterpolationConstraint F))
      ?hpresB ?haddB (List.range' 0 (multiplicity - a)) acc ?hb
    · intro acc _b' _y hy
      exact Array.mem_push_of_mem _ hy
    · intro acc
      exact Array.mem_push_self
    · simpa [List.mem_range'] using
        (show 0 ≤ b ∧ b < 0 + (multiplicity - a) by omega)
  · simpa [List.mem_range'] using
      (show 0 ≤ a ∧ a < 0 + multiplicity by omega)

private theorem interpolationConstraints_mem {F : Type*} {points : Array (F × F)}
    {multiplicity : Nat} {point : F × F} (hpoint : point ∈ points.toList)
    {a b : Nat} (hab : a + b < multiplicity) :
    ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
      InterpolationConstraint F) ∈ (interpolationConstraints points multiplicity).toList := by
  rw [interpolationConstraints_eq_fold]
  unfold interpolationConstraintsFold
  apply Array.mem_toList_iff.mpr
  refine foldl_array_mem_of_mem_step
    (step := fun constraints point ↦
      (List.range' 0 multiplicity).foldl
        (fun constraints a ↦
          (List.range' 0 (multiplicity - a)).foldl
            (fun constraints b ↦
              constraints.push ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
                InterpolationConstraint F))
            constraints)
        constraints)
    (target := point)
    (y := ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
      InterpolationConstraint F))
    ?hpres ?hadd points.toList #[] ?hpoint
  · intro acc _point _y hy
    exact foldl_array_mem_preserve _ (by
      intro acc _a _y hy
      exact foldl_array_mem_preserve _ (by
        intro acc _b _y hy
        exact Array.mem_push_of_mem _ hy) _ acc hy) _ acc hy
  · intro acc
    exact interpolationConstraint_mem_point_step (multiplicity := multiplicity)
      (point := point) hab acc
  · exact hpoint

private theorem interpolationConstraints_mem_valid {F : Type*} [DecidableEq F]
    {points : Array (F × F)} {multiplicity : Nat}
    {constraint : InterpolationConstraint F}
    (hmem : constraint ∈ (interpolationConstraints points multiplicity).toList) :
    (constraint.x, constraint.y) ∈ points.toList ∧
      constraint.xOrder + constraint.yOrder < multiplicity := by
  rw [interpolationConstraints_eq_fold] at hmem
  unfold interpolationConstraintsFold at hmem
  let valid : InterpolationConstraint F → Prop := fun constraint ↦
    (constraint.x, constraint.y) ∈ points.toList ∧
      constraint.xOrder + constraint.yOrder < multiplicity
  change valid constraint
  refine foldl_array_mem_valid
    (step := fun constraints point ↦
      (List.range' 0 multiplicity).foldl
        (fun constraints a ↦
          (List.range' 0 (multiplicity - a)).foldl
            (fun constraints b ↦
              constraints.push ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
                InterpolationConstraint F))
            constraints)
        constraints)
    (valid := valid)
    (prop := fun point ↦ point ∈ points.toList)
    ?hstepPoint points.toList #[] ?hpropPoints ?hvalidEmpty hmem
  · intro constraints point candidate hpoint hconstraints hcandidate
    refine foldl_array_mem_valid
      (step := fun constraints a ↦
        (List.range' 0 (multiplicity - a)).foldl
          (fun constraints b ↦
            constraints.push ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
              InterpolationConstraint F))
          constraints)
      (valid := valid)
      (prop := fun a ↦ a < multiplicity)
      ?hstepA (List.range' 0 multiplicity) constraints ?hpropA hconstraints
      hcandidate
    · intro constraints a candidate ha hconstraints hcandidate
      refine foldl_array_mem_valid
        (step := fun constraints b ↦
          constraints.push ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
            InterpolationConstraint F))
        (valid := valid)
        (prop := fun b ↦ b < multiplicity - a)
        ?hstepB (List.range' 0 (multiplicity - a)) constraints ?hpropB
        hconstraints hcandidate
      · intro constraints b candidate hb hconstraints hcandidate
        simp at hcandidate
        cases hcandidate with
        | inl hprev =>
            exact hconstraints candidate (Array.mem_def.mp hprev)
        | inr hnew =>
            subst candidate
            constructor
            · exact hpoint
            · change a + b < multiplicity
              omega
      · intro b hb
        simpa [List.mem_range'] using (show 0 ≤ b ∧ b < 0 + (multiplicity - a) by
          exact (List.mem_range'_1.mp hb))
    · intro a ha
      simpa [List.mem_range'] using (show 0 ≤ a ∧ a < 0 + multiplicity by
        exact (List.mem_range'_1.mp ha))
  · intro point hpoint
    exact hpoint
  · intro candidate hcandidate
    simp at hcandidate

private theorem interpolationMatrixOnBasis_get {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial)
    (points : Array (F × F)) (params : GSInterpParams)
    {row col : Nat} (hrow : row < (interpolationMatrixOnBasis basis points params).rows)
    (hcol : col < (interpolationMatrixOnBasis basis points params).cols) :
    (interpolationMatrixOnBasis basis points params).get row col =
      hasseMonomialEval (basis.getD col ⟨0, 0⟩)
        ((interpolationConstraints points params.multiplicity).getD row
          ⟨0, 0, 0, 0⟩) := by
  have hrow' : row < (interpolationConstraints points params.multiplicity).size := by
    simpa using hrow
  have hcol' : col < basis.size := by
    simpa using hcol
  unfold interpolationMatrixOnBasis interpolationConstraintMatrixOnBasis
  rw [DenseMatrix.get_ofFn _ _ _ hrow' hcol']

private theorem interpolationMatrix_get {F : Type*} [Semiring F]
    (points : Array (F × F)) (params : GSInterpParams)
    {row col : Nat} (hrow : row < (interpolationMatrix points params).rows)
    (hcol : col < (interpolationMatrix points params).cols) :
    (interpolationMatrix points params).get row col =
      hasseMonomialEval ((interpolationMonomials params).getD col ⟨0, 0⟩)
        ((interpolationConstraints points params.multiplicity).getD row
          ⟨0, 0, 0, 0⟩) := by
  exact interpolationMatrixOnBasis_get (interpolationMonomials params) points params hrow hcol

private theorem array_mem_getD {α : Type*} {xs : Array α} {x default : α}
    (h : x ∈ xs.toList) : ∃ i, i < xs.size ∧ xs.getD i default = x := by
  rcases List.getElem_of_mem h with ⟨i, hi, hget⟩
  refine ⟨i, ?_, ?_⟩
  · simpa using hi
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]
    simpa [Array.getElem_toList] using hget

private theorem interpolationMatrixOnBasis_dotRow {F : Type*} [Semiring F]
    (basis : Array CBivariate.Monomial)
    (points : Array (F × F)) (params : GSInterpParams) (coeffs : Array F)
    {row : Nat} (hrow : row < (interpolationMatrixOnBasis basis points params).rows) :
    (interpolationMatrixOnBasis basis points params).dotRow row coeffs =
      (List.range' 0 basis.size).foldl
        (fun acc col ↦
          acc +
            hasseMonomialEval (basis.getD col ⟨0, 0⟩)
              ((interpolationConstraints points params.multiplicity).getD row
                ⟨0, 0, 0, 0⟩) *
              coeffs.getD col 0)
        0 := by
  unfold DenseMatrix.dotRow
  simp only [interpolationMatrixOnBasis_cols]
  rw [List.range_eq_range']
  have hfold : ∀ (xs : List Nat) (acc : F),
      (∀ col, col ∈ xs → col < basis.size) →
      xs.foldl
          (fun acc col ↦
            acc + (interpolationMatrixOnBasis basis points params).get row col *
              coeffs.getD col 0)
          acc =
        xs.foldl
          (fun acc col ↦
            acc +
              hasseMonomialEval (basis.getD col ⟨0, 0⟩)
                ((interpolationConstraints points params.multiplicity).getD row
                  ⟨0, 0, 0, 0⟩) *
                coeffs.getD col 0)
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        rfl
    | cons col xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        have hcol : col < basis.size := hxs col (by simp)
        rw [interpolationMatrixOnBasis_get basis points params hrow (by simpa using hcol)]
        apply ih
        intro c hc
        exact hxs c (by simp [hc])
  apply hfold
  intro col hcol
  simpa using (List.mem_range'_1.mp hcol).2

private theorem interpolationMatrix_dotRow {F : Type*} [Semiring F]
    (points : Array (F × F)) (params : GSInterpParams) (coeffs : Array F)
    {row : Nat} (hrow : row < (interpolationMatrix points params).rows) :
    (interpolationMatrix points params).dotRow row coeffs =
      (List.range' 0 (interpolationMonomials params).size).foldl
        (fun acc col ↦
          acc +
            hasseMonomialEval ((interpolationMonomials params).getD col ⟨0, 0⟩)
              ((interpolationConstraints points params.multiplicity).getD row
                ⟨0, 0, 0, 0⟩) *
              coeffs.getD col 0)
        0 := by
  exact interpolationMatrixOnBasis_dotRow (interpolationMonomials params)
    points params coeffs hrow

private theorem hasseDerivativeEval_monomialXY_eq_hasseMonomialEval {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (monomial : CBivariate.Monomial) (constraint : InterpolationConstraint F) (c : F) :
    CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x constraint.y
        (CBivariate.monomialXY monomial.xDegree monomial.yDegree c) =
      hasseMonomialEval monomial constraint * c := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [CBivariate.hasseDerivative_monomialXY]
  unfold hasseMonomialEval
  by_cases hle : constraint.xOrder ≤ monomial.xDegree ∧
      constraint.yOrder ≤ monomial.yDegree
  · rw [if_pos hle]
    have hbool : (decide (constraint.xOrder ≤ monomial.xDegree) &&
        decide (constraint.yOrder ≤ monomial.yDegree)) = true := by
      simp [hle.1, hle.2]
    rw [if_pos hbool]
    rw [CBivariate.evalEval_monomialXY]
    ring
  · rw [if_neg hle]
    have hbool : ¬ ((decide (constraint.xOrder ≤ monomial.xDegree) &&
        decide (constraint.yOrder ≤ monomial.yDegree)) = true) := by
      intro htrue
      rcases Bool.and_eq_true_iff.mp htrue with ⟨hx, hy⟩
      exact hle ⟨of_decide_eq_true hx, of_decide_eq_true hy⟩
    rw [if_neg hbool]
    rw [CBivariate.evalEval_zero]
    simp

private theorem hasseDerivativeEval_ofMonomialCoeffs {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (monomials : Array CBivariate.Monomial) (coeffs : Array F)
    (constraint : InterpolationConstraint F) :
    CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x constraint.y
        (CBivariate.ofMonomialCoeffs monomials coeffs) =
      (List.range' 0 monomials.size).foldl
        (fun acc col ↦
          acc + hasseMonomialEval (monomials.getD col ⟨0, 0⟩) constraint *
            coeffs.getD col 0)
        0 := by
  unfold CBivariate.ofMonomialCoeffs
  have hfold : ∀ (xs : List Nat) (out : CBivariate F) (acc : F),
      CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
        constraint.y out = acc →
      CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
          constraint.y
          (xs.foldl
            (fun out col ↦
              let monomial := monomials.getD col ⟨0, 0⟩
              out + CBivariate.monomialXY monomial.xDegree monomial.yDegree
                (coeffs.getD col 0))
            out) =
        xs.foldl
          (fun acc col ↦
            acc + hasseMonomialEval (monomials.getD col ⟨0, 0⟩) constraint *
              coeffs.getD col 0)
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro out acc hout
        exact hout
    | cons col xs ih =>
        intro out acc hout
        simp only [List.foldl_cons]
        apply ih
        rw [CBivariate.hasseDerivativeEval_add, hout,
          hasseDerivativeEval_monomialXY_eq_hasseMonomialEval]
  exact hfold (List.range' 0 monomials.size) 0 0
    (CBivariate.hasseDerivativeEval_zero constraint.xOrder constraint.yOrder constraint.x
      constraint.y)

theorem interpolationPolynomialOnBasis_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array CBivariate.Monomial) (params : GSInterpParams) (coeffs : Array F)
    (hbound : ∀ monomial, monomial ∈ basis.toList →
      1 * monomial.xDegree + yWeight params * monomial.yDegree ≤
        params.weightedDegreeBound) :
    CBivariate.natWeightedDegree (interpolationPolynomialOnBasis basis coeffs)
      1 (yWeight params) ≤ params.weightedDegreeBound := by
  unfold interpolationPolynomialOnBasis
  apply CBivariate.ofMonomialCoeffs_natWeightedDegree_le
  exact hbound

theorem interpolationPolynomial_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (coeffs : Array F) :
    CBivariate.natWeightedDegree (interpolationPolynomial params coeffs)
      1 (yWeight params) ≤ params.weightedDegreeBound := by
  apply interpolationPolynomialOnBasis_weightedDegree_le
  intro monomial hmonomial
  simpa [interpolationMonomials] using CBivariate.monomialsWeightedDegreeLE_sound
    (xWeight := 1) (yWeight := yWeight params)
    (bound := params.weightedDegreeBound) hmonomial

private theorem dotRow_map_div {F : Type*} [Field F]
    (M : DenseMatrix F) (row : Nat) (v : Array F) (a : F) :
    DenseMatrix.dotRow M row (v.map fun x ↦ x / a) =
      DenseMatrix.dotRow M row v / a := by
  unfold DenseMatrix.dotRow
  have hfold : ∀ (xs : List Nat) (accL accR : F),
      accL = accR / a →
      xs.foldl
          (fun acc col ↦ acc + M.get row col * (v.map fun x ↦ x / a).getD col 0)
          accL =
        xs.foldl (fun acc col ↦ acc + M.get row col * v.getD col 0) accR / a := by
    intro xs
    induction xs with
    | nil =>
        intro accL accR hacc
        exact hacc
    | cons col xs ih =>
        intro accL accR hacc
        simp only [List.foldl_cons]
        apply ih
        rw [hacc]
        by_cases hcol : col < v.size
        · simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hcol]
          ring
        · have hle : v.size ≤ col := Nat.le_of_not_lt hcol
          simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
  simpa using hfold (List.range M.cols) 0 0 (by simp)

theorem isHomogeneousSolution_map_div {F : Type*} [Field F]
    {M : DenseMatrix F} {v : Array F} (a : F)
    (hsol : DenseMatrix.IsHomogeneousSolution M v) :
    DenseMatrix.IsHomogeneousSolution M (v.map fun x ↦ x / a) := by
  intro row hrow
  rw [dotRow_map_div]
  rw [hsol row hrow]
  simp

theorem interpolationPolynomialOnBasis_satisfies_of_solution {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {basis : Array CBivariate.Monomial}
    {points : Array (F × F)} {params : GSInterpParams} {coeffs : Array F}
    (hsol :
      DenseMatrix.IsHomogeneousSolution (interpolationMatrixOnBasis basis points params) coeffs) :
    CBivariate.SatisfiesMultiplicityConstraints
      (interpolationPolynomialOnBasis basis coeffs) points params.multiplicity := by
  intro point hpoint a b hab
  let constraint : InterpolationConstraint F :=
    { x := point.1, y := point.2, xOrder := a, yOrder := b }
  have hmem := interpolationConstraints_mem (points := points) (point := point)
    hpoint (a := a) (b := b) hab
  rcases array_mem_getD (xs := interpolationConstraints points params.multiplicity)
      (x := constraint) (default := ⟨0, 0, 0, 0⟩) hmem with ⟨row, hrow, hget⟩
  have hrowM : row < (interpolationMatrixOnBasis basis points params).rows := by
    simpa using hrow
  have hdot := hsol row hrowM
  rw [interpolationMatrixOnBasis_dotRow basis points params coeffs hrowM] at hdot
  change CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
      constraint.y (interpolationPolynomialOnBasis basis coeffs) = 0
  unfold interpolationPolynomialOnBasis
  rw [hasseDerivativeEval_ofMonomialCoeffs basis coeffs constraint]
  simpa [constraint, hget] using hdot

theorem interpolationPolynomial_satisfies_of_solution {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {coeffs : Array F}
    (hsol : DenseMatrix.IsHomogeneousSolution (interpolationMatrix points params) coeffs) :
    CBivariate.SatisfiesMultiplicityConstraints
      (interpolationPolynomial params coeffs) points params.multiplicity := by
  exact interpolationPolynomialOnBasis_satisfies_of_solution
    (basis := interpolationMonomials params) hsol

theorem interpolationCoefficientVectorOnBasis_getD_of_lt {F : Type*} [Zero F]
    (basis : Array CBivariate.Monomial) (Q : CBivariate F) {k : Nat}
    (hk : k < basis.size) :
    (interpolationCoefficientVectorOnBasis basis Q).getD k 0 =
      CBivariate.coeff Q (basis.getD k ⟨0, 0⟩).xDegree
        (basis.getD k ⟨0, 0⟩).yDegree := by
  unfold interpolationCoefficientVectorOnBasis
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]

theorem interpolationCoefficientVectorOnBasis_size {F : Type*} [Zero F]
    (basis : Array CBivariate.Monomial) (Q : CBivariate F) :
    (interpolationCoefficientVectorOnBasis basis Q).size = basis.size := by
  unfold interpolationCoefficientVectorOnBasis
  simp

theorem cbivariate_ne_zero_exists_coeff_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (hQ : Q ≠ 0) :
    ∃ i j, CBivariate.coeff Q i j ≠ 0 := by
  by_contra hnot
  apply hQ
  apply (CBivariate.eq_iff_coeff).mpr
  intro i j
  rw [CBivariate.coeff_zero]
  by_contra hcoeff
  exact hnot ⟨i, j, hcoeff⟩

theorem interpolationCoefficientVectorOnBasis_nonzero_of_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {basis : Array CBivariate.Monomial} {Q : CBivariate F}
    (hQ : Q ≠ 0)
    (hcomplete : ∀ i j, CBivariate.coeff Q i j ≠ 0 →
      ({ xDegree := i, yDegree := j } : CBivariate.Monomial) ∈ basis.toList) :
    DenseMatrix.NonzeroVector (interpolationCoefficientVectorOnBasis basis Q) := by
  rcases cbivariate_ne_zero_exists_coeff_ne_zero hQ with ⟨i, j, hcoeff⟩
  rcases array_mem_getD (xs := basis)
      (x := ({ xDegree := i, yDegree := j } : CBivariate.Monomial))
      (default := ⟨0, 0⟩) (hcomplete i j hcoeff) with
    ⟨k, hk, hget⟩
  refine ⟨k, ?_, ?_⟩
  · rw [interpolationCoefficientVectorOnBasis_size]
    exact hk
  · rw [interpolationCoefficientVectorOnBasis_getD_of_lt basis Q hk, hget]
    exact hcoeff

theorem interpolationPolynomialOnBasis_eq_of_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {basis : Array CBivariate.Monomial} {Q : CBivariate F}
    (hnodup : basis.toList.Nodup)
    (hcomplete : ∀ i j, CBivariate.coeff Q i j ≠ 0 →
      ({ xDegree := i, yDegree := j } : CBivariate.Monomial) ∈ basis.toList) :
    interpolationPolynomialOnBasis basis
        (interpolationCoefficientVectorOnBasis basis Q) = Q := by
  apply (CBivariate.eq_iff_coeff).mpr
  intro i j
  unfold interpolationPolynomialOnBasis
  by_cases hcoeff : CBivariate.coeff Q i j = 0
  · rw [CBivariate.ofMonomialCoeffs_coeff, hcoeff]
    apply DenseMatrix.foldl_range_eq_zero_of_zero
    intro col hcol
    let monomial := basis.getD col ⟨0, 0⟩
    have hvec :
        (interpolationCoefficientVectorOnBasis basis Q).getD col 0 =
          CBivariate.coeff Q monomial.xDegree monomial.yDegree := by
      exact interpolationCoefficientVectorOnBasis_getD_of_lt basis Q hcol
    by_cases hmatch : i = monomial.xDegree ∧ j = monomial.yDegree
    · change
        (if i = monomial.xDegree ∧ j = monomial.yDegree then
            (interpolationCoefficientVectorOnBasis basis Q).getD col 0
          else 0) = 0
      rw [if_pos hmatch, hvec]
      rcases hmatch with ⟨hi, hj⟩
      simpa [hi, hj] using hcoeff
    · change
        (if i = monomial.xDegree ∧ j = monomial.yDegree then
            (interpolationCoefficientVectorOnBasis basis Q).getD col 0
          else 0) = 0
      rw [if_neg hmatch]
  · rcases array_mem_getD (xs := basis)
        (x := ({ xDegree := i, yDegree := j } : CBivariate.Monomial))
        (default := ⟨0, 0⟩) (hcomplete i j hcoeff) with
      ⟨k, hk, hget⟩
    have hgetCoeff := CBivariate.ofMonomialCoeffs_coeff_getD
      (R := F) (monomials := basis)
      (coeffs := interpolationCoefficientVectorOnBasis basis Q) hnodup hk
    rw [hget] at hgetCoeff
    rw [hgetCoeff]
    rw [interpolationCoefficientVectorOnBasis_getD_of_lt basis Q hk, hget]

theorem interpolationCoefficientVectorOnBasis_solution_of_satisfies {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {basis : Array CBivariate.Monomial}
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hpoly :
      interpolationPolynomialOnBasis basis
        (interpolationCoefficientVectorOnBasis basis Q) = Q)
    (hconstraints :
      CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity) :
    DenseMatrix.IsHomogeneousSolution (interpolationMatrixOnBasis basis points params)
      (interpolationCoefficientVectorOnBasis basis Q) := by
  intro row hrow
  have hrowConstraints : row < (interpolationConstraints points params.multiplicity).size := by
    simpa [interpolationMatrixOnBasis_rows] using hrow
  let constraint :=
    (interpolationConstraints points params.multiplicity).getD row ⟨0, 0, 0, 0⟩
  have hconstraintMem :
      constraint ∈ (interpolationConstraints points params.multiplicity).toList := by
    unfold constraint
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hrowConstraints]
    exact Array.mem_def.mp
      (Array.getElem_mem (xs := interpolationConstraints points params.multiplicity)
        hrowConstraints)
  have hvalid := interpolationConstraints_mem_valid
    (points := points) (multiplicity := params.multiplicity)
    (constraint := constraint) hconstraintMem
  have hdot :=
    interpolationMatrixOnBasis_dotRow basis points params
      (interpolationCoefficientVectorOnBasis basis Q) hrow
  rw [hdot]
  have hderiv :
      CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder
          constraint.x constraint.y
          (interpolationPolynomialOnBasis basis
            (interpolationCoefficientVectorOnBasis basis Q)) = 0 := by
    rw [hpoly]
    exact hconstraints (constraint.x, constraint.y) hvalid.1
      constraint.xOrder constraint.yOrder hvalid.2
  unfold interpolationPolynomialOnBasis at hderiv
  rw [hasseDerivativeEval_ofMonomialCoeffs basis
      (interpolationCoefficientVectorOnBasis basis Q) constraint] at hderiv
  simpa [constraint] using hderiv

theorem normalizeVector?_some_of_nonzero {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {v : Array F} (hnz : DenseMatrix.NonzeroVector v) :
    ∃ norm, normalizeVector? v = some norm := by
  unfold normalizeVector?
  cases hfirst : firstNonzeroIndex? v with
  | some pivot =>
      have hpivot := firstNonzeroIndex?_some_lt_ne (v := v) hfirst
      refine ⟨v.map (fun c ↦ c / v.getD pivot 0), ?_⟩
      have hbeq : (v.getD pivot 0 == 0) = false :=
        beq_eq_false_iff_ne.mpr hpivot.2
      simp only
      rw [hbeq]
      rfl
  | none =>
      exfalso
      rcases hnz with ⟨i, hi, hne⟩
      unfold firstNonzeroIndex? at hfirst
      have hnone := (List.find?_eq_none.mp hfirst) i (List.mem_range.mpr hi)
      have hpred : (!v.getD i 0 == 0) = true := by
        have hbeq : (v.getD i 0 == 0) = false := by
          exact beq_eq_false_iff_ne.mpr hne
        rw [hbeq]
        rfl
      exact hnone hpred

/-- Soundness of the weighted-degree basis used by the public GS interpolation path. -/
theorem weightedDegreeBasis_sound (params : GSInterpParams) :
    ∀ monomial, monomial ∈ (interpolationMonomials params).toList →
      1 * monomial.xDegree + yWeight params * monomial.yDegree ≤
        params.weightedDegreeBound := by
  intro monomial hmonomial
  simpa [interpolationMonomials] using CBivariate.monomialsWeightedDegreeLE_sound
    (xWeight := 1) (yWeight := yWeight params)
    (bound := params.weightedDegreeBound) hmonomial

/-- Soundness for one returned basis-parametric dense witness. -/
theorem denseInterpolateWithBasis_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelContext : LinearKernelContext F}
    {basis : Array CBivariate.Monomial}
    {points : Array (Prod F F)} {params : GSInterpParams} {Q : CBivariate F}
    (hbasis : basis.toList.Nodup)
    (h : denseInterpolateWithBasisAndKernel kernelContext basis points params = some Q) :
    Q ≠ 0 ∧
      (∃ coeffs, Q = interpolationPolynomialOnBasis basis coeffs) ∧
        CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity := by
  unfold denseInterpolateWithBasisAndKernel at h
  set matrix := interpolationMatrixOnBasis basis points params
  change (normalizeInterpolationPolynomialOnBasis? basis =<<
    kernelContext.homogeneousWitness matrix) = some Q at h
  cases hw : kernelContext.homogeneousWitness matrix with
  | none =>
      rw [hw] at h
      contradiction
  | some coeffs =>
      rw [hw] at h
      change normalizeInterpolationPolynomialOnBasis? basis coeffs = some Q at h
      unfold normalizeInterpolationPolynomialOnBasis? at h
      cases hn : normalizeVector? coeffs with
      | none =>
          rw [hn] at h
          contradiction
      | some norm =>
          rw [hn] at h
          cases h
          have hwidth : DenseMatrix.VectorWidth matrix coeffs :=
            kernelContext.witness_width hw
          have hsol : DenseMatrix.IsHomogeneousSolution matrix coeffs :=
            kernelContext.witness_sound
              (by simpa [matrix] using interpolationMatrixOnBasis_wf basis points params) hw
          rcases normalizeVector?_some_data hn with
            ⟨pivot, hpivot, _hpivot_ne, hnorm, _hnorm_width, hnorm_one⟩
          have hpivotBasis : pivot < basis.size := by
            have hpivotCols : pivot < matrix.cols := by
              rw [← hwidth]
              exact hpivot
            simpa [matrix, interpolationMatrixOnBasis_cols] using hpivotCols
          refine ⟨?_, ⟨norm, rfl⟩, ?_⟩
          · apply CBivariate.ofMonomialCoeffs_ne_zero_of_coeff_getD_ne_zero
            · exact hbasis
            · exact hpivotBasis
            · rw [hnorm_one]
              exact one_ne_zero
          · apply interpolationPolynomialOnBasis_satisfies_of_solution
            rw [hnorm]
            exact isHomogeneousSolution_map_div (coeffs.getD pivot 0)
              (by simpa [matrix] using hsol)

/-- Basis-parametric dense completeness for finite homogeneous systems. -/
theorem denseInterpolateWithBasis_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelContext : LinearKernelContext F}
    {basis : Array CBivariate.Monomial}
    {points : Array (Prod F F)} {params : GSInterpParams}
    (hExists : ∃ coeffs,
      DenseMatrix.VectorWidth (interpolationMatrixOnBasis basis points params) coeffs ∧
        DenseMatrix.IsHomogeneousSolution (interpolationMatrixOnBasis basis points params)
          coeffs ∧
          DenseMatrix.NonzeroVector coeffs) :
    ∃ Q, denseInterpolateWithBasisAndKernel kernelContext basis points params = some Q := by
  unfold denseInterpolateWithBasisAndKernel
  set matrix := interpolationMatrixOnBasis basis points params
  cases hw : kernelContext.homogeneousWitness matrix with
  | none =>
      exfalso
      rcases hExists with ⟨coeffs, hwidth, hsolution, hnonzero⟩
      exact kernelContext.witness_complete
        (by simpa [matrix] using interpolationMatrixOnBasis_wf basis points params)
        hw coeffs (by simpa [matrix] using hwidth)
        (by simpa [matrix] using hsolution) hnonzero
  | some coeffs =>
      have hnz := kernelContext.witness_nonzero hw
      rcases normalizeVector?_some_of_nonzero hnz with ⟨norm, hnorm⟩
      refine ⟨interpolationPolynomialOnBasis basis norm, ?_⟩
      change (normalizeInterpolationPolynomialOnBasis? basis =<<
        kernelContext.homogeneousWitness matrix) =
          some (interpolationPolynomialOnBasis basis norm)
      rw [hw]
      change normalizeInterpolationPolynomialOnBasis? basis coeffs =
        some (interpolationPolynomialOnBasis basis norm)
      unfold normalizeInterpolationPolynomialOnBasis?
      rw [hnorm]

/-- Basis-parametric dense soundness specialized to a bounded basis. -/
theorem denseInterpolateWithBasisAndKernel_sound_of_bounded_basis {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelContext : LinearKernelContext F}
    {basis : Array CBivariate.Monomial}
    {points : Array (Prod F F)} {params : GSInterpParams} {Q : CBivariate F}
    (hbasis : basis.toList.Nodup)
    (hbound : ∀ monomial, monomial ∈ basis.toList →
      1 * monomial.xDegree + yWeight params * monomial.yDegree ≤
        params.weightedDegreeBound)
    (h : denseInterpolateWithBasisAndKernel kernelContext basis points params = some Q) :
    ValidInterpolationWitness points params Q := by
  rcases denseInterpolateWithBasis_sound (kernelContext := kernelContext)
      (basis := basis) (points := points) (params := params) hbasis h with
    ⟨hQne, ⟨coeffs, hQcoeffs⟩, hconstraints⟩
  refine ⟨hQne, ?_, ?_⟩
  · rw [hQcoeffs]
    exact interpolationPolynomialOnBasis_weightedDegree_le basis params coeffs hbound
  · exact (CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity Q points
      params.multiplicity).1 hconstraints

/-- Dense weighted-degree-basis soundness for the positive-message branch. -/
theorem denseInterpolateWithWeightedDegreeBasis_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelContext : LinearKernelContext F}
    {points : Array (Prod F F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : denseInterpolateWithBasisAndKernel kernelContext
      (interpolationMonomials params) points params = some Q) :
    ValidInterpolationWitness points params Q := by
  exact denseInterpolateWithBasisAndKernel_sound_of_bounded_basis
    (kernelContext := kernelContext) (basis := interpolationMonomials params)
    (points := points) (params := params)
    (CBivariate.monomialsWeightedDegreeLE_nodup 1 (yWeight params)
      params.weightedDegreeBound)
    (weightedDegreeBasis_sound params) h

/-- Soundness for one returned public interpolation witness. -/
theorem denseInterpolate_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelContext : LinearKernelContext F}
    {points : Array (Prod F F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : denseInterpolateWithKernel kernelContext points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold denseInterpolateWithKernel at h
  by_cases hLow : params.messageDegree ≤ 1
  · simp [hLow] at h
    cases h
    simpa using lowMessageDegreeInterpolation_sound (points := points)
      (params := params) hLow
  · simp [hLow] at h
    exact denseInterpolateWithWeightedDegreeBasis_sound
      (kernelContext := kernelContext) h

/-- If a basis-parametric dense interpolation matrix has more columns than rows,
the dense solver finds a nonzero homogeneous witness. -/
theorem denseInterpolateWithBasis_exists_of_dimension_slack {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array CBivariate.Monomial)
    (points : Array (F × F)) (params : GSInterpParams)
    (hSlack : HasInterpolationDimensionSlackOnBasis basis points params) :
    ∃ Q, denseInterpolateWithBasisAndKernel (denseLinearKernelContext F)
      basis points params = some Q := by
  unfold denseInterpolateWithBasisAndKernel
  rcases DenseMatrix.homogeneousWitness_exists_of_rows_lt_cols
      (interpolationMatrixOnBasis basis points params)
      (by
        simpa [HasInterpolationDimensionSlackOnBasis, interpolationMatrixOnBasis_rows,
          interpolationMatrixOnBasis_cols] using hSlack) with
    ⟨coeffs, hw⟩
  have hnz := DenseMatrix.homogeneousWitness_nonzero hw
  rcases normalizeVector?_some_of_nonzero hnz with ⟨norm, hn⟩
  refine ⟨interpolationPolynomialOnBasis basis norm, ?_⟩
  simp [denseLinearKernelContext, hw]
  change normalizeInterpolationPolynomialOnBasis? basis coeffs =
    some (interpolationPolynomialOnBasis basis norm)
  unfold normalizeInterpolationPolynomialOnBasis?
  rw [hn]

/-- Dimension slack for the public interpolation basis gives an interpolation
witness. The low-message branch is constructive; otherwise the witness comes
from the dense matrix. -/
theorem denseInterpolate_exists_of_dimension_slack {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams)
    (hSlack : HasInterpolationDimensionSlack points params) :
    ∃ Q, denseInterpolate points params = some Q := by
  unfold denseInterpolate denseInterpolateWithKernel
  by_cases hLow : params.messageDegree ≤ 1
  · refine ⟨lowMessageDegreeInterpolation points params.multiplicity, ?_⟩
    simp [hLow]
  · simp [hLow]
    exact denseInterpolateWithBasis_exists_of_dimension_slack
      (basis := interpolationMonomials params) points params hSlack

private theorem cpoly_index_le_natDegree_of_coeff_ne_zero {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {i : Nat} (hcoeff : p.coeff i ≠ 0) :
    i ≤ p.natDegree := by
  have hmem : i ∈ p.support := (CPolynomial.mem_support_iff p i).mpr hcoeff
  rw [CPolynomial.natDegree_eq_support_sup]
  exact Finset.le_sup (f := fun n ↦ n) hmem

/-- When `messageDegree > 1`, the weighted-degree basis is complete for the
semantic weighted-degree predicate. -/
theorem weightedDegreeBasis_complete_of_messageDegree_gt_one {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F]
    {params : GSInterpParams} (hHigh : ¬ params.messageDegree ≤ 1)
    {Q : CBivariate F}
    (hdeg :
      CBivariate.natWeightedDegree Q 1 (yWeight params) ≤
        params.weightedDegreeBound) :
    ∀ i j, CBivariate.coeff Q i j ≠ 0 →
      ({ xDegree := i, yDegree := j } : CBivariate.Monomial) ∈
        (interpolationMonomials params).toList := by
  intro i j hcoeff
  have hypos : 0 < yWeight params := by
    unfold yWeight
    omega
  have hcoeffY : Q.val.coeff j ≠ 0 := by
    intro hzero
    unfold CBivariate.coeff at hcoeff
    rw [hzero, CPolynomial.coeff_zero] at hcoeff
    exact hcoeff rfl
  have hjmem : j ∈ CPolynomial.support Q := (CPolynomial.mem_support_iff Q j).mpr hcoeffY
  have hterm :
      1 * (Q.val.coeff j).natDegree + yWeight params * j ≤
        CBivariate.natWeightedDegree Q 1 (yWeight params) := by
    unfold CBivariate.natWeightedDegree
    exact Finset.le_sup
      (f := fun m ↦ 1 * (Q.val.coeff m).natDegree + yWeight params * m) hjmem
  have hile : i ≤ (Q.val.coeff j).natDegree :=
    cpoly_index_le_natDegree_of_coeff_ne_zero (p := Q.val.coeff j) hcoeff
  have hweight :
      1 * i + yWeight params * j ≤ params.weightedDegreeBound := by
    calc
      1 * i + yWeight params * j ≤
          1 * (Q.val.coeff j).natDegree + yWeight params * j := by omega
      _ ≤ CBivariate.natWeightedDegree Q 1 (yWeight params) := hterm
      _ ≤ params.weightedDegreeBound := hdeg
  have hileBound : i ≤ params.weightedDegreeBound := by omega
  have hjleBound : j ≤ params.weightedDegreeBound := by
    nlinarith [hweight, hypos]
  have hweight' : i + yWeight params * j ≤ params.weightedDegreeBound := by
    simpa using hweight
  unfold interpolationMonomials CBivariate.monomialsWeightedDegreeLE CBivariate.monomialGrid
  simp [hileBound, hjleBound, hweight']

/-- Dense interpolation completeness in the ordinary positive-`Y`-weight range. -/
theorem denseInterpolate_complete_of_messageDegree_gt_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    (hHigh : ¬ params.messageDegree ≤ 1) :
    (exists Q, ValidInterpolationWitness points params Q) →
      exists Q, denseInterpolate points params = some Q := by
  intro hExists
  rcases hExists with ⟨Q, hQne, hdeg, hconstraints⟩
  have hconstraintsGS :
      CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity :=
    (CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity Q points
      params.multiplicity).2 hconstraints
  let coeffs := interpolationCoefficientVector params Q
  have hcomplete := weightedDegreeBasis_complete_of_messageDegree_gt_one
    (params := params) hHigh (Q := Q) hdeg
  have hpoly : interpolationPolynomial params coeffs = Q := by
    exact interpolationPolynomialOnBasis_eq_of_complete
      (basis := interpolationMonomials params)
      (Q := Q)
      (CBivariate.monomialsWeightedDegreeLE_nodup 1 (yWeight params)
        params.weightedDegreeBound)
      hcomplete
  have hwidth : DenseMatrix.VectorWidth (interpolationMatrix points params) coeffs := by
    unfold DenseMatrix.VectorWidth coeffs interpolationCoefficientVector interpolationMatrix
      interpolationMatrixOnBasis
    rw [interpolationCoefficientVectorOnBasis_size]
    rfl
  have hsol : DenseMatrix.IsHomogeneousSolution (interpolationMatrix points params) coeffs := by
    exact interpolationCoefficientVectorOnBasis_solution_of_satisfies
      (basis := interpolationMonomials params)
      (Q := Q) hpoly hconstraintsGS
  have hnz : DenseMatrix.NonzeroVector coeffs := by
    exact interpolationCoefficientVectorOnBasis_nonzero_of_complete
      (basis := interpolationMonomials params) (Q := Q) hQne hcomplete
  rcases denseInterpolateWithBasis_complete
      (kernelContext := denseLinearKernelContext F)
      (basis := interpolationMonomials params)
      (points := points) (params := params)
      ⟨coeffs, hwidth, hsol, hnz⟩ with ⟨Qout, hQout⟩
  refine ⟨Qout, ?_⟩
  unfold denseInterpolate denseInterpolateWithKernel
  simp [hHigh, hQout]

/-- The executable interpolation path packaged as a certified GS interpolation backend. -/
def denseInterpContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] : GSInterpContext F where
  interpolate := denseInterpolate
  sound := by
    intro points params Q h
    exact denseInterpolate_sound (kernelContext := denseLinearKernelContext F) h
  complete := by
    intro points params _hdistinct hExists
    by_cases hLow : params.messageDegree ≤ 1
    · refine ⟨lowMessageDegreeInterpolation points params.multiplicity, ?_⟩
      simp [denseInterpolate, denseInterpolateWithKernel, hLow]
    · exact denseInterpolate_complete_of_messageDegree_gt_one
        (F := F) (points := points) (params := params) hLow hExists

/-- Executable interpolation backend soundness. -/
theorem denseInterpContext_correct (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params Q,
      (denseInterpContext F).interpolate points params = some Q →
        ValidInterpolationWitness points params Q :=
  (denseInterpContext F).sound

/-- Executable interpolation backend completeness. -/
theorem denseInterpContext_complete (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params,
      DistinctXCoordinates points →
      (exists Q, ValidInterpolationWitness points params Q) →
        exists Q, (denseInterpContext F).interpolate points params = some Q :=
  (denseInterpContext F).complete

end GuruswamiSudan

end CompPoly
