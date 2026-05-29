/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness

/-!
# Dense Guruswami-Sudan Interpolation Correctness

Correctness contracts for the dense interpolation backend.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- The interpolation matrix is built with rectangular dense storage. -/
private theorem interpolationMatrix_wf {F : Type*} [Semiring F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    DenseMatrix.WellFormed (interpolationMatrix points params) := by
  simp [DenseMatrix.WellFormed, interpolationMatrix, interpolationConstraintMatrix,
    DenseMatrix.ofFn]

private theorem interpolationMatrix_rows {F : Type*} [Semiring F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    (interpolationMatrix points params).rows =
      (interpolationConstraints points params.multiplicity).size := by
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
    (v.map fun x => x / a).getD i 0 = v.getD i 0 / a := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]

private theorem normalizeVector?_some_data {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {v w : Array F} (h : normalizeVector? v = some w) :
    ∃ pivot, pivot < v.size ∧ v.getD pivot 0 ≠ 0 ∧
      w = v.map (fun x => x / v.getD pivot 0) ∧
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
    (fun constraints point =>
      (List.range' 0 multiplicity).foldl
        (fun constraints a =>
          (List.range' 0 (multiplicity - a)).foldl
            (fun constraints b =>
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

private theorem interpolationConstraint_mem_point_step {F : Type*}
    {multiplicity : Nat} {point : F × F} {a b : Nat} (hab : a + b < multiplicity)
    (out : Array (InterpolationConstraint F)) :
    ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
      InterpolationConstraint F) ∈
      List.foldl
        (fun out a' =>
          (List.range' 0 (multiplicity - a')).foldl
            (fun out b' =>
              out.push ({ x := point.1, y := point.2, xOrder := a', yOrder := b' } :
                InterpolationConstraint F))
            out)
        out (List.range' 0 multiplicity) := by
  refine foldl_array_mem_of_mem_step
    (step := fun out a' =>
      (List.range' 0 (multiplicity - a')).foldl
        (fun out b' =>
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
      (step := fun out b' =>
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
    (step := fun constraints point =>
      (List.range' 0 multiplicity).foldl
        (fun constraints a =>
          (List.range' 0 (multiplicity - a)).foldl
            (fun constraints b =>
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

private theorem interpolationMatrix_get {F : Type*} [Semiring F]
    (points : Array (F × F)) (params : GSInterpParams)
    {row col : Nat} (hrow : row < (interpolationMatrix points params).rows)
    (hcol : col < (interpolationMatrix points params).cols) :
    (interpolationMatrix points params).get row col =
      hasseMonomialEval ((interpolationMonomials params).getD col ⟨0, 0⟩)
        ((interpolationConstraints points params.multiplicity).getD row
          ⟨0, 0, 0, 0⟩) := by
  have hrow' : row < (interpolationConstraints points params.multiplicity).size := by
    simpa using hrow
  have hcol' : col < (interpolationMonomials params).size := by
    simpa using hcol
  unfold interpolationMatrix interpolationConstraintMatrix
  rw [DenseMatrix.get_ofFn _ _ _ hrow' hcol']

private theorem array_mem_getD {α : Type*} {xs : Array α} {x default : α}
    (h : x ∈ xs.toList) : ∃ i, i < xs.size ∧ xs.getD i default = x := by
  rcases List.getElem_of_mem h with ⟨i, hi, hget⟩
  refine ⟨i, ?_, ?_⟩
  · simpa using hi
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]
    simpa [Array.getElem_toList] using hget

private theorem interpolationMatrix_dotRow {F : Type*} [Semiring F]
    (points : Array (F × F)) (params : GSInterpParams) (coeffs : Array F)
    {row : Nat} (hrow : row < (interpolationMatrix points params).rows) :
    (interpolationMatrix points params).dotRow row coeffs =
      (List.range' 0 (interpolationMonomials params).size).foldl
        (fun acc col =>
          acc +
            hasseMonomialEval ((interpolationMonomials params).getD col ⟨0, 0⟩)
              ((interpolationConstraints points params.multiplicity).getD row
                ⟨0, 0, 0, 0⟩) *
              coeffs.getD col 0)
        0 := by
  unfold DenseMatrix.dotRow
  simp only [interpolationMatrix_cols]
  rw [List.range_eq_range']
  have hfold : ∀ (xs : List Nat) (acc : F),
      (∀ col, col ∈ xs → col < (interpolationMonomials params).size) →
      xs.foldl
          (fun acc col =>
            acc + (interpolationMatrix points params).get row col * coeffs.getD col 0)
          acc =
        xs.foldl
          (fun acc col =>
            acc +
              hasseMonomialEval ((interpolationMonomials params).getD col ⟨0, 0⟩)
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
        have hcol : col < (interpolationMonomials params).size := hxs col (by simp)
        rw [interpolationMatrix_get points params hrow (by simpa using hcol)]
        apply ih
        intro c hc
        exact hxs c (by simp [hc])
  apply hfold
  intro col hcol
  simpa using (List.mem_range'_1.mp hcol).2

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
        (fun acc col =>
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
            (fun out col =>
              let monomial := monomials.getD col ⟨0, 0⟩
              out + CBivariate.monomialXY monomial.xDegree monomial.yDegree
                (coeffs.getD col 0))
            out) =
        xs.foldl
          (fun acc col =>
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

private theorem interpolationPolynomial_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (coeffs : Array F) :
    CBivariate.natWeightedDegree (interpolationPolynomial params coeffs)
      1 (yWeight params) ≤ params.weightedDegreeBound := by
  unfold interpolationPolynomial interpolationMonomials
  apply CBivariate.ofMonomialCoeffs_natWeightedDegree_le
  intro monomial hmonomial
  simpa using CBivariate.monomialsWeightedDegreeLE_sound
    (xWeight := 1) (yWeight := yWeight params)
    (bound := params.weightedDegreeBound) hmonomial

private theorem dotRow_map_div {F : Type*} [Field F]
    (M : DenseMatrix F) (row : Nat) (v : Array F) (a : F) :
    DenseMatrix.dotRow M row (v.map fun x => x / a) =
      DenseMatrix.dotRow M row v / a := by
  unfold DenseMatrix.dotRow
  have hfold : ∀ (xs : List Nat) (accL accR : F),
      accL = accR / a →
      xs.foldl
          (fun acc col => acc + M.get row col * (v.map fun x => x / a).getD col 0)
          accL =
        xs.foldl (fun acc col => acc + M.get row col * v.getD col 0) accR / a := by
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

private theorem isHomogeneousSolution_map_div {F : Type*} [Field F]
    {M : DenseMatrix F} {v : Array F} (a : F)
    (hsol : DenseMatrix.IsHomogeneousSolution M v) :
    DenseMatrix.IsHomogeneousSolution M (v.map fun x => x / a) := by
  intro row hrow
  rw [dotRow_map_div]
  rw [hsol row hrow]
  simp

private theorem interpolationPolynomial_satisfies_of_solution {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {coeffs : Array F}
    (hsol : DenseMatrix.IsHomogeneousSolution (interpolationMatrix points params) coeffs) :
    CBivariate.SatisfiesMultiplicityConstraints
      (interpolationPolynomial params coeffs) points params.multiplicity := by
  intro point hpoint a b hab
  let constraint : InterpolationConstraint F :=
    { x := point.1, y := point.2, xOrder := a, yOrder := b }
  have hmem := interpolationConstraints_mem (points := points) (point := point)
    hpoint (a := a) (b := b) hab
  rcases array_mem_getD (xs := interpolationConstraints points params.multiplicity)
      (x := constraint) (default := ⟨0, 0, 0, 0⟩) hmem with ⟨row, hrow, hget⟩
  have hrowM : row < (interpolationMatrix points params).rows := by
    simpa using hrow
  have hdot := hsol row hrowM
  rw [interpolationMatrix_dotRow points params coeffs hrowM] at hdot
  change CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
      constraint.y (interpolationPolynomial params coeffs) = 0
  unfold interpolationPolynomial
  rw [hasseDerivativeEval_ofMonomialCoeffs (interpolationMonomials params) coeffs constraint]
  simpa [constraint, hget] using hdot

private theorem normalizeVector?_some_of_nonzero {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {v : Array F} (hnz : DenseMatrix.NonzeroVector v) :
    ∃ norm, normalizeVector? v = some norm := by
  unfold normalizeVector?
  cases hfirst : firstNonzeroIndex? v with
  | some pivot =>
      have hpivot := firstNonzeroIndex?_some_lt_ne (v := v) hfirst
      refine ⟨v.map (fun c => c / v.getD pivot 0), ?_⟩
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

/-- Matrix construction soundness for one returned interpolation witness. -/
theorem denseInterpolate_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelBackend : LinearKernelBackend F}
    {points : Array (Prod F F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : denseInterpolateWithKernel kernelBackend points params = some Q) :
    Q ≠ 0 ∧
      CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound ∧
        CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity := by
  unfold denseInterpolateWithKernel at h
  set matrix := interpolationMatrix points params
  change (normalizeInterpolationPolynomial? params =<< kernelBackend.homogeneousWitness matrix) =
    some Q at h
  cases hw : kernelBackend.homogeneousWitness matrix with
  | none =>
      rw [hw] at h
      contradiction
  | some coeffs =>
      rw [hw] at h
      change normalizeInterpolationPolynomial? params coeffs = some Q at h
      unfold normalizeInterpolationPolynomial? at h
      cases hn : normalizeVector? coeffs with
      | none =>
          rw [hn] at h
          contradiction
      | some norm =>
          rw [hn] at h
          cases h
          have hwidth : DenseMatrix.VectorWidth matrix coeffs :=
            kernelBackend.witness_width hw
          have hsol : DenseMatrix.IsHomogeneousSolution matrix coeffs :=
            kernelBackend.witness_sound
              (by simpa [matrix] using interpolationMatrix_wf points params) hw
          rcases normalizeVector?_some_data hn with
            ⟨pivot, hpivot, _hpivot_ne, hnorm, _hnorm_width, hnorm_one⟩
          have hpivotMonomials : pivot < (interpolationMonomials params).size := by
            have hpivotCols : pivot < matrix.cols := by
              rw [← hwidth]
              exact hpivot
            simpa [matrix, interpolationMatrix_cols] using hpivotCols
          refine ⟨?_, interpolationPolynomial_weightedDegree_le params norm, ?_⟩
          · apply CBivariate.ofMonomialCoeffs_ne_zero_of_coeff_getD_ne_zero
            · exact CBivariate.monomialsWeightedDegreeLE_nodup 1 (yWeight params)
                params.weightedDegreeBound
            · simpa [interpolationMonomials] using hpivotMonomials
            · rw [hnorm_one]
              exact one_ne_zero
          · apply interpolationPolynomial_satisfies_of_solution
            rw [hnorm]
            exact isHomogeneousSolution_map_div (coeffs.getD pivot 0)
              (by simpa [matrix] using hsol)

/-- If the dense interpolation matrix has more columns than rows, dense
interpolation finds a nonzero homogeneous witness. -/
theorem denseInterpolate_exists_of_dimension_slack {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams)
    (hSlack : HasInterpolationDimensionSlack points params) :
    ∃ Q, denseInterpolate points params = some Q := by
  unfold denseInterpolate denseInterpolateWithKernel
  rcases DenseMatrix.homogeneousWitness_exists_of_rows_lt_cols
      (interpolationMatrix points params)
      (by
        simpa [HasInterpolationDimensionSlack, interpolationMatrix_rows,
          interpolationMatrix_cols] using hSlack) with
    ⟨coeffs, hw⟩
  have hnz := DenseMatrix.homogeneousWitness_nonzero hw
  rcases normalizeVector?_some_of_nonzero hnz with ⟨norm, hn⟩
  refine ⟨interpolationPolynomial params norm, ?_⟩
  simp [denseLinearKernelBackend, hw]
  change normalizeInterpolationPolynomial? params coeffs =
    some (interpolationPolynomial params norm)
  unfold normalizeInterpolationPolynomial?
  rw [hn]

/-- Dense interpolation packaged as a certified GS interpolation backend. -/
def denseInterpBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] : GSInterpBackend F where
  interpolate := denseInterpolate
  sound := by
    intro points params Q h
    exact denseInterpolate_sound (kernelBackend := denseLinearKernelBackend F) h
  complete := by
    intro points params hExists
    sorry

/-- Dense interpolation backend soundness. -/
theorem denseInterpBackend_correct (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params Q,
      (denseInterpBackend F).interpolate points params = some Q →
        Q ≠ 0 ∧
          CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound ∧
            CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity :=
  (denseInterpBackend F).sound

/-- Dense interpolation backend completeness, assuming the dense kernel solver
completeness contract. -/
theorem denseInterpBackend_complete (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params,
      (exists Q,
        Q ≠ 0 ∧
          CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound ∧
            CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity) →
        exists Q, (denseInterpBackend F).interpolate points params = some Q :=
  (denseInterpBackend F).complete

end GuruswamiSudan

end CompPoly
