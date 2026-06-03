/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Combinations

/-!
# Koetter Span Transport Helpers

Pivot-correction, span-transport, generated-basis, `Y`-boundedness, and
final-basis invariant lemmas.
-/

namespace CompPoly

namespace GuruswamiSudan

def koetterPivotCorrectionOn {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) (xs : List Nat) :
    CPolynomial F :=
  xs.foldl
    (fun out idx ↦
      if idx == pivot.index then
        out + weights idx
      else
        let delta := koetterDiscrepancy constraint (basis.getD idx 0)
        if delta == 0 then
          out
        else
          out + CPolynomial.C (delta / pivot.discrepancy) * weights idx)
    0

def koetterPivotCorrection {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) :
    CPolynomial F :=
  koetterPivotCorrectionOn constraint basis pivot weights (List.range basis.size)

def koetterNonpivotWeights {F : Type*} [Zero F] [BEq F]
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) : Nat → CPolynomial F :=
  fun idx ↦ if idx == pivot.index then 0 else weights idx

def koetterTransportWeights {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) :
    Nat → CPolynomial F :=
  fun idx ↦
    if idx == pivot.index then
      (koetterPivotCorrection constraint basis pivot weights).divByMonic
        (CPolynomial.linearFactor constraint.x)
    else
      weights idx

theorem koetterTransportWeights_pivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) :
    koetterTransportWeights constraint basis pivot weights pivot.index =
      (koetterPivotCorrection constraint basis pivot weights).divByMonic
        (CPolynomial.linearFactor constraint.x) := by
  unfold koetterTransportWeights
  rw [if_pos (by simp)]

theorem koetterTransportWeights_nonpivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) {idx : Nat}
    (hidx : ¬ idx == pivot.index) :
    koetterTransportWeights constraint basis pivot weights idx = weights idx := by
  unfold koetterTransportWeights
  rw [if_neg hidx]

theorem ofYConstant_transportPivot_mul_updatedPivot_eq_correction_oldPivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F)
    (hroot :
      CPolynomial.eval constraint.x
        (koetterPivotCorrection constraint basis pivot weights) = 0) :
    CBivariate.ofYConstant
          (koetterTransportWeights constraint basis pivot weights pivot.index) *
        koetterUpdatedEntry constraint basis pivot pivot.index =
      CBivariate.ofYConstant
          (koetterPivotCorrection constraint basis pivot weights) *
        basis.getD pivot.index 0 := by
  rw [koetterTransportWeights_pivot]
  exact (ofYConstant_mul_oldPivot_eq_updatedPivot_of_eval_zero
    constraint basis pivot (koetterPivotCorrection constraint basis pivot weights) hroot).symm

theorem ofYConstant_transportNonpivot_mul_updated_eq_weight_mul_updated {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) {idx : Nat}
    (hidx : ¬ idx == pivot.index) :
    CBivariate.ofYConstant
          (koetterTransportWeights constraint basis pivot weights idx) *
        koetterUpdatedEntry constraint basis pivot idx =
      CBivariate.ofYConstant (weights idx) *
        koetterUpdatedEntry constraint basis pivot idx := by
  rw [koetterTransportWeights_nonpivot constraint basis pivot weights hidx]

theorem koetterBasisCombination_eq_nonpivotUpdated_add_correction {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) :
    koetterBasisCombination weights basis =
      koetterUpdatedEntryCombination (koetterNonpivotWeights pivot weights)
          constraint basis pivot +
        CBivariate.ofYConstant
            (koetterPivotCorrection constraint basis pivot weights) *
          basis.getD pivot.index 0 := by
  unfold koetterBasisCombination koetterUpdatedEntryCombination
  let oldStep : CBivariate F → Nat → CBivariate F :=
    fun out idx ↦ out + CBivariate.ofYConstant (weights idx) * basis.getD idx 0
  let updatedStep : CBivariate F → Nat → CBivariate F :=
    fun out idx ↦
      out + CBivariate.ofYConstant (koetterNonpivotWeights pivot weights idx) *
        koetterUpdatedEntry constraint basis pivot idx
  let correctionStep : CPolynomial F → Nat → CPolynomial F :=
    fun out idx ↦
      if idx == pivot.index then
        out + weights idx
      else
        let delta := koetterDiscrepancy constraint (basis.getD idx 0)
        if delta == 0 then
          out
        else
          out + CPolynomial.C (delta / pivot.discrepancy) * weights idx
  have hfold :
      ∀ (xs : List Nat) oldOut updatedOut correctionOut,
        oldOut =
          updatedOut +
            CBivariate.ofYConstant correctionOut * basis.getD pivot.index 0 →
        xs.foldl oldStep oldOut =
          xs.foldl updatedStep updatedOut +
            CBivariate.ofYConstant (xs.foldl correctionStep correctionOut) *
              basis.getD pivot.index 0 := by
    intro xs
    induction xs with
    | nil =>
        intro oldOut updatedOut correctionOut hrel
        simpa using hrel
    | cons idx xs ih =>
        intro oldOut updatedOut correctionOut hrel
        simp only [List.foldl_cons]
        apply ih
        unfold oldStep updatedStep correctionStep
        by_cases hidx : idx == pivot.index
        · rw [if_pos hidx]
          have hidxEq : idx = pivot.index := LawfulBEq.eq_of_beq hidx
          subst idx
          unfold koetterNonpivotWeights
          rw [if_pos (by simp), ofYConstant_zero, zero_mul, add_zero,
            ofYConstant_add]
          rw [hrel]
          ring
        · rw [if_neg hidx]
          unfold koetterNonpivotWeights
          rw [if_neg hidx]
          by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
          · rw [if_pos hdelta]
            have hzero :
                koetterDiscrepancy constraint (basis.getD idx 0) = 0 :=
              LawfulBEq.eq_of_beq hdelta
            have hlocal :=
              ofYConstant_mul_oldNonpivot_eq_updated_add_correction
                constraint basis pivot (weights idx) hidx
            rw [hzero] at hlocal
            simp [ofYConstant_zero] at hlocal
            have hlocal' :
                CBivariate.ofYConstant (weights idx) * basis.getD idx 0 =
                  CBivariate.ofYConstant (weights idx) *
                    koetterUpdatedEntry constraint basis pivot idx := by
              simpa [Array.getD_eq_getD_getElem?] using hlocal
            rw [hrel, hlocal']
            ring
          · rw [if_neg hdelta]
            have hlocal :=
              ofYConstant_mul_oldNonpivot_eq_updated_add_correction
                constraint basis pivot (weights idx) hidx
            have hlocal' :
                CBivariate.ofYConstant (weights idx) * basis.getD idx 0 =
                  CBivariate.ofYConstant (weights idx) *
                      koetterUpdatedEntry constraint basis pivot idx +
                    CBivariate.ofYConstant
                        (CPolynomial.C
                          (koetterDiscrepancy constraint (basis.getD idx 0) /
                            pivot.discrepancy) *
                          weights idx) *
                      basis.getD pivot.index 0 := by
              simpa [Array.getD_eq_getD_getElem?] using hlocal
            rw [hrel, hlocal', ofYConstant_add]
            ring
  simpa [oldStep, updatedStep, correctionStep, koetterPivotCorrection,
    koetterPivotCorrectionOn] using
    hfold (List.range basis.size) 0 0 0 (by simp [ofYConstant_zero])

theorem koetterUpdatedEntryCombination_transport_eq_nonpivot_add_pivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F)
    (hpivot : pivot.index < basis.size) :
    koetterUpdatedEntryCombination
        (koetterTransportWeights constraint basis pivot weights)
        constraint basis pivot =
      koetterUpdatedEntryCombination (koetterNonpivotWeights pivot weights)
          constraint basis pivot +
        CBivariate.ofYConstant
            (koetterTransportWeights constraint basis pivot weights pivot.index) *
          koetterUpdatedEntry constraint basis pivot pivot.index := by
  unfold koetterUpdatedEntryCombination
  let transportTerm : Nat → CBivariate F :=
    fun idx ↦
      CBivariate.ofYConstant
          (koetterTransportWeights constraint basis pivot weights idx) *
        koetterUpdatedEntry constraint basis pivot idx
  let nonpivotTerm : Nat → CBivariate F :=
    fun idx ↦
      CBivariate.ofYConstant (koetterNonpivotWeights pivot weights idx) *
        koetterUpdatedEntry constraint basis pivot idx
  let pivotTerm : CBivariate F :=
    CBivariate.ofYConstant
        (koetterTransportWeights constraint basis pivot weights pivot.index) *
      koetterUpdatedEntry constraint basis pivot pivot.index
  let singleTerm : Nat → CBivariate F :=
    fun idx ↦ if idx == pivot.index then pivotTerm else 0
  change
    (List.range basis.size).foldl (fun out idx ↦ out + transportTerm idx) 0 =
      (List.range basis.size).foldl (fun out idx ↦ out + nonpivotTerm idx) 0 +
        pivotTerm
  have hterms :
      ∀ idx, idx ∈ List.range basis.size →
        transportTerm idx = nonpivotTerm idx + singleTerm idx := by
    intro idx _hmem
    by_cases hidx : idx == pivot.index
    · have hidxEq : idx = pivot.index := LawfulBEq.eq_of_beq hidx
      subst idx
      unfold transportTerm nonpivotTerm singleTerm koetterNonpivotWeights
      rw [if_pos (by simp), if_pos (by simp)]
      rw [ofYConstant_zero, zero_mul, zero_add]
    · unfold transportTerm nonpivotTerm singleTerm koetterNonpivotWeights
      rw [if_neg hidx, if_neg hidx]
      rw [koetterTransportWeights_nonpivot constraint basis pivot weights hidx]
      rw [add_zero]
  have hfold :
      (List.range basis.size).foldl (fun out idx ↦ out + transportTerm idx) 0 =
        (List.range basis.size).foldl
          (fun out idx ↦ out + (nonpivotTerm idx + singleTerm idx)) 0 := by
    apply foldl_add_congr_terms
    exact hterms
  rw [hfold, foldl_add_distrib_terms]
  have hsingle :
      (List.range basis.size).foldl (fun out idx ↦ out + singleTerm idx) 0 =
        pivotTerm := by
    unfold singleTerm
    exact foldl_add_single_beq_of_nodup_mem (List.range basis.size)
      pivot.index pivotTerm List.nodup_range
      (List.mem_range.mpr hpivot)
  rw [hsingle]

theorem koetterBasisCombination_eq_updateBasis_transport {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F)
    (hpivot : pivot.index < basis.size)
    (hroot :
      CPolynomial.eval constraint.x
        (koetterPivotCorrection constraint basis pivot weights) = 0) :
    koetterBasisCombination weights basis =
      koetterBasisCombination
        (koetterTransportWeights constraint basis pivot weights)
        (koetterUpdateBasis constraint basis pivot) := by
  rw [koetterBasisCombination_updateBasis_eq_updatedEntryCombination]
  rw [koetterBasisCombination_eq_nonpivotUpdated_add_correction]
  rw [koetterUpdatedEntryCombination_transport_eq_nonpivot_add_pivot
    constraint basis pivot weights hpivot]
  rw [ofYConstant_transportPivot_mul_updatedPivot_eq_correction_oldPivot
    constraint basis pivot weights hroot]

theorem koetterPivotCorrection_eval_mul_discrepancy_eq_foldl {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F)
    (hpivotDisc :
      pivot.discrepancy =
        koetterDiscrepancy constraint (basis.getD pivot.index 0))
    (hpivotNe : pivot.discrepancy ≠ 0) :
    CPolynomial.eval constraint.x
        (koetterPivotCorrection constraint basis pivot weights) *
        pivot.discrepancy =
      (List.range basis.size).foldl
        (fun acc idx ↦
          acc + CPolynomial.eval constraint.x (weights idx) *
            koetterDiscrepancy constraint (basis.getD idx 0))
        0 := by
  unfold koetterPivotCorrection
  let scalarStep : F → Nat → F :=
    fun acc idx ↦
      acc + CPolynomial.eval constraint.x (weights idx) *
        koetterDiscrepancy constraint (basis.getD idx 0)
  let correctionStep : CPolynomial F → Nat → CPolynomial F :=
    fun out idx ↦
      if idx == pivot.index then
        out + weights idx
      else
        let delta := koetterDiscrepancy constraint (basis.getD idx 0)
        if delta == 0 then
          out
        else
          out + CPolynomial.C (delta / pivot.discrepancy) * weights idx
  have hfold :
      ∀ (xs : List Nat) out acc,
        CPolynomial.eval constraint.x out * pivot.discrepancy = acc →
          CPolynomial.eval constraint.x (xs.foldl correctionStep out) *
              pivot.discrepancy =
            xs.foldl scalarStep acc := by
    intro xs
    induction xs with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons idx xs ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        unfold correctionStep scalarStep
        by_cases hidx : idx == pivot.index
        · rw [if_pos hidx, cpoly_eval_add]
          have hidxEq : idx = pivot.index := LawfulBEq.eq_of_beq hidx
          subst idx
          rw [← hpivotDisc]
          ring_nf
          rw [hacc]
          ring
        · rw [if_neg hidx]
          by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
          · rw [if_pos hdelta]
            have hzero :
                koetterDiscrepancy constraint (basis.getD idx 0) = 0 :=
              LawfulBEq.eq_of_beq hdelta
            rw [hzero]
            simpa using hacc
          · rw [if_neg hdelta, cpoly_eval_add, CPolynomial.eval_mul,
              CPolynomial.eval_C]
            field_simp [hpivotNe]
            rw [hacc]
  simpa [scalarStep, correctionStep, koetterPivotCorrection, koetterPivotCorrectionOn] using
    hfold (List.range basis.size) 0 0 (by
    rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_zero, Polynomial.eval_zero]
    simp)

theorem koetterPivotCorrection_eval_eq_zero_of_foldl_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F)
    (hpivotDisc :
      pivot.discrepancy =
        koetterDiscrepancy constraint (basis.getD pivot.index 0))
    (hpivotNe : pivot.discrepancy ≠ 0)
    (hfoldZero :
      (List.range basis.size).foldl
          (fun acc idx ↦
            acc + CPolynomial.eval constraint.x (weights idx) *
              koetterDiscrepancy constraint (basis.getD idx 0))
          0 = 0) :
    CPolynomial.eval constraint.x
      (koetterPivotCorrection constraint basis pivot weights) = 0 := by
  have hmul := koetterPivotCorrection_eval_mul_discrepancy_eq_foldl
    constraint basis pivot weights hpivotDisc hpivotNe
  rw [hfoldZero] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right hpivotNe

theorem koetterDiscrepancy_combinationFold_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (weights : Nat → CPolynomial F)
    (xs : List Nat)
    (hidx : ∀ idx, idx ∈ xs → idx < basis.size)
    (hLower : ∀ idx, idx ∈ xs → ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD idx 0) = 0)
    (out : CBivariate F) (acc : F)
    (hacc : koetterDiscrepancy constraint out = acc) :
    koetterDiscrepancy constraint
        (xs.foldl
          (fun out idx ↦ out + CBivariate.ofYConstant (weights idx) * basis.getD idx 0)
          out) =
      xs.foldl
        (fun acc idx ↦
          acc + CPolynomial.eval constraint.x (weights idx) *
            koetterDiscrepancy constraint (basis.getD idx 0))
        acc := by
  induction xs generalizing out acc with
  | nil =>
      simpa using hacc
  | cons idx xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hidx j (by simp [hj])
      · intro j hj a ha
        exact hLower j (by simp [hj]) a ha
      · rw [koetterDiscrepancy_add, hacc]
        rw [koetterDiscrepancy_ofYConstant_mul_eq_eval_mul_of_lower]
        intro a ha
        exact hLower idx (by simp) a ha

theorem koetterDiscrepancy_basisCombination_eq_foldl {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (weights : Nat → CPolynomial F)
    (hLower : ∀ idx, idx < basis.size → ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD idx 0) = 0) :
    koetterDiscrepancy constraint (koetterBasisCombination weights basis) =
      (List.range basis.size).foldl
        (fun acc idx ↦
          acc + CPolynomial.eval constraint.x (weights idx) *
            koetterDiscrepancy constraint (basis.getD idx 0))
        0 := by
  unfold koetterBasisCombination
  apply koetterDiscrepancy_combinationFold_eq
  · intro idx hmem
    exact List.mem_range.mp hmem
  · intro idx hmem
    exact hLower idx (List.mem_range.mp hmem)
  · unfold koetterDiscrepancy
    rw [CBivariate.hasseDerivativeEval_zero]

theorem koetterBasisCombination_discrepancy_foldl_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (weights : Nat → CPolynomial F) {Q : CBivariate F}
    (hcomb : koetterBasisCombination weights basis = Q)
    (hdisc : koetterDiscrepancy constraint Q = 0)
    (hLower : ∀ idx, idx < basis.size → ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD idx 0) = 0) :
    (List.range basis.size).foldl
        (fun acc idx ↦
          acc + CPolynomial.eval constraint.x (weights idx) *
            koetterDiscrepancy constraint (basis.getD idx 0))
        0 = 0 := by
  have hcombDisc :
      koetterDiscrepancy constraint (koetterBasisCombination weights basis) = 0 := by
    rw [hcomb]
    exact hdisc
  have hfold := koetterDiscrepancy_basisCombination_eq_foldl
    constraint basis weights hLower
  simpa [hfold] using hcombDisc

theorem koetterPivotCorrection_eval_eq_zero_of_combination {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (weights : Nat → CPolynomial F) {Q : CBivariate F}
    (hcomb : koetterBasisCombination weights basis = Q)
    (hdisc : koetterDiscrepancy constraint Q = 0)
    (hLower : ∀ idx, idx < basis.size → ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD idx 0) = 0)
    (hpivotDisc :
      pivot.discrepancy =
        koetterDiscrepancy constraint (basis.getD pivot.index 0))
    (hpivotNe : pivot.discrepancy ≠ 0) :
    CPolynomial.eval constraint.x
      (koetterPivotCorrection constraint basis pivot weights) = 0 := by
  apply koetterPivotCorrection_eval_eq_zero_of_foldl_eq_zero
    constraint basis pivot weights hpivotDisc hpivotNe
  exact koetterBasisCombination_discrepancy_foldl_eq_zero
    constraint basis weights hcomb hdisc hLower

theorem koetterUpdateBasis_span_contains_of_discrepancy_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) {Q : CBivariate F}
    (hpivot : pivot.index < basis.size)
    (hpivotDisc :
      pivot.discrepancy =
        koetterDiscrepancy constraint (basis.getD pivot.index 0))
    (hpivotNe : pivot.discrepancy ≠ 0)
    (hspan : koetterBasisSpanContains basis Q)
    (hdisc : koetterDiscrepancy constraint Q = 0)
    (hLower : ∀ idx, idx < basis.size → ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD idx 0) = 0) :
    koetterBasisSpanContains (koetterUpdateBasis constraint basis pivot) Q := by
  rcases hspan with ⟨weights, hcomb⟩
  refine ⟨koetterTransportWeights constraint basis pivot weights, ?_⟩
  have hroot := koetterPivotCorrection_eval_eq_zero_of_combination
    constraint basis pivot weights hcomb hdisc hLower hpivotDisc hpivotNe
  rw [← hcomb]
  exact (koetterBasisCombination_eq_updateBasis_transport
    constraint basis pivot weights hpivot hroot).symm

theorem koetterProcessConstraint_span_contains_of_discrepancy_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F) {Q : CBivariate F}
    (hspan : koetterBasisSpanContains state.basis Q)
    (hdisc : koetterDiscrepancy constraint Q = 0)
    (hLower : ∀ idx, idx < state.basis.size → ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (state.basis.getD idx 0) = 0) :
    koetterBasisSpanContains (koetterProcessConstraint params constraint state).basis Q := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      simpa using hspan
  | some pivot =>
      change koetterBasisSpanContains
        (koetterUpdateBasis constraint state.basis pivot) Q
      rcases koetterSelectPivot_some_discrepancy hpivot with ⟨hpivotDisc, hpivotNe⟩
      exact koetterUpdateBasis_span_contains_of_discrepancy_zero
        constraint state.basis pivot (koetterSelectPivot_some_index_lt hpivot)
        hpivotDisc hpivotNe hspan hdisc hLower

theorem koetterProcessConstraints_fold_span_contains {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (original : List (InterpolationConstraint F))
    (hbefore : koetterConstraintsLowerBefore original) {Q : CBivariate F}
    (hQDisc : ∀ constraint, constraint ∈ original →
      koetterDiscrepancy constraint Q = 0) :
    ∀ remaining processed state,
      processed.reverse ++ remaining = original →
      koetterBasisSpanContains state.basis Q →
      koetterBasisSatisfiesConstraints state.basis processed →
      koetterConstraintsLowerClosed processed →
      koetterBasisSpanContains
        (remaining.foldl (fun state constraint ↦ koetterProcessConstraint params constraint state)
          state).basis Q := by
  intro remaining
  induction remaining with
  | nil =>
      intro processed state _hsplit hspan _hSat _hClosed
      simpa using hspan
  | cons current remaining ih =>
      intro processed state hsplit hspan hSat hClosed
      simp only [List.foldl_cons]
      apply ih (current :: processed) (koetterProcessConstraint params current state)
      · rw [List.reverse_cons, List.append_assoc]
        simpa using hsplit
      · apply koetterProcessConstraint_span_contains_of_discrepancy_zero
        · exact hspan
        · apply hQDisc current
          have hmem : current ∈ processed.reverse ++ current :: remaining := by
            simp
          simpa [hsplit] using hmem
        · intro idx hidx a ha
          have hLowerMem :=
            koetterConstraintLowerIn_of_before_lt hsplit hbefore hClosed a ha
          have hSatLower := hSat (lowerXConstraint current a) hLowerMem idx hidx
          simpa [koetterDiscrepancy, lowerXConstraint] using hSatLower
      · exact koetterProcessConstraint_satisfies_cons params current state processed hSat hClosed
          (koetterConstraintLowerIn_of_before hsplit hbefore)
      · exact koetterConstraintsLowerClosed_cons_of_before hsplit hbefore hClosed

theorem koetterFinalBasis_span_contains {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) {Q : CBivariate F}
    (hspan : koetterBasisSpanContains (koetterInitialBasis params) Q)
    (hdisc : ∀ constraint,
      constraint ∈ (interpolationConstraints points params.multiplicity).toList →
        koetterDiscrepancy constraint Q = 0) :
    koetterBasisSpanContains
      (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis Q := by
  let constraints := interpolationConstraints points params.multiplicity
  let initial := koetterInitialState (F := F) params
  have hbefore : koetterConstraintsLowerBefore constraints.toList := by
    rw [interpolationConstraints_toList_eq_list]
    exact interpolationConstraintsList_lowerBefore points params.multiplicity
  have hspanFold := koetterProcessConstraints_fold_span_contains
    params constraints.toList hbefore hdisc constraints.toList [] initial (by simp)
    (by simpa [initial, koetterInitialState] using hspan)
    (by intro constraint hmem; simp at hmem)
    (by intro constraint hmem; simp at hmem)
  simpa [constraints, initial, koetterProcessConstraints] using hspanFold

theorem koetterInitialBasis_combination_eq_finiteYExpansion {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (params : GSInterpParams) :
    koetterBasisCombination (fun j ↦ Q.val.coeff j) (koetterInitialBasis params) =
      koetterFiniteYExpansion Q (koetterYCap params) := by
  unfold koetterBasisCombination koetterFiniteYExpansion
  rw [koetterInitialBasis_size]
  apply foldl_add_congr_terms
  intro idx hidx
  have hidxle : idx ≤ koetterYCap params := by
    have hlt : idx < koetterYCap params + 1 := List.mem_range.mp hidx
    omega
  rw [koetterInitialBasis_getD_of_le_yCap params hidxle]
  exact ofYConstant_mul_monomialY_eq_ofYCoefficient (Q.val.coeff idx) idx

theorem koetterInitialBasis_spans_of_yCap {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {params : GSInterpParams}
    (hQ : ∀ j, koetterYCap params < j → Q.val.coeff j = 0) :
    koetterBasisSpanContains (koetterInitialBasis params) Q := by
  refine ⟨fun j ↦ Q.val.coeff j, ?_⟩
  rw [koetterInitialBasis_combination_eq_finiteYExpansion,
    koetterFiniteYExpansion_eq_of_yCap hQ]

inductive koetterBasisGeneratedBy {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array (CBivariate F)) : CBivariate F → Prop
  | entry {idx : Nat} (hidx : idx < basis.size) :
      koetterBasisGeneratedBy basis (basis.getD idx 0)
  | sub {P Q : CBivariate F}
      (hP : koetterBasisGeneratedBy basis P)
      (hQ : koetterBasisGeneratedBy basis Q) :
      koetterBasisGeneratedBy basis (P - Q)
  | cc_mul (c : F) {P : CBivariate F}
      (hP : koetterBasisGeneratedBy basis P) :
      koetterBasisGeneratedBy basis (CBivariate.CC c * P)
  | linearX_mul (x : F) {P : CBivariate F}
      (hP : koetterBasisGeneratedBy basis P) :
      koetterBasisGeneratedBy basis (CBivariate.linearXFactor x * P)

theorem koetterUpdatedEntry_generatedBy_oldBasis {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (hpivot : pivot.index < basis.size)
    {idx : Nat} (hi : idx < basis.size) :
    koetterBasisGeneratedBy basis (koetterUpdatedEntry constraint basis pivot idx) := by
  unfold koetterUpdatedEntry
  by_cases hidx : idx == pivot.index
  · rw [if_pos hidx]
    exact koetterBasisGeneratedBy.linearX_mul constraint.x
      (koetterBasisGeneratedBy.entry hi)
  · rw [if_neg hidx]
    by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
    · rw [if_pos hdelta]
      exact koetterBasisGeneratedBy.entry hi
    · rw [if_neg hdelta]
      exact koetterBasisGeneratedBy.sub (koetterBasisGeneratedBy.entry hi)
        (koetterBasisGeneratedBy.cc_mul
          (koetterDiscrepancy constraint (basis.getD idx 0) / pivot.discrepancy)
          (koetterBasisGeneratedBy.entry hpivot))

theorem koetterUpdateBasis_entries_generatedBy_oldBasis {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (hpivot : pivot.index < basis.size) :
    ∀ idx, idx < (koetterUpdateBasis constraint basis pivot).size →
      koetterBasisGeneratedBy basis
        ((koetterUpdateBasis constraint basis pivot).getD idx 0) := by
  intro idx hi
  have hsize := koetterUpdateBasis_size constraint basis pivot
  have hiOld : idx < basis.size := by
    simpa [hsize] using hi
  rw [koetterUpdateBasis_getD_of_lt constraint basis pivot hiOld]
  exact koetterUpdatedEntry_generatedBy_oldBasis constraint basis pivot hpivot hiOld

theorem koetterBasisGeneratedBy_of_entries_generatedBy {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {base basis : Array (CBivariate F)}
    (hentries : ∀ idx, idx < basis.size →
      koetterBasisGeneratedBy base (basis.getD idx 0)) :
    ∀ {Q : CBivariate F}, koetterBasisGeneratedBy basis Q →
      koetterBasisGeneratedBy base Q := by
  intro Q hQ
  induction hQ with
  | entry hidx =>
      exact hentries _ hidx
  | sub hP hQ ihP ihQ =>
      exact koetterBasisGeneratedBy.sub ihP ihQ
  | cc_mul c hP ihP =>
      exact koetterBasisGeneratedBy.cc_mul c ihP
  | linearX_mul x hP ihP =>
      exact koetterBasisGeneratedBy.linearX_mul x ihP

theorem koetterUpdateBasis_entries_generatedBy_base {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {base : Array (CBivariate F)}
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (hpivot : pivot.index < basis.size)
    (hentries : ∀ idx, idx < basis.size →
      koetterBasisGeneratedBy base (basis.getD idx 0)) :
    ∀ idx, idx < (koetterUpdateBasis constraint basis pivot).size →
      koetterBasisGeneratedBy base
        ((koetterUpdateBasis constraint basis pivot).getD idx 0) := by
  intro idx hi
  have hOld :=
    koetterUpdateBasis_entries_generatedBy_oldBasis constraint basis pivot hpivot idx hi
  exact koetterBasisGeneratedBy_of_entries_generatedBy hentries hOld

theorem koetterProcessConstraint_entries_generatedBy_base {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {base : Array (CBivariate F)}
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F)
    (hentries : ∀ idx, idx < state.basis.size →
      koetterBasisGeneratedBy base (state.basis.getD idx 0)) :
    ∀ idx, idx < (koetterProcessConstraint params constraint state).basis.size →
      koetterBasisGeneratedBy base
        ((koetterProcessConstraint params constraint state).basis.getD idx 0) := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      intro idx hi
      simpa using hentries idx hi
  | some pivot =>
      intro idx hi
      simp at hi ⊢
      simpa [Array.getD_eq_getD_getElem?] using
        koetterUpdateBasis_entries_generatedBy_base constraint state.basis pivot
          (koetterSelectPivot_some_index_lt hpivot) hentries idx hi

theorem koetterProcessConstraints_entries_generatedBy_base {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {base : Array (CBivariate F)}
    (params : GSInterpParams) (constraints : Array (InterpolationConstraint F))
    (state : KoetterState F)
    (hentries : ∀ idx, idx < state.basis.size →
      koetterBasisGeneratedBy base (state.basis.getD idx 0)) :
    ∀ idx, idx < (koetterProcessConstraints params constraints state).basis.size →
      koetterBasisGeneratedBy base
        ((koetterProcessConstraints params constraints state).basis.getD idx 0) := by
  unfold koetterProcessConstraints
  rw [← Array.foldl_toList]
  induction constraints.toList generalizing state with
  | nil =>
      simpa using hentries
  | cons constraint _rest ih =>
      simp only [List.foldl_cons]
      exact ih (koetterProcessConstraint params constraint state)
        (koetterProcessConstraint_entries_generatedBy_base params constraint state hentries)

theorem koetterFinalBasis_entries_generatedBy_initial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) :
    ∀ idx,
      idx <
        (koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis.size →
      koetterBasisGeneratedBy (koetterInitialBasis params)
        ((koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis.getD idx 0) := by
  exact koetterProcessConstraints_entries_generatedBy_base params
    (interpolationConstraints points params.multiplicity)
    (koetterInitialState params)
    (by
      intro idx hidx
      simpa [koetterInitialState] using koetterBasisGeneratedBy.entry
        (basis := koetterInitialBasis params) hidx)

theorem coeff_linearXFactor_mul_eq_zero_of_yCoeff_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x : F) (P : CBivariate F) {j : Nat}
    (hP : ∀ i, CompPoly.CBivariate.coeff P i j = 0) :
    ∀ i, CompPoly.CBivariate.coeff (CBivariate.linearXFactor x * P) i j = 0 := by
  intro i
  unfold CBivariate.linearXFactor
  rw [sub_mul, CompPoly.CBivariate.coeff_sub]
  cases i with
  | zero =>
      rw [CompPoly.CBivariate.coeff_X_mul_zero, CompPoly.CBivariate.coeff_CC_mul]
      simp [hP 0]
  | succ i =>
      rw [CompPoly.CBivariate.coeff_X_mul_succ, CompPoly.CBivariate.coeff_CC_mul]
      simp [hP i, hP (i + 1)]

theorem koetterBasisGeneratedBy_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {basis : Array (CBivariate F)} {cap : Nat}
    (hBasis : koetterBasisYBounded cap basis) :
    ∀ {Q : CBivariate F}, koetterBasisGeneratedBy basis Q →
      ∀ i j, cap < j → CBivariate.coeff Q i j = 0 := by
  intro Q hQ
  induction hQ with
  | entry hidx =>
      intro i j hj
      exact hBasis _ hidx i j hj
  | sub hP hQ ihP ihQ =>
      intro i j hj
      rw [CompPoly.CBivariate.coeff_sub, ihP i j hj, ihQ i j hj]
      simp
  | cc_mul c hP ihP =>
      intro i j hj
      rw [CompPoly.CBivariate.coeff_CC_mul, ihP i j hj]
      simp
  | linearX_mul x hP ihP =>
      intro i j hj
      exact coeff_linearXFactor_mul_eq_zero_of_yCoeff_zero x _
        (fun k ↦ ihP k j hj) i

theorem koetterInitialBasis_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) :
    koetterBasisYBounded (F := F) (koetterYCap params)
      (koetterInitialBasis params) := by
  intro idx hidx i j hj
  have hidxCap : idx ≤ koetterYCap params := by
    rw [koetterInitialBasis_size] at hidx
    omega
  rw [koetterInitialBasis_getD_of_le_yCap params hidxCap]
  rw [CompPoly.CBivariate.coeff_monomialXY]
  have hne : ¬(i = 0 ∧ j = idx) := by
    intro hmatch
    rcases hmatch with ⟨_hi, hjidx⟩
    have hjle : j ≤ koetterYCap params := by
      omega
    exact (Nat.not_lt_of_ge hjle) hj
  simp [hne]

theorem koetterUpdatedEntry_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {cap : Nat} (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) (pivot : KoetterPivot F)
    (hBasis : koetterBasisYBounded cap basis)
    (hpivot : pivot.index < basis.size) {idx : Nat} (hi : idx < basis.size) :
    ∀ i j, cap < j →
      CompPoly.CBivariate.coeff (koetterUpdatedEntry constraint basis pivot idx) i j = 0 := by
  intro i j hj
  unfold koetterUpdatedEntry
  by_cases hidx : idx == pivot.index
  · rw [if_pos hidx]
    exact coeff_linearXFactor_mul_eq_zero_of_yCoeff_zero constraint.x
      (basis.getD idx 0) (j := j) (fun k ↦ hBasis idx hi k j hj) i
  · rw [if_neg hidx]
    by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
    · rw [if_pos hdelta]
      exact hBasis idx hi i j hj
    · rw [if_neg hdelta]
      rw [CompPoly.CBivariate.coeff_sub, CompPoly.CBivariate.coeff_CC_mul]
      rw [hBasis idx hi i j hj, hBasis pivot.index hpivot i j hj]
      simp

theorem koetterUpdateBasis_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {cap : Nat} (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) (pivot : KoetterPivot F)
    (hBasis : koetterBasisYBounded cap basis)
    (hpivot : pivot.index < basis.size) :
    koetterBasisYBounded cap (koetterUpdateBasis constraint basis pivot) := by
  intro idx hi i j hj
  have hsize := koetterUpdateBasis_size constraint basis pivot
  have hiOld : idx < basis.size := by
    rw [hsize] at hi
    exact hi
  rw [koetterUpdateBasis_getD_of_lt constraint basis pivot hiOld]
  exact koetterUpdatedEntry_yBounded constraint basis pivot hBasis hpivot hiOld i j hj

theorem koetterProcessConstraint_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {cap : Nat} (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F)
    (hBasis : koetterBasisYBounded cap state.basis) :
    koetterBasisYBounded cap (koetterProcessConstraint params constraint state).basis := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      simpa using hBasis
  | some pivot =>
      change koetterBasisYBounded cap (koetterUpdateBasis constraint state.basis pivot)
      exact koetterUpdateBasis_yBounded constraint state.basis pivot hBasis
        (koetterSelectPivot_some_index_lt hpivot)

theorem koetterProcessConstraints_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {cap : Nat} (params : GSInterpParams) (constraints : Array (InterpolationConstraint F))
    (state : KoetterState F)
    (hBasis : koetterBasisYBounded cap state.basis) :
    koetterBasisYBounded cap (koetterProcessConstraints params constraints state).basis := by
  unfold koetterProcessConstraints
  rw [← Array.foldl_toList]
  induction constraints.toList generalizing state with
  | nil =>
      simpa using hBasis
  | cons constraint _rest ih =>
      simp only [List.foldl_cons]
      exact ih (koetterProcessConstraint params constraint state)
        (koetterProcessConstraint_yBounded params constraint state hBasis)

theorem koetterFinalBasis_yBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) :
    koetterBasisYBounded (koetterYCap params)
      (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis := by
  exact koetterProcessConstraints_yBounded params
    (interpolationConstraints points params.multiplicity)
    (koetterInitialState params)
    (by
      simpa [koetterInitialState] using koetterInitialBasis_yBounded (F := F) params)

theorem koetterFinalBasis_weakLeading {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) :
    koetterBasisWeakLeading params
      (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis := by
  exact koetterProcessConstraints_weakLeading params
    (interpolationConstraints points params.multiplicity)
    (koetterInitialState params)
    (by
      simpa [koetterInitialState] using koetterInitialBasis_weakLeading (F := F) params)

theorem koetterFinalBasis_satisfies_constraints {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) :
    koetterBasisSatisfiesConstraints
      (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis
      (interpolationConstraints points params.multiplicity).toList := by
  let constraints := interpolationConstraints points params.multiplicity
  let initial := koetterInitialState (F := F) params
  have hbefore : koetterConstraintsLowerBefore constraints.toList := by
    rw [interpolationConstraints_toList_eq_list]
    exact interpolationConstraintsList_lowerBefore points params.multiplicity
  have hSat := koetterProcessConstraints_fold_satisfies params constraints.toList hbefore
    constraints.toList [] initial (by simp)
    (by intro c hc; simp at hc)
    (by intro c hc; simp at hc)
  simpa [constraints, initial, koetterProcessConstraints] using hSat

end GuruswamiSudan

end CompPoly
