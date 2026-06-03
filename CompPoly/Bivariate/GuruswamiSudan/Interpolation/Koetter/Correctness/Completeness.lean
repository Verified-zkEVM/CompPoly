/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Transport

/-!
# Koetter Interpolation Completeness

Completeness theorems and public context wrapper for direct Koetter interpolation.
-/

namespace CompPoly

namespace GuruswamiSudan

theorem koetterFinalBasis_entry_moduleFacts {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) {idx : Nat}
    (hidx :
      idx <
        (koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis.size) :
    koetterBasisGeneratedBy (koetterInitialBasis params)
      ((koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis.getD idx 0) ∧
    (∀ i j, koetterYCap params < j →
      CBivariate.coeff
        ((koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis.getD idx 0) i j = 0) ∧
    (∀ constraint,
      constraint ∈ (interpolationConstraints points params.multiplicity).toList →
      koetterDiscrepancy constraint
        ((koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis.getD idx 0) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact koetterFinalBasis_entries_generatedBy_initial points params idx hidx
  · intro i j hj
    exact koetterFinalBasis_yBounded points params idx hidx i j hj
  · intro constraint hmem
    exact koetterFinalBasis_satisfies_constraints points params constraint hmem idx hidx

/-- Completeness for raw Koetter interpolation when `messageDegree > 1`.

If any valid witness exists in the finite `Y`-bounded search space, the raw
Koetter final selection returns one. -/
theorem koetterRawInterpolate_complete_of_messageDegree_gt_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    (hMessage : ¬ params.messageDegree ≤ 1) :
    (exists Q, ValidInterpolationWitness points params Q) →
      exists Q, koetterRawInterpolate points params = some Q := by
  intro hExists
  by_cases hMultiplicity : params.multiplicity = 0
  · apply koetterRawInterpolate_some_of_exists_final_entry
    have hconstraints :
        (interpolationConstraints points params.multiplicity).toList = [] := by
      rw [hMultiplicity, interpolationConstraints_toList_eq_list]
      simp [interpolationConstraintsList]
    have hbasis :
        (koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis =
          (koetterInitialState params).basis := by
      unfold koetterProcessConstraints
      rw [← Array.foldl_toList, hconstraints]
      simp
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [hbasis]
      change 0 < (koetterInitialBasis (F := F) params).size
      rw [koetterInitialBasis_size]
      omega
    · rw [hbasis]
      change (koetterInitialBasis (F := F) params).getD 0 0 ≠ 0
      exact koetterInitialBasis_entry_ne_zero params (by omega)
    · rw [hbasis]
      change CBivariate.natWeightedDegree
        ((koetterInitialBasis (F := F) params).getD 0 0) 1 (yWeight params) ≤
          params.weightedDegreeBound
      exact koetterInitialBasis_entry_weightedDegree_le params (by omega)
  apply koetterRawInterpolate_some_of_exists_final_entry
  rcases hExists with ⟨Q, hQ⟩
  have hWitnessYCap : ∀ j, koetterYCap params < j → Q.val.coeff j = 0 := by
    intro j hj
    exact validWitness_coeffY_eq_zero_of_yCap_lt hMessage hQ hj
  have hWitnessFiniteExpansion :
      koetterFiniteYExpansion Q (koetterYCap params) = Q :=
    koetterFiniteYExpansion_eq_of_yCap hWitnessYCap
  have hWitnessInitialSpan :
      koetterBasisSpanContains (koetterInitialBasis params) Q :=
    koetterInitialBasis_spans_of_yCap hWitnessYCap
  have hWitnessBoundedCoeff :
      ∃ i j,
        j ≤ koetterYCap params ∧
          CBivariate.coeff Q i j ≠ 0 ∧
            i + yWeight params * j ≤ params.weightedDegreeBound :=
    validWitness_exists_bounded_coeff_within_yCap hMessage hQ
  have hWitnessConstraints :
      ∀ constraint, constraint ∈ (interpolationConstraints points params.multiplicity).toList →
        koetterDiscrepancy constraint Q = 0 := by
    intro constraint hmem
    exact validWitness_discrepancy_eq_zero_of_constraint_mem hQ hmem
  have hWitnessFinalSpan :
      koetterBasisSpanContains
        (koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis Q :=
    koetterFinalBasis_span_contains points params hWitnessInitialSpan hWitnessConstraints
  have hFinalNonzeroEntry :
      ∃ idx,
        idx <
          (koetterProcessConstraints params
            (interpolationConstraints points params.multiplicity)
            (koetterInitialState params)).basis.size ∧
          (koetterProcessConstraints params
            (interpolationConstraints points params.multiplicity)
            (koetterInitialState params)).basis.getD idx 0 ≠ 0 :=
    exists_nonzero_entry_of_koetterBasisSpanContains
      ((koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis)
      hWitnessFinalSpan hQ.1
  have hFinalGenerated := koetterFinalBasis_entries_generatedBy_initial points params
  have hFinalYBounded := koetterFinalBasis_yBounded points params
  have hFinalSat := koetterFinalBasis_satisfies_constraints points params
  have hFinalWeak := koetterFinalBasis_weakLeading points params
  rcases exists_basis_entry_natWeightedDegree_le_of_weakLeading_span
      (params := params)
      (basis :=
        (koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis)
      (Q := Q) hFinalWeak hWitnessFinalSpan hQ.1 with
    ⟨idx, hi, hne, hdegLeQ⟩
  refine ⟨idx, hi, hne, ?_⟩
  exact le_trans hdegLeQ hQ.2.1

/-- Completeness for the public Koetter interpolation operation.

For `messageDegree > 1` this uses the direct Koetter completeness theorem,
not a dense-backend fallback. -/
theorem koetterInterpolate_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} :
    (exists Q, ValidInterpolationWitness points params Q) →
      exists Q, koetterInterpolate points params = some Q := by
  intro hExists
  unfold koetterInterpolate
  by_cases hLow : params.messageDegree ≤ 1
  · refine ⟨lowMessageDegreeInterpolation points params.multiplicity, ?_⟩
    simp [hLow]
  · simp [hLow]
    exact koetterRawInterpolate_complete_of_messageDegree_gt_one
      (F := F) (points := points) (params := params) hLow hExists

/-- Public Koetter interpolation context.

The executable operation has no dense interpolation fallback. Its completeness
field uses the raw Koetter theorem for `messageDegree > 1` and the constructive
low-message branch for `messageDegree ≤ 1`. -/
def koetterInterpContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] : GSInterpContext F where
  interpolate := koetterInterpolate
  sound := by
    intro points params Q h
    exact koetterInterpolate_sound h
  complete := by
    intro points params _hdistinct hExists
    exact koetterInterpolate_complete hExists

/-- Public Koetter interpolation backend soundness. -/
theorem koetterInterpContext_correct (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params Q,
      (koetterInterpContext F).interpolate points params = some Q →
        ValidInterpolationWitness points params Q :=
  (koetterInterpContext F).sound

/-- Public Koetter interpolation backend completeness. -/
theorem koetterInterpContext_complete (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params,
      DistinctXCoordinates points →
      (exists Q, ValidInterpolationWitness points params Q) →
        exists Q, (koetterInterpContext F).interpolate points params = some Q :=
  (koetterInterpContext F).complete

end GuruswamiSudan

end CompPoly
