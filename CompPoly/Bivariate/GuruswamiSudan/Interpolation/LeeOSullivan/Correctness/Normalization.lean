/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Common
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness

/-!
# Lee-O'Sullivan Candidate Normalization

Soundness and existence facts for normalizing raw Lee-O'Sullivan candidates.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- Normalizing a bounded raw Lee candidate preserves the interpolation witness
contract when the raw candidate already satisfies the multiplicity constraints. -/
theorem normalizeLeeCandidate?_sound_of_raw
    {points : Array (F × F)} {params : GSInterpParams}
    {rawQ Q : CBivariate F}
    (hHigh : ¬ params.messageDegree ≤ 1)
    (hdeg :
      CBivariate.natWeightedDegree rawQ 1 (yWeight params) ≤
        params.weightedDegreeBound)
    (hmult :
      CBivariate.SatisfiesMultiplicityConstraints rawQ points params.multiplicity)
    (hnorm : normalizeLeeCandidate? params rawQ = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold normalizeLeeCandidate? normalizeInterpolationPolynomial?
    normalizeInterpolationPolynomialOnBasis? at hnorm
  cases hn : normalizeVector? (interpolationCoefficientVector params rawQ) with
  | none =>
      rw [hn] at hnorm
      contradiction
  | some norm =>
      rw [hn] at hnorm
      cases hnorm
      let basis := interpolationMonomials params
      have hcomplete :
          ∀ i j, CBivariate.coeff rawQ i j ≠ 0 →
            ({ xDegree := i, yDegree := j } : CBivariate.Monomial) ∈ basis.toList := by
        intro i j hcoeff
        exact weightedDegreeBasis_complete_of_messageDegree_gt_one
          (params := params) hHigh hdeg i j hcoeff
      have hrawPoly :
          interpolationPolynomialOnBasis basis
              (interpolationCoefficientVectorOnBasis basis rawQ) = rawQ := by
        exact interpolationPolynomialOnBasis_eq_of_complete
          (basis := basis) (Q := rawQ)
          (CBivariate.monomialsWeightedDegreeLE_nodup 1 (yWeight params)
            params.weightedDegreeBound)
          hcomplete
      have hsol :
          DenseMatrix.IsHomogeneousSolution
            (interpolationMatrixOnBasis basis points params)
            (interpolationCoefficientVectorOnBasis basis rawQ) := by
        exact interpolationCoefficientVectorOnBasis_solution_of_satisfies
          (basis := basis) (Q := rawQ) hrawPoly hmult
      rcases normalizeVector?_some_data hn with
        ⟨pivot, hpivot, _hpivotNe, hnormEq, _hsize, hpivotOne⟩
      have hpivotBasis : pivot < basis.size := by
        simpa [basis, interpolationCoefficientVector,
          interpolationCoefficientVectorOnBasis_size] using hpivot
      have hnormPivotNe : norm.getD pivot 0 ≠ 0 := by
        rw [hpivotOne]
        exact one_ne_zero
      refine ⟨?_, ?_, ?_⟩
      · apply CBivariate.ofMonomialCoeffs_ne_zero_of_coeff_getD_ne_zero
        · exact CBivariate.monomialsWeightedDegreeLE_nodup 1 (yWeight params)
            params.weightedDegreeBound
        · exact hpivotBasis
        · exact hnormPivotNe
      · exact interpolationPolynomialOnBasis_weightedDegree_le
          basis params norm (weightedDegreeBasis_sound params)
      · have hmultQ :
            CBivariate.SatisfiesMultiplicityConstraints
              (interpolationPolynomialOnBasis basis norm) points params.multiplicity := by
          apply interpolationPolynomialOnBasis_satisfies_of_solution
          rw [hnormEq]
          exact isHomogeneousSolution_map_div
            ((interpolationCoefficientVectorOnBasis basis rawQ).getD pivot 0)
            hsol
        exact (CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity
          (interpolationPolynomialOnBasis basis norm) points params.multiplicity).1 hmultQ

/-- A nonzero bounded raw Lee candidate can be normalized by the shared
coefficient-vector policy. -/
theorem normalizeLeeCandidate?_some_of_raw
    {params : GSInterpParams} {rawQ : CBivariate F}
    (hHigh : ¬ params.messageDegree ≤ 1)
    (hne : rawQ ≠ 0)
    (hdeg :
      CBivariate.natWeightedDegree rawQ 1 (yWeight params) ≤
        params.weightedDegreeBound) :
    ∃ Q, normalizeLeeCandidate? params rawQ = some Q := by
  let basis := interpolationMonomials params
  have hcomplete :
      ∀ i j, CBivariate.coeff rawQ i j ≠ 0 →
        ({ xDegree := i, yDegree := j } : CBivariate.Monomial) ∈ basis.toList := by
    intro i j hcoeff
    exact weightedDegreeBasis_complete_of_messageDegree_gt_one
      (params := params) hHigh hdeg i j hcoeff
  have hnz :
      DenseMatrix.NonzeroVector
        (interpolationCoefficientVectorOnBasis basis rawQ) :=
    interpolationCoefficientVectorOnBasis_nonzero_of_complete hne hcomplete
  rcases normalizeVector?_some_of_nonzero hnz with ⟨norm, hnorm⟩
  refine ⟨interpolationPolynomialOnBasis basis norm, ?_⟩
  simp [normalizeLeeCandidate?, normalizeInterpolationPolynomial?,
    normalizeInterpolationPolynomialOnBasis?, interpolationCoefficientVector,
    basis, hnorm]

end LeeOSullivan

end GuruswamiSudan

end CompPoly
