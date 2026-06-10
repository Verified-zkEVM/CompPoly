/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Algorithm

/-!
# Approximant-Basis Interpolation Correctness Surface

Theorem statements for the modular-equation reduction and the public
`GSInterpContext` boundary.  Proof bodies are intentionally explicit theorem
debt while the executable backend and benchmark evidence are developed.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace ApproximantBasis

open PolynomialMatrix
open PolynomialMatrix.Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- The executable GS modular row predicate is equivalent to packed
multiplicity constraints for the bivariate coefficient-row view. -/
theorem gsModularEquation_row_iff_multiplicity
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (modCtx : CPolynomial.ModContext F)
    (mulCtx : CPolynomial.MulContext F)
    (points : Array (F × F)) (params : GSInterpParams)
    (row : PolynomialRow F) :
    let data := buildGSModularData V E mulCtx modCtx points params
    rowSatisfiesModularBool mulCtx modCtx row data.matrix data.moduli = true ↔
      CBivariate.satisfiesMultiplicityConstraintsBool
        (CBivariate.ofCoeffRow row) points params.multiplicity = true := by
  sorry

/-- Soundness for executable approximant-basis interpolation. -/
theorem approximantBasisInterpolate_sound
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h :
      approximantBasisInterpolate V E solver points params = some Q) :
    ValidInterpolationWitness points params Q := by
  sorry

/-- Completeness for executable approximant-basis interpolation on distinct
input `x`-coordinates. -/
theorem approximantBasisInterpolate_complete
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (points : Array (F × F)) (params : GSInterpParams)
    (hdistinct : DistinctXCoordinates points)
    (hexists : ∃ Q, ValidInterpolationWitness points params Q) :
    ∃ Q, approximantBasisInterpolate V E solver points params = some Q := by
  sorry

/-- Public approximant-basis interpolation backend context. -/
def approximantBasisInterpContext
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F) : GSInterpContext F where
  interpolate := approximantBasisInterpolate V E solver
  sound := by
    intro points params Q h
    exact approximantBasisInterpolate_sound V E solver h
  complete := by
    intro points params hdistinct hexists
    exact approximantBasisInterpolate_complete V E solver points params hdistinct hexists

end ApproximantBasis

end GuruswamiSudan

end CompPoly
