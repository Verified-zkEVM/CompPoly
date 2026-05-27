/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm

/-!
# Dense Guruswami-Sudan Interpolation Correctness

Correctness contracts for the dense interpolation backend.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Matrix construction soundness for one returned interpolation witness. -/
theorem denseInterpolate_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {kernelBackend : LinearKernelBackend F}
    {points : Array (Prod F F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : denseInterpolateWithKernel kernelBackend points params = some Q) :
    Q ≠ 0 ∧
      CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound ∧
        CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity := by
  sorry

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
