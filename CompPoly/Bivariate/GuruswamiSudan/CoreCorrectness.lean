/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Core

/-!
# Guruswami-Sudan Core Correctness

Public correctness theorem for the backend-parametric CompPoly
Guruswami-Sudan core.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Every polynomial returned by `gsCore` is a bounded-degree root of the
interpolation polynomial produced by the interpolation backend. -/
theorem gsCore_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams}
    {p : CPolynomial F}
    (hp : p ∈ (gsCore points interpBackend rootBackend params).toList) :
    exists Q,
      interpBackend.interpolate points params = some Q ∧
        Q ≠ 0 ∧
          CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound ∧
            CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity ∧
              degreeLt p params.messageDegree ∧
                CBivariate.composeY Q p = 0 := by
  sorry

end GuruswamiSudan

end CompPoly
