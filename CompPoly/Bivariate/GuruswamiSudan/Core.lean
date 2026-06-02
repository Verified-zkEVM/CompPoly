/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation
import CompPoly.Bivariate.GuruswamiSudan.Root

/-!
# Guruswami-Sudan Core

End-to-end executable CompPoly Guruswami-Sudan polynomial core, following the
interpolation-and-root-finding decomposition of [GS99].

## References

* [Guruswami, V., and Sudan, M., *Improved decoding of Reed-Solomon and
    algebraic-geometry codes*][GS99]
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Run interpolation, then bounded-degree root finding, using explicit backends. -/
def gsCore {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (points : Array (Prod F F))
    (interpContext : GSInterpContext F)
    (rootContext : GSRootContext F)
    (params : GSInterpParams) : Array (CPolynomial F) :=
  match interpContext.interpolate points params with
  | none => #[]
  | some Q => rootContext.rootsYDegreeLt Q params.messageDegree

end GuruswamiSudan

end CompPoly
