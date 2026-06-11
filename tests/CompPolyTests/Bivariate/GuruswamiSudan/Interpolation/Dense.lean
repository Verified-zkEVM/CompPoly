/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Dense Guruswami-Sudan Interpolation Tests

Regression coverage for dense interpolation matrix construction, witness
selection, and the low-message branch.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Interpolation.Dense

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def params : GSInterpParams :=
  { messageDegree := 2, multiplicity := 1, weightedDegreeBound := 2 }

private def points : Array (Prod F3 F3) :=
  #[(0, 0), (1, 1)]

private def lowParams : GSInterpParams :=
  { messageDegree := 1, multiplicity := 1, weightedDegreeBound := 0 }

private def lowPoints : Array (Prod F3 F3) :=
  #[(0, 0)]

#guard (interpolationMatrix points params).rows == 2
#guard (interpolationMonomials params).size == 6
#guard (denseInterpolate points params).isSome

#guard (interpolationMonomials lowParams).size == 1
#guard (denseInterpolateWithBasisAndKernel (denseLinearKernelContext F3)
  (interpolationMonomials lowParams) lowPoints lowParams).isNone
#guard (denseInterpolate lowPoints lowParams).isSome

end GuruswamiSudan.Interpolation.Dense

end CompPolyTests
