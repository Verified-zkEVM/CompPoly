/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import Mathlib.Algebra.Field.ZMod

/-!
# Guruswami-Sudan Core Tests

End-to-end smoke tests for the backend-parametric CompPoly Guruswami-Sudan core.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Core

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def params : GSInterpParams :=
  { messageDegree := 2, multiplicity := 1, weightedDegreeBound := 2 }

private def points : Array (Prod F3 F3) :=
  #[(0, 0), (1, 1)]

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private theorem f3Elements_complete : ContainsAllFieldElements f3Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def fieldRoots : FieldRootContext F3 :=
  enumeratingFieldRootContext F3 f3Elements f3Elements_complete

#guard (gsCore points (denseInterpContext F3)
  (rothRuckensteinRootContext F3 fieldRoots) params).size <= 3

end GuruswamiSudan.Core

end CompPolyTests
