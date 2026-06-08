/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Hasse
import Mathlib.Algebra.Field.ZMod

/-!
# Guruswami-Sudan Hasse Tests

Regression coverage for executable Hasse derivative helpers.
-/

namespace CompPolyTests

open CompPoly

namespace GuruswamiSudan.Hasse

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def q : CBivariate F3 :=
  CBivariate.monomialXY 2 1 1

#guard CBivariate.coeff (CBivariate.hasseDerivative 1 0 q) 1 1 == (2 : F3)
#guard CBivariate.hasseDerivativeEval 1 0 2 1 q == (1 : F3)

end GuruswamiSudan.Hasse

end CompPolyTests
