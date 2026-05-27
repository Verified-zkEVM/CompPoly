/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Compose
import Mathlib.Algebra.Field.ZMod

/-!
# Guruswami-Sudan Composition Tests

Regression coverage for `CBivariate.composeY`.
-/

namespace CompPolyTests

open CompPoly

namespace GuruswamiSudan.Compose

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def q : CBivariate F3 :=
  CBivariate.Y + CBivariate.monomialXY 1 0 2

private def pX : CPolynomial F3 :=
  CPolynomial.monomial 1 1

#guard CBivariate.composeY q pX == 0

end GuruswamiSudan.Compose

end CompPolyTests
