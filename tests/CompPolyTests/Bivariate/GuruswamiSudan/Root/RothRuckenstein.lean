/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Roth-Ruckenstein Root Tests

Regression coverage for the Roth-Ruckenstein root backend.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Root.RothRuckenstein

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private def fieldRoots : FieldRootBackend F3 :=
  linearOrEnumeratingFieldRootBackend F3 f3Elements

private def qYMinusX : CBivariate F3 :=
  CBivariate.Y + CBivariate.monomialXY 1 0 2

private def pX : CPolynomial F3 :=
  CPolynomial.monomial 1 1

private def qXTimesYMinusOne : CBivariate F3 :=
  CBivariate.monomialXY 1 1 1 + CBivariate.monomialXY 1 0 2

private def pOne : CPolynomial F3 :=
  CPolynomial.C 1

#guard pX ∈ (rothRuckensteinRootsYDegreeLt fieldRoots qYMinusX 2).toList
#guard pX ∈
  ((rothRuckensteinRootBackend F3 fieldRoots).rootsYDegreeLt qYMinusX 2).toList
#guard pOne ∈ (rothRuckensteinRootsYDegreeLt fieldRoots qXTimesYMinusOne 2).toList
#guard (rothRuckensteinRootsYDegreeLt fieldRoots (0 : CBivariate F3) 2).isEmpty

end GuruswamiSudan.Root.RothRuckenstein

end CompPolyTests
