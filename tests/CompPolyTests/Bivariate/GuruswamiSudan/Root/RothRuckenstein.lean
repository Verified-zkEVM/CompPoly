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
abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

instance : Fact (Nat.Prime 5) :=
  ⟨by decide⟩

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private def fieldRoots : FieldRootBackend F3 :=
  linearOrEnumeratingFieldRootBackend F3 f3Elements

private def f5Ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F5 where
  q := 5
  finite := by infer_instance
  card_eq := by
    simp [F5, Nat.card_eq_fintype_card, ZMod.card]
  q_odd := by decide
  frobenius_fixed := by decide

private def f5FieldRoots : FieldRootBackend F5 :=
  oddFiniteFieldRootBackend F5 f5Ctx
    (CPolynomial.Roots.FiniteField.deterministicLinearFactorProductSplitter F5)

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

private def pXPlusOne : CPolynomial F5 :=
  CPolynomial.ofArray #[(1 : F5), 1]

private def pTwoXPlusTwo : CPolynomial F5 :=
  CPolynomial.ofArray #[(2 : F5), 2]

private def qTwoLinearYFactors : CBivariate F5 :=
  CBivariate.linearYFactor pXPlusOne * CBivariate.linearYFactor pTwoXPlusTwo

private def nonlinearInitialEquationRoots : Array (CPolynomial F5) :=
  rothRuckensteinRootsYDegreeLt f5FieldRoots qTwoLinearYFactors 2

#guard 2 < (initialCoefficientPolynomial qTwoLinearYFactors).val.size
#guard pXPlusOne ∈ nonlinearInitialEquationRoots.toList
#guard pTwoXPlusTwo ∈ nonlinearInitialEquationRoots.toList

end GuruswamiSudan.Root.RothRuckenstein

end CompPolyTests
