/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Koetter Guruswami-Sudan Interpolation Tests

Focused executable coverage for the direct `CBivariate` Koetter interpolation
path.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Interpolation.Koetter

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

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private theorem f3Elements_complete : ContainsAllFieldElements f3Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def fieldRoots : FieldRootContext F3 :=
  enumeratingFieldRootContext F3 f3Elements f3Elements_complete

private def rootContext : GSRootContext F3 :=
  rothRuckensteinRootContext F3 fieldRoots

private def initialBasis : Array (CBivariate F3) :=
  koetterInitialBasis params

private def xDerivativeConstraint : InterpolationConstraint F3 :=
  { x := 1, y := 1, xOrder := 1, yOrder := 0 }

private def evalConstraint : InterpolationConstraint F3 :=
  { x := 1, y := 1, xOrder := 0, yOrder := 0 }

private def unchangedState : KoetterState F3 :=
  koetterProcessConstraint params xDerivativeConstraint (koetterInitialState params)

private def oneStepState : KoetterState F3 :=
  koetterProcessConstraint params evalConstraint (koetterInitialState params)

#guard koetterYCap params == 2
#guard initialBasis.size == 3
#guard initialBasis.getD 2 0 == CBivariate.monomialXY 0 2 (1 : F3)
#guard unchangedState.basis == initialBasis
#guard oneStepState.basis.all fun Q ↦ koetterDiscrepancy evalConstraint Q == 0

#guard (koetterInterpolate lowPoints lowParams).isSome
#guard match koetterInterpolate lowPoints lowParams with
  | none => false
  | some Q => interpolationWitnessIsValidBool lowPoints lowParams Q

#guard (koetterInterpolate points params).isSome
#guard match koetterInterpolate points params with
  | none => false
  | some Q => interpolationWitnessIsValidBool points params Q

#guard ((koetterInterpContext F3).interpolate points params).isSome

#guard match denseInterpolate points params, koetterInterpolate points params with
  | some denseQ, some koetterQ =>
      interpolationWitnessIsValidBool points params denseQ &&
        interpolationWitnessIsValidBool points params koetterQ
  | _, _ => false

#guard (gsCore points (koetterInterpContext F3) rootContext params).size <= 3

end GuruswamiSudan.Interpolation.Koetter

end CompPolyTests
