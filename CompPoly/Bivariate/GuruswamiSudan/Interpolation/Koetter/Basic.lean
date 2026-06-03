/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic

/-!
# Koetter Guruswami-Sudan Interpolation Basics

Small executable helpers shared by the direct `CBivariate` Koetter
interpolation implementation.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Finite `Y` cap used by the positive-`Y`-weight Koetter branch. -/
def koetterYCap (params : GSInterpParams) : Nat :=
  params.weightedDegreeBound / yWeight params

/-- The monic linear factor `X - x` as a bivariate polynomial. -/
def CBivariate.linearXFactor {R : Type*}
    [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    CBivariate R :=
  (CBivariate.X : CBivariate R) - CBivariate.CC x

/-- Koetter basis state, stored directly as bivariate polynomials. -/
structure KoetterState (F : Type*) [Zero F] where
  basis : Array (CBivariate F)

/-- Discrepancy of one basis polynomial at one packed Hasse constraint. -/
def koetterDiscrepancy {F : Type*} [Semiring F]
    (constraint : InterpolationConstraint F) (Q : CBivariate F) : F :=
  CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder
    constraint.x constraint.y Q

/-- Pivot data selected for one Koetter update. -/
structure KoetterPivot (F : Type*) where
  index : Nat
  discrepancy : F
  weightedDegree : Nat

/-- Stable weighted-order comparison for pivot and final-candidate selection. -/
def koetterPivotBetter {F : Type*} (candidate current : KoetterPivot F) : Bool :=
  candidate.weightedDegree < current.weightedDegree ||
    (candidate.weightedDegree == current.weightedDegree && candidate.index < current.index)

end GuruswamiSudan

end CompPoly
