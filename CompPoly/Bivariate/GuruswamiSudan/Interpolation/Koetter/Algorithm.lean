/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Basic

/-!
# Direct Koetter Guruswami-Sudan Interpolation

Executable direct-`CBivariate` Koetter interpolation. This is an additional
interpolation implementation alongside dense linear-system interpolation. The
public `koetterInterpolate` operation uses the existing low-message-degree
constructive branch, and otherwise returns the raw direct Koetter result.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Initial Koetter basis `1, Y, ..., Y^l`, where `l = koetterYCap params`. -/
def koetterInitialBasis {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) : Array (CBivariate F) :=
  (List.range (koetterYCap params + 1)).map
    (fun j ↦ CBivariate.monomialXY 0 j 1) |>.toArray

/-- Initial Koetter state. -/
def koetterInitialState {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) : KoetterState F :=
  { basis := koetterInitialBasis params }

/-- Select the nonzero-discrepancy pivot of least weighted degree. -/
def koetterSelectPivot {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) : Option (KoetterPivot F) :=
  (List.range basis.size).foldl
    (fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then
        best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best)
    none

/-- One basis entry after a Koetter pivot update, using the original basis. -/
def koetterUpdatedEntry {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (idx : Nat) : CBivariate F :=
  let current := basis.getD idx 0
  let pivotPoly := basis.getD pivot.index 0
  if idx == pivot.index then
    CBivariate.linearXFactor constraint.x * current
  else
    let delta := koetterDiscrepancy constraint current
    if delta == 0 then
      current
    else
      current - CBivariate.CC (delta / pivot.discrepancy) * pivotPoly

/-- Apply one Koetter pivot update to every basis element. -/
def koetterUpdateBasis {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) : Array (CBivariate F) :=
  (List.range basis.size).foldl
    (fun out idx ↦
      out.setIfInBounds idx (koetterUpdatedEntry constraint basis pivot idx))
    basis

/-- Process one Hasse constraint. If all discrepancies vanish, the state is unchanged. -/
def koetterProcessConstraint {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F) : KoetterState F :=
  match koetterSelectPivot params constraint state.basis with
  | none => state
  | some pivot => { basis := koetterUpdateBasis constraint state.basis pivot }

/-- Process an array of Hasse constraints in order. -/
def koetterProcessConstraints {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraints : Array (InterpolationConstraint F))
    (state : KoetterState F) : KoetterState F :=
  constraints.foldl
    (fun state constraint ↦ koetterProcessConstraint params constraint state)
    state

/-- Select the nonzero final basis element of least weighted degree. -/
def koetterSelectFinal? {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (basis : Array (CBivariate F)) :
    Option (CBivariate F) :=
  let best := (List.range basis.size).foldl
    (fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then
        best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best)
    none
  match best with
  | none => none
  | some pivot =>
      let Q := basis.getD pivot.index 0
      if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
        some Q
      else
        none

/-- Raw positive-message Koetter interpolation. -/
def koetterRawInterpolate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  let constraints := interpolationConstraints points params.multiplicity
  let finalState := koetterProcessConstraints params constraints
    (koetterInitialState params)
  koetterSelectFinal? params finalState.basis

/-- Koetter interpolation with the existing low-message branch and raw direct
positive-message Koetter pass. -/
def koetterInterpolate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    koetterRawInterpolate points params

end GuruswamiSudan

end CompPoly
