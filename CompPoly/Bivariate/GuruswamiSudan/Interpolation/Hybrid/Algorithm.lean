/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Algorithm

/-!
# Hybrid Guruswami-Sudan Interpolation

Output-sensitive interpolation backend combining the adaptive Lee-O'Sullivan
route with the order-driven approximant-basis route, following the ski-rental
analysis in `gs-interpolation-complexity-analysis.md`.

The Mulders-Storjohann reduction of the Lee-O'Sullivan basis terminates after
a number of steps that vanishes on codewords and scales with the distance of
the received word from the code, while the approximant-basis backend costs
the same on every input. The hybrid runs the reduction with a calibrated step
budget `B` as fuel; if the budget is exhausted before the basis is
conflict-free, it falls back to the approximant solver, so the total cost is
within a constant factor of the cheaper route on every input.

The budget is the entire fuel policy: the reduction loop stops by itself as
soon as the basis is conflict-free, so unused fuel is free and any cap below
`B` could only trigger premature fallback. (In particular the degree excess
`Δ` of `gs-interpolation-complexity-analysis.md` is *not* a usable cap: the
implementation's step count includes leading-position moves that leave the
shifted-degree sum unchanged, so reductions routinely need more than `Δ`
steps.)

The dispatch affects performance only: both branches are complete verified
interpolators, and `Interpolation/Hybrid/Correctness.lean` shows the hybrid
result always coincides with one of them.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace Hybrid

open PolynomialMatrix
open PolynomialMatrix.Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- Positive-`Y`-weight hybrid interpolation branch: reduce the
Lee-O'Sullivan basis with the budgeted fuel and keep the result when it
reached shifted weak Popov form (no leading conflict remains), otherwise fall
back to the approximant-basis solver. -/
def hybridPositiveInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (budget : GSInterpParams → Nat)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if distinctXCoordinatesBool points then
    let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
    let basis := leeOSullivanBasisRowsWithRG R G params
    let shift := leeOSullivanShifts params
    let reduced := muldersStorjohannReduceWithFuelFast (budget params) basis shift
    match cachedLeadingConflict? (rowLeadingPositions reduced shift) with
    | some _ =>
        ApproximantBasis.approximantBasisPositiveInterpolate V E solver
          points params
    | none =>
        match LeeOSullivan.leastShiftedDegreeRow? reduced shift with
        | none => none
        | some row =>
            match rowShiftedDegree? row shift with
            | none => none
            | some degree =>
                if degree ≤ params.weightedDegreeBound then
                  let rawQ := CBivariate.ofCoeffRow row
                  match LeeOSullivan.normalizeLeeCandidate? params rawQ with
                  | none => none
                  | some Q => some Q
                else
                  none
  else
    none

/-- Hybrid interpolation with the shared low-message branch. -/
def hybridInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (budget : GSInterpParams → Nat)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    hybridPositiveInterpolate V E solver budget points params

end Hybrid

end GuruswamiSudan

end CompPoly
