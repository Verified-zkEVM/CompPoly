/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic
import CompPoly.LinearAlgebra.PolynomialMatrix.ShiftedReduction

/-!
# Executable Lee-O'Sullivan Interpolation
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

private structure RowChoice (F : Type*) [Zero F] where
  index : Nat
  row : PolynomialRow F
  degree : Nat

private def betterRowChoice [Zero F] (candidate current : RowChoice F) : Bool :=
  candidate.degree < current.degree ||
    (candidate.degree == current.degree && candidate.index < current.index)

/-- Select a nonzero row of least shifted degree from a reduced matrix. -/
def leastShiftedDegreeRow? (M : PolynomialMatrix F) (shift : Array Nat) :
    Option (PolynomialRow F) :=
  let choice? :=
    (List.range M.size).foldl
      (fun best i ↦
        let row := M.getD i #[]
        match rowShiftedDegree? row shift with
        | none => best
        | some degree =>
            let candidate : RowChoice F := { index := i, row := row, degree := degree }
            match best with
            | none => some candidate
            | some current =>
                if betterRowChoice candidate current then some candidate else best)
      none
  choice?.map fun choice ↦ choice.row

/-- Normalize a row-derived candidate using the shared interpolation vector policy. -/
def normalizeLeeCandidate? (params : GSInterpParams) (Q : CBivariate F) :
    Option (CBivariate F) :=
  normalizeInterpolationPolynomial? params
    (interpolationCoefficientVector params Q)

/-- Positive-`Y`-weight Lee-O'Sullivan interpolation branch. -/
def leeOSullivanPositiveInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if distinctXCoordinatesBool points then
    let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
    let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
    let basis := leeOSullivanBasisRowsWithRG R G params
    let shift := leeOSullivanShifts params
    let reduced := reducer.reduce basis shift
    match leastShiftedDegreeRow? reduced shift with
    | none => none
    | some row =>
        match rowShiftedDegree? row shift with
        | none => none
        | some degree =>
            if degree ≤ params.weightedDegreeBound then
              let rawQ := CBivariate.ofCoeffRow row
              match normalizeLeeCandidate? params rawQ with
              | none => none
              | some Q => some Q
            else
              none
  else
    none

/-- Lee-O'Sullivan interpolation with the shared low-message branch. -/
def leeOSullivanInterpolate
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (reducer : ShiftedRowReducerContext F)
    (points : Array (F × F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    leeOSullivanPositiveInterpolate V E reducer points params

end LeeOSullivan

end GuruswamiSudan

end CompPoly
