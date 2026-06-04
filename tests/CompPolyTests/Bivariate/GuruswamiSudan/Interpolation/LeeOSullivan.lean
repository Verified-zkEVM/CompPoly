/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Core
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import CompPoly.Univariate.LagrangeArray
import Mathlib.Algebra.Field.ZMod

/-!
# Lee-O'Sullivan Guruswami-Sudan Interpolation Tests

Focused executable coverage for Lee-O'Sullivan setup, shifted-row construction,
and backend context assembly.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan
open CompPoly.GuruswamiSudan.LeeOSullivan

namespace GuruswamiSudan.Interpolation.LeeOSullivan

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def params : GSInterpParams :=
  { messageDegree := 2, multiplicity := 1, weightedDegreeBound := 2 }

private def lowParams : GSInterpParams :=
  { messageDegree := 1, multiplicity := 1, weightedDegreeBound := 0 }

private def points : Array (F3 × F3) :=
  #[(0, 0), (1, 1)]

private def points3 : Array (F3 × F3) :=
  #[(0, 1), (1, 2), (2, 1)]

private def lowPoints : Array (F3 × F3) :=
  #[(0, 0)]

private def duplicateXPoints : Array (F3 × F3) :=
  #[(0, 0), (0, 1)]

private def xs : Array F3 :=
  #[0, 1]

private def directV : CPolynomial.VanishingPolynomialContext F3 :=
  CPolynomial.VanishingPolynomialContext.direct

private def subproductV : CPolynomial.VanishingPolynomialContext F3 :=
  CPolynomial.VanishingPolynomialContext.subproduct CPolynomial.MulContext.naive

private def hornerE : CPolynomial.BatchEvalContext F3 :=
  CPolynomial.BatchEvalContext.horner F3

private def subproductE : CPolynomial.BatchEvalContext F3 :=
  CPolynomial.BatchEvalContext.subproduct F3
    CPolynomial.MulContext.naive CPolynomial.ModContext.remainderOnly

private def reducer : PolynomialMatrix.ShiftedRowReducerContext F3 :=
  PolynomialMatrix.muldersStorjohannReducerContext F3

private def leeContext : GSInterpContext F3 :=
  leeOSullivanInterpContext directV hornerE reducer

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

private def R : CPolynomial F3 :=
  CPolynomial.CLagrange.interpolateArray points

private def RCoefficient : CPolynomial F3 :=
  CPolynomial.interpolateCoefficientForm directV hornerE points

private def RSubproductCoefficient : CPolynomial F3 :=
  CPolynomial.interpolateCoefficientForm subproductV subproductE points

private def R3 : CPolynomial F3 :=
  CPolynomial.CLagrange.interpolateArray points3

private def R3Coefficient : CPolynomial F3 :=
  CPolynomial.interpolateCoefficientForm directV hornerE points3

private def GDirect : CPolynomial F3 :=
  directV.vanishingPolynomial xs

private def GSubproduct : CPolynomial F3 :=
  subproductV.vanishingPolynomial xs

private def zeroRow : PolynomialRow F3 :=
  #[0, 0]

private def weakPopovMatrix : PolynomialMatrix F3 :=
  #[
    #[CPolynomial.C (1 : F3), 0],
    #[0, CPolynomial.C (1 : F3)]
  ]

#guard interpolationYCap params == 2
#guard leeOSullivanWidth params == 3
#guard leeOSullivanShifts params == #[0, 1, 2]

#guard CPolynomial.eval (0 : F3) R == 0
#guard CPolynomial.eval (1 : F3) R == 1
#guard CPolynomial.eval (0 : F3) RCoefficient == 0
#guard CPolynomial.eval (1 : F3) RCoefficient == 1
#guard RCoefficient == R
#guard RSubproductCoefficient == R
#guard R3Coefficient == R3
#guard CPolynomial.eval (0 : F3) R3Coefficient == 1
#guard CPolynomial.eval (1 : F3) R3Coefficient == 2
#guard CPolynomial.eval (2 : F3) R3Coefficient == 1

#guard CPolynomial.eval (0 : F3) (CPolynomial.vanishingPolynomialArray xs) == 0
#guard CPolynomial.eval (1 : F3) (CPolynomial.vanishingPolynomialArray xs) == 0
#guard GDirect == CPolynomial.vanishingPolynomialArray xs
#guard GSubproduct == CPolynomial.vanishingPolynomialArray xs

#guard PolynomialMatrix.rowShiftedDegree? zeroRow #[0, 1] |>.isNone
#guard PolynomialMatrix.shiftedLeadingConflict? weakPopovMatrix #[0, 0] |>.isNone
#guard PolynomialMatrix.muldersStorjohannReduce weakPopovMatrix #[0, 0] == weakPopovMatrix

#guard (leeOSullivanBasisRows directV hornerE points params).size == leeOSullivanWidth params
#guard (leeOSullivanBasisRows directV hornerE points params).all
  (fun row ↦ row.size == leeOSullivanWidth params)

#guard leeOSullivanPositiveInterpolate directV hornerE reducer duplicateXPoints params == none

#guard (leeOSullivanInterpolate directV hornerE reducer points params).isSome
#guard match leeOSullivanInterpolate directV hornerE reducer points params with
  | none => false
  | some Q => interpolationWitnessIsValidBool points params Q

#guard (leeOSullivanInterpolate directV hornerE reducer lowPoints lowParams).isSome
#guard match leeOSullivanInterpolate directV hornerE reducer lowPoints lowParams with
  | none => false
  | some Q => interpolationWitnessIsValidBool lowPoints lowParams Q

#guard (gsCore points leeContext rootContext params).size <= 3
#guard (gsCore lowPoints leeContext rootContext lowParams).size <= 3

end GuruswamiSudan.Interpolation.LeeOSullivan

end CompPolyTests
