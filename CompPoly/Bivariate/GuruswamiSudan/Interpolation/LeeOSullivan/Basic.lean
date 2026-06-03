/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.CoeffRows
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness
import CompPoly.Univariate.CoefficientInterpolation
import CompPoly.Univariate.Vanishing

/-!
# Lee-O'Sullivan Interpolation Basics
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Finite `Y` cap used by positive-`Y`-weight interpolation backends. -/
def interpolationYCap (params : GSInterpParams) : Nat :=
  params.weightedDegreeBound / yWeight params

/-- Number of coefficient columns in the Lee-O'Sullivan module basis. -/
def leeOSullivanWidth (params : GSInterpParams) : Nat :=
  interpolationYCap params + 1

/-- Lee-O'Sullivan shifted-degree shifts, `shift[j] = j * yWeight params`. -/
def leeOSullivanShifts (params : GSInterpParams) : Array Nat :=
  CBivariate.weightedDegreeShift (yWeight params) (leeOSullivanWidth params)

/-- Uniform exponent `t_i = min i s` in the Lee-O'Sullivan basis. -/
def leeOSullivanT (params : GSInterpParams) (i : Nat) : Nat :=
  min i params.multiplicity

/-- Executable duplicate-`x` detector for packed points. -/
def distinctXCoordinatesBool {F : Type*} [BEq F] (points : Array (F × F)) : Bool :=
  let rec go : List (F × F) → Bool
    | [] => true
    | point :: rest =>
        !(rest.any fun other ↦ other.1 == point.1) && go rest
  go points.toList

/-- The Lee-O'Sullivan basis polynomial `P_i`. -/
def leeOSullivanBasisPolynomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (R G : CPolynomial F) (params : GSInterpParams) (i : Nat) : CBivariate F :=
  let t := leeOSullivanT params i
  (CBivariate.Y : CBivariate F) ^ (i - t) *
    (CBivariate.linearYFactor R) ^ t *
      (CBivariate.ofYConstant G) ^ (params.multiplicity - t)

/-- Lee-O'Sullivan basis rows from already-built `R` and `G`. -/
def leeOSullivanBasisRowsWithRG {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (R G : CPolynomial F) (params : GSInterpParams) : PolynomialMatrix F :=
  let width := leeOSullivanWidth params
  (List.range width).map
    (fun i ↦ CBivariate.toCoeffRow width
      (leeOSullivanBasisPolynomial R G params i)) |>.toArray

/-- Lee-O'Sullivan basis rows from packed points. -/
def leeOSullivanBasisRows {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) (params : GSInterpParams) : PolynomialMatrix F :=
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
  leeOSullivanBasisRowsWithRG R G params

end GuruswamiSudan

end CompPoly
