/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic

/-!
# Dense Guruswami-Sudan Interpolation

Executable interpolation backend. In the ordinary positive-`Y`-weight case it
builds a Hasse-constraint matrix, computes one homogeneous-kernel witness, and
normalizes it. In the low-message case it returns an explicit product witness.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Constructive interpolation witness for the `messageDegree ≤ 1` GS range. -/
def lowMessageDegreeInterpolation {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (Prod F F)) (multiplicity : Nat) : CBivariate F :=
  points.toList.foldl
    (fun Q point =>
      Q * (CBivariate.linearYFactor (CPolynomial.C point.2)) ^ multiplicity)
    1

/-- Dense interpolation over an explicitly supplied finite monomial basis. -/
def denseInterpolateWithBasisAndKernel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (kernelBackend : LinearKernelBackend F)
    (basis : Array CBivariate.Monomial)
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  let matrix := interpolationMatrixOnBasis basis points params
  normalizeInterpolationPolynomialOnBasis? basis
    =<< kernelBackend.homogeneousWitness matrix

/-- Interpolation through an explicit homogeneous-kernel backend, with a
constructive low-message fallback.

When `messageDegree ≤ 1`, `yWeight params = 0`, so weighted degree alone does
not bound the `Y`-degree. The fallback returns an explicit product witness
instead of searching the finite dense basis. -/
def denseInterpolateWithKernel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (kernelBackend : LinearKernelBackend F)
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  if params.messageDegree ≤ 1 then
    some (lowMessageDegreeInterpolation points params.multiplicity)
  else
    denseInterpolateWithBasisAndKernel kernelBackend
      (interpolationMonomials params) points params

/-- Dense interpolation using the built-in Gaussian-elimination kernel backend. -/
def denseInterpolate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  denseInterpolateWithKernel (denseLinearKernelBackend F) points params

end GuruswamiSudan

end CompPoly
