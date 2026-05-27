/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic

/-!
# Dense Guruswami-Sudan Interpolation

Executable dense interpolation backend: build the Hasse-constraint matrix,
compute one homogeneous-kernel witness, normalize it, and return the associated
`CBivariate` interpolation polynomial.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Dense interpolation through an explicit homogeneous-kernel backend. -/
def denseInterpolateWithKernel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (kernelBackend : LinearKernelBackend F)
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  let matrix := interpolationMatrix points params
  normalizeInterpolationPolynomial? params
    =<< kernelBackend.homogeneousWitness matrix

/-- Dense interpolation using the built-in Gaussian-elimination kernel backend. -/
def denseInterpolate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (Prod F F)) (params : GSInterpParams) :
    Option (CBivariate F) :=
  denseInterpolateWithKernel (denseLinearKernelBackend F) points params

end GuruswamiSudan

end CompPoly
