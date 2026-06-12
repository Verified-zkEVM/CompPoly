/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.Correctness

/-!
# Recursive PM-Basis

Umbrella module for the divide-and-conquer PM-basis: executable definitions,
correctness development, and the production `PMBasisContext` instances backed
by the recursive driver with scalar dense-kernel leaves.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- PM-basis context backed by the recursive driver, scalar dense-kernel leaves,
and an independently tuned basis-composition cutoff. -/
def kernelLeafPMBasisContextWithLowAndCompose (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) : PMBasisContext F where
  runtime := kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
    composeLeafCutoff
  basis := pmBasis (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
    composeLeafCutoff)
  sound := by
    intro problem shift row hrow
    exact pmBasis_kernelLeaf_approximates mulCtx lowCtx leafCutoff
      composeLeafCutoff problem shift hrow
  complete_minimal := by
    -- Shifted-minimality of the recursive PM-basis (the predictable-degree
    -- property of minimal approximant bases): every nonzero X-adic solution
    -- row is degree-dominated by some basis row.
    letI : DecidableEq F := instDecidableEqOfLawfulBEq
    intro problem shift row hpos hwf happrox hnz hwidth
    exact pmBasis_kernelLeaf_complete_minimal mulCtx lowCtx leafCutoff
      composeLeafCutoff problem shift row hpos hwf happrox hnz hwidth

/-- PM-basis context backed by the recursive driver and scalar dense-kernel
leaves. -/
def kernelLeafPMBasisContextWithLow (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff : Nat) : PMBasisContext F :=
  kernelLeafPMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff leafCutoff

/-- PM-basis context whose low products are obtained by truncating full
products. -/
def kernelLeafPMBasisContext (mulCtx : CPolynomial.MulContext F)
    (leafCutoff : Nat) : PMBasisContext F :=
  kernelLeafPMBasisContextWithLow mulCtx
    (PolynomialMatrix.MulLowContext.fromMulContext mulCtx) leafCutoff

end Approximant

end PolynomialMatrix

end CompPoly
