/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.CantorZassenhaus
import CompPoly.Univariate.Roots.Extraction

/-!
# Odd Finite-Field Root Backend

Executable field-root extraction over odd finite fields. The public operation
handles zero, constant, and linear cases explicitly, computes the finite-field
root product modulo the input polynomial, splits the product into linear
factors, then validates and deduplicates candidates against the original input.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Executable roots of a univariate polynomial over an odd finite field. -/
def rootsInOddFiniteFieldWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    (p : CPolynomial F) : Array F :=
  if p == 0 then
    #[]
  else if p.val.size ≤ 1 then
    #[]
  else if p.val.size = 2 && !(p.coeff 1 == 0) then
    CPolynomial.rootsFromLinearFactors p #[p]
  else
    let rootProduct := finiteFieldRootProductWith M D ctx p
    let factors := splitter.splitLinearFactors ctx.q rootProduct
    CPolynomial.rootsFromLinearFactors p factors

/-- Executable roots using the default raw multiplication and monic-remainder backends. -/
def rootsInOddFiniteField {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    (p : CPolynomial F) : Array F :=
  rootsInOddFiniteFieldWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx splitter p

end FiniteField

end Roots

end CPolynomial

end CompPoly
