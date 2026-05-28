/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.Roots.Context

/-!
# Finite-Field Root Products

Executable construction of `gcd(p, X^q - X)` as
`gcd(p, (X^q mod p) - (X mod p))`, so large finite fields never materialize the
dense polynomial `X^q - X`.
-/

namespace CompPoly

namespace CPolynomial

namespace Raw

namespace Roots

namespace FiniteField

/-- Raw squarefree product of the linear factors of `p` whose roots lie in the field. -/
def finiteFieldRootProductWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (p : CPolynomial.Raw F) : CPolynomial.Raw F :=
  if p.trim == 0 then
    0
  else
    let pMonic := CPolynomial.Raw.monicNormalize p
    CPolynomial.Raw.gcdMonic pMonic (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic)

/-- Raw squarefree product using the default raw backends. -/
def finiteFieldRootProduct {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (p : CPolynomial.Raw F) : CPolynomial.Raw F :=
  finiteFieldRootProductWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx p

end FiniteField

end Roots

end Raw

namespace Roots

namespace FiniteField

/-- The squarefree product of the linear factors of `p` whose roots lie in the field. -/
def finiteFieldRootProductWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (p : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray (CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith M D ctx p.val)

/-- The squarefree product of the linear factors of `p` using the default raw backends. -/
def finiteFieldRootProduct {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (p : CPolynomial F) : CPolynomial F :=
  finiteFieldRootProductWith CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx p

end FiniteField

end Roots

end CPolynomial

end CompPoly
