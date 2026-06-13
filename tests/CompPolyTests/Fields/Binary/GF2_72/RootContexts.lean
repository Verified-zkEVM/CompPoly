/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_72
import CompPoly.Univariate.Roots.Shoup

/-!
# GF(2^72) Root-Context Tests

Focused compile-time checks for the certified finite-field, Shoup, and smooth
root-search contexts over executable `GF(2^72)`.
-/

namespace CompPolyTests.Fields.Binary.GF2_72.RootContexts

private abbrev F := GF2_72.ConcreteField

example :
    GF2_72.finiteFieldContext.q = GF2_72.fieldSize :=
  rfl

example :
    GF2_72.shoupTraceContext.toFiniteFieldContext.q = GF2_72.fieldSize :=
  rfl

example :
    GF2_72.smoothHornerRootContext.q = GF2_72.fieldSize :=
  rfl

example :
    GF2_72.smoothSubproductRootContext.q = GF2_72.fieldSize :=
  rfl

noncomputable example :
    CompPoly.CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CompPoly.CPolynomial.Roots.FiniteField.shoupLinearFactorProductSplitter
    GF2_72.shoupTraceContext

noncomputable example :
    CompPoly.CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CompPoly.CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
    CompPoly.CPolynomial.Raw.MulContext.naive CompPoly.CPolynomial.Raw.ModContext.naive
    GF2_72.smoothSubproductRootContext

end CompPolyTests.Fields.Binary.GF2_72.RootContexts
