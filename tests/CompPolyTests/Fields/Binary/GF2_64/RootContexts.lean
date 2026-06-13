/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_64
import CompPoly.Univariate.Roots.Shoup

/-!
# GF(2^64) Root-Context Tests

Focused compile-time checks for the certified finite-field, Shoup, and smooth
root-search contexts over executable `GF(2^64)`.
-/

namespace CompPolyTests.Fields.Binary.GF2_64.RootContexts

private abbrev F := GF2_64.ConcreteField

example :
    GF2_64.finiteFieldContext.q = GF2_64.fieldSize :=
  rfl

example :
    GF2_64.shoupTraceContext.toFiniteFieldContext.q = GF2_64.fieldSize :=
  rfl

example :
    GF2_64.smoothHornerRootContext.q = GF2_64.fieldSize :=
  rfl

example :
    GF2_64.smoothSubproductRootContext.q = GF2_64.fieldSize :=
  rfl

noncomputable example :
    CompPoly.CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CompPoly.CPolynomial.Roots.FiniteField.shoupLinearFactorProductSplitter
    GF2_64.shoupTraceContext

noncomputable example :
    CompPoly.CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F :=
  CompPoly.CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
    CompPoly.CPolynomial.Raw.MulContext.naive CompPoly.CPolynomial.Raw.ModContext.naive
    GF2_64.smoothSubproductRootContext

end CompPolyTests.Fields.Binary.GF2_64.RootContexts
