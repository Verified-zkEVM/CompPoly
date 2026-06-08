/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_48
import CompPoly.Fields.Binary.GF2_72
import CompPoly.Univariate.Roots

/-!
# Binary-Field Univariate Root Tests

Instantiation checks for the executable univariate finite-field root backend over
`GF(2^48)` and `GF(2^72)` with Shoup and smooth splitters.
-/

namespace CompPolyTests.Univariate.Roots.Binary

open CompPoly

private abbrev F48 := GF2_48.ConcreteField
private abbrev F72 := GF2_72.ConcreteField

private def rootsWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F)
    (p : CPolynomial F) : Array F :=
  CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx splitter p

noncomputable example (p : CPolynomial F48) :
    Array F48 :=
  rootsWith GF2_48.finiteFieldContext
    (CPolynomial.Roots.FiniteField.shoupLinearFactorProductSplitter
      GF2_48.shoupTraceContext)
    p

noncomputable example (p : CPolynomial F48) :
    Array F48 :=
  rootsWith GF2_48.finiteFieldContext
    (CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      GF2_48.smoothHornerRootContext)
    p

noncomputable example (p : CPolynomial F48) :
    Array F48 :=
  rootsWith GF2_48.finiteFieldContext
    (CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      GF2_48.smoothSubproductRootContext)
    p

noncomputable example (p : CPolynomial F48) :
    Array F48 :=
  rootsWith GF2_48.finiteFieldContext
    (CPolynomial.Roots.FiniteField.lasVegasLinearFactorProductSplitterWithTrace
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      GF2_48.finiteFieldContext
      GF2_48.fieldEnumeration
      GF2_48.shoupTraceContext
      GF2_48.lasVegasConfig
      GF2_48.lasVegasProbeFamily)
    p

noncomputable example (p : CPolynomial F72) :
    Array F72 :=
  rootsWith GF2_72.finiteFieldContext
    (CPolynomial.Roots.FiniteField.shoupLinearFactorProductSplitter
      GF2_72.shoupTraceContext)
    p

noncomputable example (p : CPolynomial F72) :
    Array F72 :=
  rootsWith GF2_72.finiteFieldContext
    (CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      GF2_72.smoothHornerRootContext)
    p

noncomputable example (p : CPolynomial F72) :
    Array F72 :=
  rootsWith GF2_72.finiteFieldContext
    (CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      GF2_72.smoothSubproductRootContext)
    p

noncomputable example (p : CPolynomial F72) :
    Array F72 :=
  rootsWith GF2_72.finiteFieldContext
    (CPolynomial.Roots.FiniteField.lasVegasLinearFactorProductSplitterWithTrace
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      GF2_72.finiteFieldContext
      GF2_72.fieldEnumeration
      GF2_72.shoupTraceContext
      GF2_72.lasVegasConfig
      GF2_72.lasVegasProbeFamily)
    p

end CompPolyTests.Univariate.Roots.Binary
