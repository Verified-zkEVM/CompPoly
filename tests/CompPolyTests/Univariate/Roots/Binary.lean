/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.Binary
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
      CompPoly.GuruswamiSudan.Binary.gf2_48FieldEnumeration
      GF2_48.shoupTraceContext
      CompPoly.GuruswamiSudan.Binary.gf2_48LasVegasConfig
      CompPoly.GuruswamiSudan.Binary.gf2_48LasVegasProbeFamily)
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
      CompPoly.GuruswamiSudan.Binary.gf2_72FieldEnumeration
      GF2_72.shoupTraceContext
      CompPoly.GuruswamiSudan.Binary.gf2_72LasVegasConfig
      CompPoly.GuruswamiSudan.Binary.gf2_72LasVegasProbeFamily)
    p

end CompPolyTests.Univariate.Roots.Binary
