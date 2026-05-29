/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Context
import CompPoly.Univariate.Roots.Correctness

/-!
# Guruswami-Sudan Finite-Field Root Adapter

Adapter from the reusable odd finite-field univariate root operation to the
certified `FieldRootBackend` context consumed by Roth-Ruckenstein root finding.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Package the generic odd finite-field root finder as a GS field-root backend. -/
def oddFiniteFieldRootBackendWith (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F)
    (splitterValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        splitter.validInput ctx.q
          (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D ctx p)) :
    FieldRootBackend F where
  rootsInField := CPolynomial.Roots.FiniteField.rootsInOddFiniteFieldWith M D ctx splitter
  sound := by
    intro p a h
    exact CPolynomial.Roots.FiniteField.rootsInOddFiniteFieldWith_sound M D ctx splitter h
  complete := by
    intro p a hp hroot
    exact CPolynomial.Roots.FiniteField.rootsInOddFiniteFieldWith_complete
      M D ctx splitter splitterValid hp hroot

/-- Package the generic odd finite-field root finder with the default raw arithmetic backends. -/
def oddFiniteFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F)
    (splitterValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        splitter.validInput ctx.q (CPolynomial.Roots.FiniteField.finiteFieldRootProduct ctx p)) :
    FieldRootBackend F :=
  oddFiniteFieldRootBackendWith F CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx splitter (by
      intro p hp
      exact splitterValid hp)

/-- Package a smooth cyclic splitter as a GS field-root backend. -/
def smoothOddFiniteFieldRootBackendWith (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (oddCtx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (smoothCtx : CPolynomial.Roots.FiniteField.SmoothCyclicRootContext F)
    (smoothValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        smoothCtx.validInput
          (CPolynomial.Roots.FiniteField.finiteFieldRootProductWith M D oddCtx p)) :
    FieldRootBackend F :=
  oddFiniteFieldRootBackendWith F M D oddCtx
    (CPolynomial.Roots.FiniteField.smoothLinearFactorProductSplitterWith M D smoothCtx)
    (by
      intro p hp
      exact smoothValid hp)

/-- Package a smooth cyclic splitter with default raw arithmetic as a GS field-root backend. -/
def smoothOddFiniteFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (oddCtx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (smoothCtx : CPolynomial.Roots.FiniteField.SmoothCyclicRootContext F)
    (smoothValid :
      ∀ {p : CPolynomial F}, p ≠ 0 →
        smoothCtx.validInput
          (CPolynomial.Roots.FiniteField.finiteFieldRootProduct oddCtx p)) :
    FieldRootBackend F :=
  smoothOddFiniteFieldRootBackendWith F CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive oddCtx smoothCtx (by
      intro p hp
      exact smoothValid hp)

end GuruswamiSudan

end CompPoly
