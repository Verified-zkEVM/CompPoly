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
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F) :
    FieldRootBackend F where
  rootsInField := CPolynomial.Roots.FiniteField.rootsInOddFiniteFieldWith M D ctx splitter
  sound := by
    intro p a h
    exact CPolynomial.Roots.FiniteField.rootsInOddFiniteFieldWith_sound M D ctx splitter h
  complete := by
    intro p a hp hroot
    exact CPolynomial.Roots.FiniteField.rootsInOddFiniteFieldWith_complete
      M D ctx splitter hp hroot

/-- Package the generic odd finite-field root finder with the default raw arithmetic backends. -/
def oddFiniteFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (splitter : CPolynomial.Roots.FiniteField.LinearFactorProductSplitter F) :
    FieldRootBackend F :=
  oddFiniteFieldRootBackendWith F CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive ctx splitter

/--
Package the deterministic odd finite-field root finder from arithmetic contexts.

This builds the matching deterministic splitter from the same multiplication and
remainder contexts, so concrete fields only need to provide their field facts
and arithmetic backend choices at the edge.
-/
def deterministicOddFiniteFieldRootBackendWith (F : Type*)
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F) :
    FieldRootBackend F :=
  oddFiniteFieldRootBackendWith F M D ctx
    (CPolynomial.Roots.FiniteField.deterministicLinearFactorProductSplitterWith F M D)

/-- Package the deterministic odd finite-field root finder with the default raw arithmetic. -/
def deterministicOddFiniteFieldRootBackend (F : Type*)
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F) :
    FieldRootBackend F :=
  deterministicOddFiniteFieldRootBackendWith F
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx

end GuruswamiSudan

end CompPoly
