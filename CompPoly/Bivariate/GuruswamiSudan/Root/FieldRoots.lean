/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Context
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Univariate.Roots.Enumeration

/-!
# Guruswami-Sudan Field Roots

Executable univariate field-root helpers used by Roth-Ruckenstein recursion.
The explicit `FieldRootContext` context makes this dependency replaceable for
large concrete fields.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Executable degree-`< k` check for canonical polynomials. -/
def degreeLtBool {F : Type*} [Zero F] (p : CPolynomial F) (k : Nat) : Bool :=
  p.val.size ≤ k

/-- Compatibility alias for the univariate exhaustive-enumeration predicate. -/
abbrev ContainsAllFieldElements {F : Type*} (elements : Array F) : Prop :=
  CPolynomial.Roots.FiniteField.ContainsAllFieldElements elements

/-- Compatibility wrapper for roots by exhaustive evaluation over an explicit field list. -/
def rootsInFieldByEnumeration {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (elements : Array F) (hElements : ContainsAllFieldElements elements)
    (p : CPolynomial F) : Array F :=
  let enumeration :=
    CPolynomial.Roots.FiniteField.fieldEnumerationOfArray elements hElements
  CPolynomial.Roots.FiniteField.rootsInFieldByEnumeration enumeration p

/-- Field roots by explicit enumeration over a supplied field-element list. -/
def enumeratingFieldRootContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (elements : Array F) (hElements : ContainsAllFieldElements elements) :
    FieldRootContext F where
  rootsInField := rootsInFieldByEnumeration elements hElements
  sound := by
    intro p a h
    exact CPolynomial.Roots.FiniteField.rootsInFieldByEnumeration_sound h
  complete := by
    intro p a hp h
    exact CPolynomial.Roots.FiniteField.rootsInFieldByEnumeration_complete
      (CPolynomial.Roots.FiniteField.fieldEnumerationOfArray elements hElements) h

end GuruswamiSudan

end CompPoly
