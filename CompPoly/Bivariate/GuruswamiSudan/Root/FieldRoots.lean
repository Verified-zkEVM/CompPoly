/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Context
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField

/-!
# Guruswami-Sudan Field Roots

Executable univariate field-root helpers used by Roth-Ruckenstein recursion.
The explicit `FieldRootBackend` context makes this dependency replaceable for
large concrete fields.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Executable degree-`< k` check for canonical polynomials. -/
def degreeLtBool {F : Type*} [Zero F] (p : CPolynomial F) (k : Nat) : Bool :=
  p.val.size ≤ k

/-- Roots by exhaustive evaluation over an explicit field-element list. -/
def rootsInFieldByEnumeration {F : Type*} [Semiring F] [BEq F]
    (elements : Array F) (p : CPolynomial F) : Array F :=
  elements.filter fun a => CPolynomial.eval a p == 0

/-- An array contains every field element. Duplicate entries are allowed. -/
def ContainsAllFieldElements {F : Type*} (elements : Array F) : Prop :=
  forall a : F, a ∈ elements.toList

private theorem rootsInFieldByEnumeration_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {elements : Array F} {p : CPolynomial F} {a : F}
    (h : a ∈ (rootsInFieldByEnumeration elements p).toList) :
    CPolynomial.eval a p = 0 := by
  rw [rootsInFieldByEnumeration] at h
  simp at h
  simpa [CPolynomial.eval_horner_eq_eval] using h.2

/-- Field roots by explicit enumeration over a supplied field-element list. -/
def enumeratingFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (elements : Array F) (hElements : ContainsAllFieldElements elements) :
    FieldRootBackend F where
  rootsInField := rootsInFieldByEnumeration elements
  sound := by
    intro p a h
    exact rootsInFieldByEnumeration_sound h
  complete := by
    intro p a hp h
    rw [rootsInFieldByEnumeration]
    simp [h]
    simpa using hElements a

end GuruswamiSudan

end CompPoly
