/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Context

/-!
# Guruswami-Sudan Field Roots

Executable univariate field-root helpers used by Roth-Ruckenstein recursion.
The explicit `FieldRootBackend` context keeps this dependency replaceable for
large concrete fields.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Executable degree-`< k` check for canonical polynomials. -/
def degreeLtBool {F : Type*} [Zero F] (p : CPolynomial F) (k : Nat) : Bool :=
  p.val.size ≤ k

/-- Enumerate coefficient vectors of fixed length over a supplied finite element list. -/
def coefficientVectors {F : Type*} (elements : Array F) : Nat → Array (Array F)
  | 0 => #[#[]]
  | n + 1 =>
      Id.run do
        let mut out := #[]
        for pref in coefficientVectors elements n do
          for a in elements do
            out := out.push (pref.push a)
        pure out

/-- Enumerate all polynomials with coefficient-vector length `k` over an explicit field list. -/
def polynomialsDegreeLt {F : Type*} [Zero F] [BEq F] [LawfulBEq F]
    (elements : Array F) (k : Nat) : Array (CPolynomial F) :=
  (coefficientVectors elements k).map CPolynomial.ofArray

/-- Roots by exhaustive evaluation over an explicit field-element list. -/
def rootsInFieldByEnumeration {F : Type*} [Semiring F] [BEq F]
    (elements : Array F) (p : CPolynomial F) : Array F :=
  elements.filter fun a => CPolynomial.eval a p == 0

/-- An array contains every field element. Duplicate entries are allowed. -/
def ContainsAllFieldElements {F : Type*} (elements : Array F) : Prop :=
  forall a : F, a ∈ elements.toList

/-- Linear closed-form field roots when the result is determined without
enumerating the field. -/
def rootsInFieldLinear? {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) : Array F :=
  if p.val.size = 1 then
    if p.coeff 0 == 0 then #[] else #[]
  else if p.val.size = 2 && !(p.coeff 1 == 0) then
    #[-(p.coeff 0) / p.coeff 1]
  else
    #[]

/-- Linear closed-form field roots for large-field backends.

When the polynomial is identically zero this returns one representative root so
the function remains executable without enumerating the whole field.
-/
def rootsInFieldLinear {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) : Array F :=
  if p.val.size = 0 || (p.val.size = 1 && p.coeff 0 == 0) then
    #[0]
  else
    rootsInFieldLinear? p

/-- Prefer the linear closed-form path, then fall back to explicit enumeration. -/
def rootsInFieldLinearOrEnumeration {F : Type*} [Field F] [BEq F]
    (elements : Array F) (p : CPolynomial F) : Array F :=
  let linearRoots := rootsInFieldLinear p
  if p.val.size = 0 || (p.val.size = 1 && p.coeff 0 == 0) then
    rootsInFieldByEnumeration elements p
  else if linearRoots.size = 0 then
    rootsInFieldByEnumeration elements p
  else
    linearRoots

/-- Field square-root backend, used by future low-degree root specializations. -/
structure FieldSqrtBackend (F : Type*) where
  sqrt? : F → Option F

/-- Polynomial square-root backend, used by future root backends below the GS API. -/
structure PolynomialSqrtBackend (F : Type*) [Zero F] where
  sqrt? : CPolynomial F → Option (CPolynomial F)

/-- Field roots by explicit enumeration over a supplied field-element list. -/
def enumeratingFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (elements : Array F) : FieldRootBackend F where
  rootsInField := rootsInFieldByEnumeration elements
  sound := by
    intro p a h
    sorry
  complete := by
    intro p a hp h
    sorry

/-- Linear roots with an enumeration fallback. -/
def linearOrEnumeratingFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (elements : Array F) : FieldRootBackend F where
  rootsInField := rootsInFieldLinearOrEnumeration elements
  sound := by
    intro p a h
    sorry
  complete := by
    intro p a hp h
    sorry

/-- Linear-only executable field-root backend.

This is useful for workloads known to generate only linear field equations. Its
contract fields are placeholders until a complete non-enumerating finite-field
backend replaces it for large fields.
-/
def linearFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F] :
    FieldRootBackend F where
  rootsInField := rootsInFieldLinear
  sound := by
    intro p a h
    sorry
  complete := by
    intro p a hp h
    sorry

end GuruswamiSudan

end CompPoly
