/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Correctness

/-!
# Exhaustive Finite-Field Root Enumeration

Reusable lazy field-enumeration contexts for finite-field root search. The
context stores an indexing function rather than an array of all elements; array
inputs are adapted through `fieldEnumerationOfArray` for tests and small
callers.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- A lazy complete enumeration of a finite field. -/
structure FieldEnumeration (F : Type*) where
  size : Nat
  elem : Fin size → F
  complete : ∀ a : F, ∃ i : Fin size, elem i = a

/-- An array contains every field element. Duplicate entries are allowed. -/
def ContainsAllFieldElements {F : Type*} (elements : Array F) : Prop :=
  ∀ a : F, a ∈ elements.toList

/-- Adapt an explicit element array to a lazy enumeration context. -/
def fieldEnumerationOfArray {F : Type*} (elements : Array F)
    (hElements : ContainsAllFieldElements elements) :
    FieldEnumeration F where
  size := elements.size
  elem i := elements[i]
  complete := by
    intro a
    rcases List.mem_iff_get.mp (hElements a) with ⟨i, hi⟩
    refine ⟨⟨i.val, by simpa only [Array.length_toList] using i.isLt⟩, ?_⟩
    simpa using hi

/-- Roots by exhaustive evaluation over a lazy field enumeration. -/
def rootsInFieldByEnumeration {F : Type*} [Semiring F] [BEq F]
    (enumeration : FieldEnumeration F) (p : CPolynomial F) : Array F :=
  (Array.ofFn enumeration.elem).filter fun a ↦ CPolynomial.evalHorner a p == 0

/-- Exhaustive enumeration only returns actual roots. -/
theorem rootsInFieldByEnumeration_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {enumeration : FieldEnumeration F} {p : CPolynomial F} {a : F}
    (h : a ∈ (rootsInFieldByEnumeration enumeration p).toList) :
    CPolynomial.eval a p = 0 := by
  rw [rootsInFieldByEnumeration] at h
  simp at h
  simpa [CPolynomial.eval_horner_eq_eval] using h.2

/-- Complete enumeration finds every root. -/
theorem rootsInFieldByEnumeration_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    a ∈ (rootsInFieldByEnumeration enumeration p).toList := by
  rw [rootsInFieldByEnumeration]
  rcases enumeration.complete a with ⟨i, hi⟩
  simpa [CPolynomial.eval_horner_eq_eval, hroot] using ⟨i, hi⟩

/-- Linear factors for every enumerated root of `p`. -/
def enumeratedLinearFactors {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (p : CPolynomial F) :
    Array (CPolynomial F) :=
  (rootsInFieldByEnumeration enumeration p).map CPolynomial.linearFactor

/-- Every factor emitted by exhaustive enumeration is represented linear. -/
theorem enumeratedLinearFactors_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {enumeration : FieldEnumeration F} {p factor : CPolynomial F}
    (h : factor ∈ (enumeratedLinearFactors enumeration p).toList) :
    IsLinearFactor factor := by
  rw [enumeratedLinearFactors] at h
  simp at h
  rcases h with ⟨a, _hmem, rfl⟩
  exact linearFactor_isLinearFactor a

/-- Exhaustive enumeration emits the linear factor for every root. -/
theorem enumeratedLinearFactors_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (enumeratedLinearFactors enumeration p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  refine ⟨CPolynomial.linearFactor a, ?_, linearFactor_isRootFactorCandidate a⟩
  rw [enumeratedLinearFactors]
  simpa using
    (List.mem_map.mpr
      ⟨a, rootsInFieldByEnumeration_complete enumeration hroot, rfl⟩)

/-- Exhaustive enumeration packaged as a linear-factor product splitter. -/
def enumeratingLinearFactorProductSplitter {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun _ p ↦ enumeratedLinearFactors enumeration p
  validInput := fun _ _ ↦ True
  sound := by
    intro _q p factor h
    exact enumeratedLinearFactors_sound h
  complete := by
    intro _q p a _hvalid _hp hroot
    exact enumeratedLinearFactors_complete enumeration hroot

end FiniteField

end Roots

end CPolynomial

end CompPoly
