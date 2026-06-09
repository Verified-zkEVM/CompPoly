/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.Roots.Context

/-!
# Linear-Factor Splitter Helpers

Shared executable helpers for finite-field linear-factor splitters.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Boolean recognizer for represented nonconstant linear factors. -/
def isRepresentedLinearFactor {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) : Bool :=
  decide (p.val.size ≤ 2) && !(p.coeff 1 == 0)

/-- The represented-linear Boolean recognizer is sound. -/
theorem isRepresentedLinearFactor_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (h : isRepresentedLinearFactor p = true) :
    IsLinearFactor p := by
  unfold isRepresentedLinearFactor at h
  simp at h
  simpa [IsLinearFactor, CPolynomial.coeff, CPolynomial.Raw.coeff] using h

/-- Return `p` as a singleton array if it is represented as a nonconstant linear factor. -/
def representedLinearFactorArray {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) : Array (CPolynomial F) :=
  if isRepresentedLinearFactor p then #[p] else #[]

/-- `X^exponent mod modulus`, lifted back to canonical polynomials. -/
def xPowModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial F) (exponent : Nat) : CPolynomial F :=
  CPolynomial.ofArray
    (CPolynomial.Raw.powModWith M D modulus.val
      (CPolynomial.Raw.X : CPolynomial.Raw F) exponent)

end FiniteField

end Roots

end CPolynomial

end CompPoly
