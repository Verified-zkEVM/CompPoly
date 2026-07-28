/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Impl
import CompPoly.Univariate.Roots.Enumeration

/-!
# Direct Binary-Extension Field Enumerations

Lazy finite-field enumeration contexts for executable direct binary-extension
carriers.
-/

namespace BinaryField

namespace Extension

namespace Concrete

open CompPoly.CPolynomial.Roots.FiniteField

variable (params : ExecutableParams)

private theorem toNat_lt (a : ConcreteField params) :
    toNat params a < fieldSize params.degree := by
  simpa [toNat, toBitVec, fieldSize] using (toBitVec params a).isLt

private theorem ofNat_toNat (a : ConcreteField params) :
    ofNat params (toNat params a) = a := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat, toBitVec, ofNat, ofBitVec]

/-- Lazy complete enumeration for a direct executable binary-extension carrier. -/
def fieldEnumeration : FieldEnumeration (ConcreteField params) where
  size := fieldSize params.degree
  elem i := ofNat params i.val
  complete := by
    intro a
    exact ⟨⟨toNat params a, toNat_lt params a⟩, ofNat_toNat params a⟩

end Concrete

end Extension

end BinaryField
