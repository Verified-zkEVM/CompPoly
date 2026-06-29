/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast.Theorems
import Mathlib.Algebra.Field.TransferInstance

/-!
# Field Structure for Fast Goldilocks Arithmetic

This module transfers the canonical Goldilocks field structure to the fast
`UInt64` representation.
-/

namespace Goldilocks
namespace Fast

/-- Ring equivalence between the fast representation and canonical Goldilocks. -/
def ringEquiv : Field ≃+* Goldilocks.Basic.Field where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x := rfl

/-- Applying the inverse `ringEquiv` converts a canonical value into fast form. -/
@[simp]
theorem ringEquiv_symm_apply (x : Goldilocks.Basic.Field) : ringEquiv.symm x = ofField x := rfl

/-- Field instance transferred from canonical Goldilocks through `toField`. -/
instance (priority := low) instField : _root_.Field Field :=
  toField_injective.field toField
    toField_zero
    toField_one
    toField_add
    toField_mul
    toField_neg
    toField_sub
    toField_inv
    toField_div
    toField_nsmul
    toField_zsmul
    toField_nnqsmul
    toField_qsmul
    toField_npow
    toField_zpow
    toField_natCast
    toField_intCast
    toField_nnratCast
    toField_ratCast

/-- Commutative-ring instance inherited from the transferred field structure. -/
instance (priority := low) instCommRing : CommRing Field := by
  infer_instance

/-- Fast Goldilocks is a non-binary field. -/
instance (priority := low) instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    intro h
    have hv := congrArg Subtype.val h
    exact (by decide : (2 : UInt64) ≠ 0) hv

end Fast
end Goldilocks
