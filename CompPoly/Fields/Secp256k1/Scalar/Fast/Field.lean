/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.Secp256k1.Scalar.Fast.Theorems
import Mathlib.Algebra.Field.TransferInstance

/-!
# Field Structure for Fast secp256k1 Scalar Arithmetic

This module transfers the canonical secp256k1 scalar-field structure to the
fast four-limb representation and exposes the corresponding ring equivalence.
-/

namespace Secp256k1.Scalar.Fast

/-- Ring equivalence between fast 4×`UInt64` scalars and canonical secp256k1 scalars. -/
def ringEquiv : Field ≃+* Secp256k1.Scalar.Basic.Field where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

/-- Applying `ringEquiv` interprets a fast scalar in the canonical scalar field. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x := rfl

/-- Applying the inverse equivalence converts a canonical scalar to fast representation. -/
@[simp]
theorem ringEquiv_symm_apply (x : Secp256k1.Scalar.Basic.Field) :
    ringEquiv.symm x = ofField x := rfl

/-- Field instance transferred from the canonical scalar field through `toField`. -/
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

/-- Fast secp256k1 scalar arithmetic is a non-binary field. -/
instance (priority := low) instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    intro h
    have hv : (2 : Secp256k1.Scalar.Basic.Field) = 0 := by
      simpa using congrArg toField h
    exact (by decide : (2 : Secp256k1.Scalar.Basic.Field) ≠ 0) hv

end Secp256k1.Scalar.Fast
