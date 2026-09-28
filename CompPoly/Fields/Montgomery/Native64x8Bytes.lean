/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Montgomery.Native64x8Field
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of the eight-limb Montgomery carrier

`Native64x8.FastField modulus` stores a Montgomery residue in eight 32-bit limbs. Its canonical
natural is the value after one Montgomery reduction, `FastField.toNat`, so the bytes agree with
the `ZMod modulus` codec (`toBytes_ofField`, `toNat_ofField`). Decoding converts through
`ofField`.
-/

@[expose] public section

namespace Montgomery.Native64x8

open CompPoly

variable {modulus : ℕ} [P : Mont64x8Field modulus]

namespace FastField

/-- The canonical natural of a fast element is the residue of its canonical field value. -/
theorem toNat_eq_val_toField (x : FastField modulus) : toNat x = (toField x).val := by
  rw [toField, ZMod.val_natCast, Nat.mod_eq_of_lt (toNat_lt x)]

/-- Carrier agreement: the canonical natural of `ofField n` is the residue `n.val`. -/
theorem toNat_ofField (n : ZMod modulus) : toNat (ofField n) = n.val := by
  rw [toNat_eq_val_toField, toField_ofField]

theorem ofField_cast_toNat (x : FastField modulus) : ofField (toNat x : ZMod modulus) = x :=
  ofField_toField x

instance : CanonicalNat (FastField modulus) :=
  CanonicalNat.ofToField toNat ofField toNat_lt ofField_cast_toNat toNat_ofField

instance : ByteCodec (FastField modulus) := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound (FastField modulus) = modulus := rfl

@[simp] theorem canonicalNat_toNat (x : FastField modulus) : CanonicalNat.toNat x = toNat x := rfl

@[simp] theorem canonicalNat_ofNat (n : ℕ) :
    CanonicalNat.ofNat (F := FastField modulus) n = ofField (n : ZMod modulus) := rfl

@[simp] theorem byteCodec_width : ByteCodec.width (FastField modulus) = Bytes.bytesFor modulus :=
  rfl

/-- The fast carrier and `ZMod modulus` encode the same element identically. -/
theorem toBytes_ofField (n : ZMod modulus) :
    ByteCodec.toBytes (ofField n) = ByteCodec.toBytes n := by
  show Bytes.toVecLE _ (toNat (ofField n)) = Bytes.toVecLE _ n.val
  rw [toNat_ofField]

/-- Encoding then converting to the spec field is encoding in the spec field. -/
theorem toBytes_eq_toBytes_toField (x : FastField modulus) :
    ByteCodec.toBytes x = ByteCodec.toBytes (toField x) := by
  rw [← toBytes_ofField, ofField_toField]

end FastField

end Montgomery.Native64x8
