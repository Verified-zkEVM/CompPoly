/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Mersenne31.Fast
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of the fast Mersenne31 carrier

`Mersenne31.Fast.Field` stores the canonical residue in a `UInt32`, so its canonical natural is
the stored word and the four-byte little-endian encoding agrees with `Mersenne31.Field`
(`toBytes_ofField`).
-/

@[expose] public section

namespace Mersenne31.Fast

open CompPoly

theorem toNat_lt (x : Field) : toNat x < Mersenne31.fieldSize := x.property

theorem ofField_cast_toNat (x : Field) : ofField (toNat x : Mersenne31.Field) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  change toNat (ofField _) = toNat x
  rw [toNat_ofField, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt x.property

instance : CanonicalNat Field :=
  CanonicalNat.ofToField toNat ofField toNat_lt ofField_cast_toNat toNat_ofField

instance : ByteCodec Field := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound Field = Mersenne31.fieldSize := rfl

@[simp] theorem canonicalNat_toNat (x : Field) : CanonicalNat.toNat x = toNat x := rfl

@[simp] theorem byteCodec_width : ByteCodec.width Field = 4 := by decide

/-- The fast carrier and `Mersenne31.Field` encode the same element identically. -/
theorem toBytes_ofField (n : Mersenne31.Field) :
    ByteCodec.toBytes (ofField n) = ByteCodec.toBytes n := by
  show Bytes.toVecLE _ (toNat (ofField n)) = Bytes.toVecLE _ n.val
  rw [toNat_ofField]

end Mersenne31.Fast
