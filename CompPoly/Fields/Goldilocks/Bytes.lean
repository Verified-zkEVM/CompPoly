/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Goldilocks.Fast
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of the fast Goldilocks carrier

`Goldilocks.Fast.Field` stores the canonical residue in a `UInt64`, so its canonical natural is
the stored word and the eight-byte little-endian encoding agrees with `Goldilocks.Field`
(`toBytes_ofField`).
-/

@[expose] public section

namespace Goldilocks.Fast

open CompPoly

theorem toNat_lt (x : Field) : toNat x < Goldilocks.fieldSize := x.property

theorem ofField_cast_toNat (x : Field) : ofField (toNat x : Goldilocks.Field) = x :=
  ofField_toField x

instance : CanonicalNat Field :=
  CanonicalNat.ofToField toNat ofField toNat_lt ofField_cast_toNat toNat_ofField

instance : ByteCodec Field := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound Field = Goldilocks.fieldSize := rfl

@[simp] theorem canonicalNat_toNat (x : Field) : CanonicalNat.toNat x = toNat x := rfl

@[simp] theorem byteCodec_width : ByteCodec.width Field = 8 := by decide

/-- The fast carrier and `Goldilocks.Field` encode the same element identically. -/
theorem toBytes_ofField (n : Goldilocks.Field) :
    ByteCodec.toBytes (ofField n) = ByteCodec.toBytes n := by
  show Bytes.toVecLE _ (toNat (ofField n)) = Bytes.toVecLE _ n.val
  rw [toNat_ofField]

end Goldilocks.Fast
