/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Data.Bytes.Vector

/-! # Four-byte little-endian word storage

This codec stores the word itself. A Montgomery field coordinate is a word in this format;
it is distinct from the canonical field-element serialization.
-/

@[expose] public section
namespace CompPoly

instance : CanonicalNat UInt32 where
  bound := 2 ^ 32
  toNat := UInt32.toNat
  ofNat := UInt32.ofNat
  toNat_lt := UInt32.toNat_lt
  ofNat_toNat x := UInt32.ofNat_toNat
  toNat_ofNat_of_lt h := by
    simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt h]
  ofNat_mod n := by
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_ofNat', Nat.mod_mod]

instance : ByteCodec UInt32 := ByteCodec.ofCanonicalNat _

@[simp] theorem ByteCodec.width_uint32 : ByteCodec.width UInt32 = 4 := by decide

/-- The word codec exposes precisely the four little-endian bytes of its bit pattern. -/
theorem ByteCodec.toBytes_uint32 (x : UInt32) :
    (ByteCodec.toBytes x).toList = Bytes.toListLE 4 x.toNat := rfl

end CompPoly
