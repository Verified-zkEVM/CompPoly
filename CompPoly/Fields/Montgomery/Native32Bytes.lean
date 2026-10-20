/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Montgomery.Native32Field
public import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Data.ByteArray.Packed

/-!
# Serialization of the 32-bit Montgomery carrier

`Native32.FastField modulus` stores a Montgomery residue. Its canonical natural is the value
after one Montgomery reduction, `FastField.toNat`, so the bytes are those of the abstract field
element and agree with the `ZMod modulus` codec: `toBytes_ofField` and `toNat_ofField` are the
agreement laws. Decoding converts through `ofField`.
-/

@[expose] public section

namespace Montgomery.Native32

open CompPoly

variable {modulus : ℕ} [P : Mont32Field modulus]

namespace FastField

/-- The canonical natural of a fast element is the residue of its canonical field value. -/
theorem toNat_eq_val_toField (x : FastField modulus) : toNat x = (toField x).val := by
  rw [toField, ZMod.val_natCast, Nat.mod_eq_of_lt toNat_lt_modulus]

/-- Carrier agreement: the canonical natural of `ofField n` is the residue `n.val`. -/
theorem toNat_ofField (n : ZMod modulus) : toNat (ofField n) = n.val := by
  rw [toNat_eq_val_toField, toField_ofField]

theorem ofField_cast_toNat (x : FastField modulus) : ofField (toNat x : ZMod modulus) = x :=
  ofField_toField x

instance : CanonicalNat (FastField modulus) :=
  CanonicalNat.ofToField toNat ofField (fun _ => toNat_lt_modulus) ofField_cast_toNat
    toNat_ofField

instance : ByteCodec (FastField modulus) := ByteCodec.ofCanonicalNat _

/-- The stored Montgomery residue as a raw word; words at or above the modulus decode to
zero. -/
@[inline] instance : PackedRepr (FastField modulus) :=
  PackedRepr.ofWord32 (fun x ↦ x.1)
    (fun v ↦ if h : v < P.modulus32 then ⟨v, by simpa [UInt32.lt_iff_toNat_lt] using h⟩
      else ⟨0, by simp⟩)
    (fun x ↦ by
      have hx : x.1 < P.modulus32 := by
        rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat]; exact x.2
      simp only [hx, ↓reduceDIte]
      rfl)

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

end Montgomery.Native32
