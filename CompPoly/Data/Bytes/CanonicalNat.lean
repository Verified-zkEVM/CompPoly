/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Classes.CanonicalNat
public import CompPoly.Data.Bytes.LittleEndian
public import CompPoly.Data.Bytes.Codec

/-!
# Byte codecs from canonical naturals

A type with a `CanonicalNat` structure has a fixed-width byte codec: the little-endian bytes
of `toNat`, `bytesFor bound` of them, decoded by `ofNat?`. This is `ByteCodec.ofCanonicalNat`,
a definition rather than an instance so that a composite type may choose a different codec
(an extension field concatenates its coefficients) while still having a canonical natural.

The same structure gives the total decoder used for challenges: `ofBytesModOrder` reads any
number of bytes as an integer and reduces it modulo `bound`. Reading back an exact-width
encoding this way recovers the element (`ofBytesModOrder_toBytes`); reading more bytes than
the width is what makes the result close to uniform.

`ZMod p` receives both: `instCanonicalNatZMod` from `CompPoly.Data.Classes.CanonicalNat` and the
derived `ByteCodec (ZMod p)` here, so every spec prime field in `CompPoly.Fields` serializes.
-/

@[expose] public section

universe u

namespace CompPoly

open Bytes

variable {F : Type u}

/-- The fixed-width byte codec of a type with canonical naturals: `bytesFor bound` little-endian
bytes of `toNat`, decoded by `ofNat?`. -/
@[instance_reducible]
def ByteCodec.ofCanonicalNat (F : Type u) [CanonicalNat F] : ByteCodec F where
  width := bytesFor (CanonicalNat.bound F)
  toBytes x := toVecLE _ (CanonicalNat.toNat x)
  ofBytes? v := CanonicalNat.ofNat? (ofVecLE v)
  ofBytes?_toBytes x := by
    have h : CanonicalNat.toNat x < 256 ^ bytesFor (CanonicalNat.bound F) :=
      Nat.lt_of_lt_of_le (CanonicalNat.toNat_lt x) (le_pow_bytesFor _)
    rw [ofVecLE_toVecLE_of_lt h, CanonicalNat.ofNat?_toNat]

namespace CanonicalNat

variable [CanonicalNat F]

/-- Read any byte string as a little-endian integer and reduce it modulo `bound`. Total, and
close to uniform when the string is longer than `bytesFor bound`. -/
def ofBytesModOrder {n : ℕ} (v : Vector UInt8 n) : F := ofNat (ofVecLE v)

/-- `ofBytesModOrder` on a `ByteArray` of any size. -/
def ofByteArrayModOrder (b : ByteArray) : F := ofNat (ofByteArrayLE b)

instance {n : ℕ} : Deserialize F (Vector UInt8 n) := ⟨ofBytesModOrder⟩

instance : Deserialize F ByteArray := ⟨ofByteArrayModOrder⟩

@[simp] theorem deserialize_vector_eq {n : ℕ} (v : Vector UInt8 n) :
    (Deserialize.deserialize v : F) = ofBytesModOrder v := rfl

@[simp] theorem deserialize_byteArray_eq (b : ByteArray) :
    (Deserialize.deserialize b : F) = ofByteArrayModOrder b := rfl

/-- Reading back an exact-width little-endian encoding modulo the order recovers the element. -/
theorem ofBytesModOrder_toVecLE_toNat (x : F) :
    ofBytesModOrder (toVecLE (bytesFor (bound F)) (toNat x)) = x := by
  have h : toNat x < 256 ^ bytesFor (bound F) :=
    Nat.lt_of_lt_of_le (toNat_lt x) (le_pow_bytesFor _)
  rw [ofBytesModOrder, ofVecLE_toVecLE_of_lt h, ofNat_toNat]

theorem ofByteArrayModOrder_toByteArrayLE_toNat (x : F) :
    ofByteArrayModOrder (toByteArrayLE (bytesFor (bound F)) (toNat x)) = x := by
  have h : toNat x < 256 ^ bytesFor (bound F) :=
    Nat.lt_of_lt_of_le (toNat_lt x) (le_pow_bytesFor _)
  rw [ofByteArrayModOrder, ofByteArrayLE_toByteArrayLE_of_lt h, ofNat_toNat]

end CanonicalNat

/-- Reading back the `ofCanonicalNat` encoding modulo the order recovers the element. -/
theorem ByteCodec.ofBytesModOrder_toBytes [CanonicalNat F] (x : F) :
    CanonicalNat.ofBytesModOrder ((ByteCodec.ofCanonicalNat F).toBytes x) = x :=
  CanonicalNat.ofBytesModOrder_toVecLE_toNat x

/-! ## `ZMod` -/

/-- The little-endian residue codec of `ZMod p`, `bytesFor p` bytes wide. -/
instance instByteCodecZMod (p : ℕ) [NeZero p] : ByteCodec (ZMod p) := ByteCodec.ofCanonicalNat _

@[simp] theorem ByteCodec.width_zmod (p : ℕ) [NeZero p] : ByteCodec.width (ZMod p) = bytesFor p :=
  rfl

@[simp] theorem ByteCodec.toBytes_zmod {p : ℕ} [NeZero p] (x : ZMod p) :
    ByteCodec.toBytes x = toVecLE (bytesFor p) x.val := rfl

@[simp] theorem ByteCodec.ofBytes?_zmod {p : ℕ} [NeZero p] (v : Vector UInt8 (bytesFor p)) :
    ByteCodec.ofBytes? v = (CanonicalNat.ofNat? (ofVecLE v) : Option (ZMod p)) := rfl

end CompPoly

/-! ## Round trips through the class interfaces

For a type whose codec is `ByteCodec.ofCanonicalNat`, the total decoder inverts the serializer
at the codec's width. Together with `ByteCodec.deserialize_serialize` (the partial decoder) and
the `Serialize.IsInjective` instances, this is the full round-trip story a protocol relies on.
-/

namespace CompPoly

/-- The total decoder inverts the serializer at the codec's own width, whenever the codec is
the one derived from canonical naturals. -/
theorem CanonicalNat.deserialize_serialize {F : Type u} [CanonicalNat F] [inst : ByteCodec F]
    (h : inst = ByteCodec.ofCanonicalNat F) (x : F) :
    (Deserialize.deserialize (serialize x : Vector UInt8 (ByteCodec.width F)) : F) = x := by
  subst h
  exact ofBytesModOrder_toVecLE_toNat x

theorem CanonicalNat.deserialize_serialize_byteArray {F : Type u} [CanonicalNat F]
    [inst : ByteCodec F] (h : inst = ByteCodec.ofCanonicalNat F) (x : F) :
    (Deserialize.deserialize (serialize x : ByteArray) : F) = x := by
  subst h
  exact ofByteArrayModOrder_toByteArrayLE_toNat x

/-- `ZMod p`: the total decoder inverts the serializer. -/
theorem deserialize_serialize_zmod {p : ℕ} [NeZero p] (x : ZMod p) :
    (Deserialize.deserialize (serialize x : ByteArray) : ZMod p) = x :=
  CanonicalNat.deserialize_serialize_byteArray rfl x

end CompPoly
