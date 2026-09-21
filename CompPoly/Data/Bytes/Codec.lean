/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Classes.Serialize
public import CompPoly.Data.Classes.HasSize

/-!
# Fixed-width byte codecs

`ByteCodec F` is a fixed-width byte encoding of `F` with a decoder that succeeds on every
encoding. Its single law, `ofBytes?_toBytes`, makes `toBytes` injective, and from it the
protocol-facing classes follow for free: `HasSize F UInt8`, `Serialize F ByteArray` with
`Serialize.IsInjective`, `DeserializeOption`, and `Serde`, together with the same for
`Vector UInt8 (width F)`.

The encoding is a property of the *value*, not of the carrier: two carriers of the same field
must give the same bytes for the same element. Scalar fields derive their codec from
`CanonicalNat` (`ByteCodec.ofCanonicalNat`, in `CompPoly.Data.Bytes.CanonicalNat`); composite
types such as extensions and degree-bounded polynomials concatenate the codecs of their parts.
-/

@[expose] public section

universe u

namespace CompPoly

/-- A fixed-width byte encoding of `F` whose decoder recovers every encoded element. -/
class ByteCodec (F : Type u) where
  /-- The number of bytes of every encoding. -/
  width : ℕ
  /-- Encode an element. -/
  toBytes : F → Vector UInt8 width
  /-- Decode `width` bytes, failing on strings that encode no element. -/
  ofBytes? : Vector UInt8 width → Option F
  ofBytes?_toBytes (x : F) : ofBytes? (toBytes x) = some x

namespace ByteCodec

variable {F : Type u} [ByteCodec F]

attribute [simp] ofBytes?_toBytes

theorem toBytes_injective : Function.Injective (toBytes : F → Vector UInt8 (width F)) := by
  intro x y h
  have := congrArg ofBytes? h
  simpa only [ofBytes?_toBytes, Option.some.injEq] using this

@[simp]
theorem toBytes_inj {x y : F} : toBytes x = toBytes y ↔ x = y :=
  toBytes_injective.eq_iff

/-- The encoding as a `ByteArray` of size `width F`. -/
def toByteArray (x : F) : ByteArray := ⟨(toBytes x).toArray⟩

@[simp] theorem data_toByteArray (x : F) : (toByteArray x).data = (toBytes x).toArray := rfl

@[simp] theorem size_toByteArray (x : F) : (toByteArray x).size = width F := by
  simp only [toByteArray, ByteArray.size, Vector.size_toArray]

theorem toByteArray_injective : Function.Injective (toByteArray : F → ByteArray) := by
  intro x y h
  have := congrArg ByteArray.data h
  simp only [data_toByteArray, Vector.toArray_inj] at this
  exact toBytes_injective this

/-- Decode a `ByteArray`, failing unless it has size `width F` and encodes an element. -/
def ofByteArray? (b : ByteArray) : Option F :=
  if h : b.size = width F then ofBytes? ⟨b.data, h⟩ else none

@[simp]
theorem ofByteArray?_toByteArray (x : F) : ofByteArray? (toByteArray x) = some x := by
  unfold ofByteArray?
  split
  · exact ofBytes?_toBytes x
  · exact absurd (size_toByteArray x) (by assumption)

/-! ## Derived protocol interfaces -/

instance : HasSize F UInt8 where
  size := width F
  toFun := ⟨toBytes, toBytes_injective⟩

instance : Serialize F ByteArray := ⟨toByteArray⟩

instance : Serialize.IsInjective F ByteArray := ⟨toByteArray_injective⟩

instance : DeserializeOption F ByteArray := ⟨ofByteArray?⟩

instance : Serde F ByteArray where

instance : Serialize F (Vector UInt8 (width F)) := ⟨toBytes⟩

instance : Serialize.IsInjective F (Vector UInt8 (width F)) := ⟨toBytes_injective⟩

instance : DeserializeOption F (Vector UInt8 (width F)) := ⟨ofBytes?⟩

instance : Serde F (Vector UInt8 (width F)) where

@[simp] theorem serialize_eq_toByteArray (x : F) : (serialize x : ByteArray) = toByteArray x := rfl

@[simp] theorem serialize_eq_toBytes (x : F) :
    (serialize x : Vector UInt8 (width F)) = toBytes x := rfl

@[simp] theorem deserialize_byteArray_eq (b : ByteArray) :
    (DeserializeOption.deserialize b : Option F) = ofByteArray? b := rfl

@[simp] theorem deserialize_vector_eq (v : Vector UInt8 (width F)) :
    (DeserializeOption.deserialize v : Option F) = ofBytes? v := rfl

theorem deserialize_serialize (x : F) :
    (DeserializeOption.deserialize (serialize x : ByteArray) : Option F) = some x :=
  ofByteArray?_toByteArray x

end ByteCodec

end CompPoly
