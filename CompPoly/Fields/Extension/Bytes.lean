/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Arithmetic
public import CompPoly.Data.Bytes.Vector
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of field extensions

An element of `Ext P` is its coefficient vector, ascending powers of the adjoined root, and it
encodes as the concatenation of the coefficient encodings: `P.d * width F` bytes. This is how
arkworks and plonky3 serialize extension fields, and it is *not* the little-endian expansion of
the element's base-`q` canonical natural, which is why `Ext` carries a `ByteCodec` but no
`CanonicalNat`.

A challenge in `Ext P` is likewise read coefficient by coefficient from `P.d * k` bytes
(`Deserialize (Ext P) (Vector UInt8 (P.d * k))`), matching how a sponge over the base field
samples extension elements.

`CompPoly.Data.Bytes.CanonicalNat` is imported so that an extension of a `ZMod` base field
serializes with no further imports.
-/

@[expose] public section

namespace CompPoly.Extension

namespace Ext

variable {F : Type*} {P : ExtensionParams F}

instance [ByteCodec F] : ByteCodec (Ext P) where
  width := P.d * ByteCodec.width F
  toBytes x := ByteCodec.toBytes x.coeffs
  ofBytes? b := (ByteCodec.ofBytes? b).map Ext.mk
  ofBytes?_toBytes x := by simp only [ByteCodec.ofBytes?_toBytes, Option.map_some]

@[simp] theorem byteCodec_width [ByteCodec F] :
    ByteCodec.width (Ext P) = P.d * ByteCodec.width F := rfl

theorem toBytes_eq [ByteCodec F] (x : Ext P) : ByteCodec.toBytes x = ByteCodec.toBytes x.coeffs :=
  rfl

instance {k : ℕ} [Deserialize F (Vector UInt8 k)] : Deserialize (Ext P) (Vector UInt8 (P.d * k)) :=
  ⟨fun b => ⟨Deserialize.deserialize b⟩⟩

end Ext

end CompPoly.Extension
