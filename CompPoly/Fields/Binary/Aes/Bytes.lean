/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Binary.Aes.Arithmetic
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of the AES field

An `AesField` element is a bit pattern in the polynomial basis of
`GF(2)[X] / (X^8 + X^4 + X^3 + X + 1)`, bit `i` the coefficient of `X^i`, so it encodes as the
one byte `toBitVec`. Level three of the binary tower has the same cardinality and a different
basis; the two encodings are not interchangeable, and `AesField.toGhash` remains the only
sanctioned bridge out of this presentation.
-/

@[expose] public section

namespace AesField

open CompPoly

instance : CanonicalNat AesField :=
  CanonicalNat.ofBitVec toBitVec ofBitVec ofBitVec_toBitVec toBitVec_ofBitVec

instance : ByteCodec AesField := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound AesField = 2 ^ 8 := rfl

@[simp] theorem canonicalNat_toNat (x : AesField) : CanonicalNat.toNat x = (toBitVec x).toNat :=
  rfl

@[simp] theorem byteCodec_width : ByteCodec.width AesField = 1 := by
  show Bytes.bytesFor (2 ^ 8) = 1
  rw [Bytes.bytesFor_two_pow (by norm_num)]

end AesField
