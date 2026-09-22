/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Binary.BF64.Impl
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of `BF64`

A `BF64` element is a bit pattern in the polynomial basis of
`GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`, bit `i` the coefficient of `X^i`. Its canonical natural
is that pattern read as an integer, and its encoding is the eight little-endian bytes of the
word, the same bytes a `u64::to_le_bytes` of the word gives. No other presentation of
`GF(2^64)` is implied.
-/

@[expose] public section

namespace BF64

open CompPoly

instance : CanonicalNat BF64 :=
  CanonicalNat.ofBitVec toBitVec ofBitVec ofBitVec_toBitVec toBitVec_ofBitVec

instance : ByteCodec BF64 := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound BF64 = 2 ^ 64 := rfl

@[simp] theorem canonicalNat_toNat (x : BF64) : CanonicalNat.toNat x = x.toBitVec.toNat := rfl

@[simp] theorem byteCodec_width : ByteCodec.width BF64 = 8 := by
  show Bytes.bytesFor (2 ^ 64) = 8
  rw [Bytes.bytesFor_two_pow (by norm_num)]

end BF64
