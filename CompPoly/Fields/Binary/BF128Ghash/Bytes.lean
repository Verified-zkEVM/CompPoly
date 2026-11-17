/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Binary.BF128Ghash.Arithmetic
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of the GHASH field

A `ConcreteBF128Ghash` element is a bit pattern in the polynomial basis of
`GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)`, bit `i` the coefficient of `X^i`. Its canonical
natural is that pattern read as an integer and its encoding the sixteen little-endian bytes of
the word. This is the field's own presentation; GCM's big-endian, bit-reflected block format
is a separate wire codec and is not provided here.
-/

@[expose] public section

namespace BF128Ghash

open CompPoly

namespace ConcreteBF128Ghash

instance : CanonicalNat ConcreteBF128Ghash :=
  CanonicalNat.ofBitVec toBitVec ofBitVec ofBitVec_toBitVec toBitVec_ofBitVec

instance : ByteCodec ConcreteBF128Ghash := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound ConcreteBF128Ghash = 2 ^ 128 := rfl

@[simp] theorem canonicalNat_toNat (x : ConcreteBF128Ghash) :
    CanonicalNat.toNat x = x.toBitVec.toNat := rfl

@[simp] theorem byteCodec_width : ByteCodec.width ConcreteBF128Ghash = 16 := by
  show Bytes.bytesFor (2 ^ 128) = 16
  rw [Bytes.bytesFor_two_pow (by norm_num)]

end ConcreteBF128Ghash

end BF128Ghash
