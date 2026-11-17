/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Fields.Binary.BF64.Bytes
public meta import CompPoly.Fields.Binary.BF128Ghash.Bytes
public meta import CompPoly.Fields.Binary.Aes.Bytes
public meta import CompPoly.Fields.Binary.Tower.Bytes
public import CompPoly.Fields.Binary.BF64.Bytes
public import CompPoly.Fields.Binary.BF128Ghash.Bytes
public import CompPoly.Fields.Binary.Aes.Bytes
public import CompPoly.Fields.Binary.Tower.Bytes

/-!
# Serialization of the binary fields

Each binary presentation encodes the bit pattern of its own declared basis, little-endian.
Checked here: widths, the bit convention (bit `i` is byte `i / 8`, bit `i % 8`), round trips,
that the two level-seven carriers agree, and that same-width presentations are *different*
types whose bytes are not interchanged by anything in this layer.
-/

public meta section

namespace CompPolyTests.BinaryBytes

open CompPoly ConcreteBinaryTower

/-! ## Widths -/

#guard ByteCodec.width BF64 = 8
#guard ByteCodec.width BF128Ghash.ConcreteBF128Ghash = 16
#guard ByteCodec.width AesField = 1
#guard ByteCodec.width (ConcreteBTField 3) = 1
#guard ByteCodec.width (ConcreteBTField 7) = 16
#guard ByteCodec.width Fast.FastBT128 = 16

/-! ## Bit convention: little-endian bytes of the coordinate word -/

#guard (ByteCodec.toBytes (BF64.ofBitVec 0x0102#64)).toList = [2, 1, 0, 0, 0, 0, 0, 0]
#guard (ByteCodec.toBytes (BF64.ofBitVec (1#64 <<< 63))).toList = [0, 0, 0, 0, 0, 0, 0, 0x80]
#guard (ByteCodec.toBytes (BF128Ghash.ofBitVec (1#128 <<< 127))).toList
  = List.replicate 15 0 ++ [0x80]
#guard (ByteCodec.toBytes (AesField.ofBitVec 0x53#8)).toList = [0x53]
#guard (ByteCodec.toBytes (ConcreteBTField.ofBitVec (k := 3) 0x53#8)).toList = [0x53]
-- `FastBT128 = ⟨lo, hi⟩`, `lo` first.
#guard (ByteCodec.toBytes (Fast.FastBT128.mk 0x0201 0x0403)).toList
  = [1, 2, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0, 0, 0, 0, 0]

/-! ## Round trips -/

#guard (ByteCodec.ofBytes? (ByteCodec.toBytes (BF64.ofBitVec 0xdeadbeef#64)) : Option BF64)
  = some (BF64.ofBitVec 0xdeadbeef#64)
#guard (DeserializeOption.deserialize
  (serialize (BF128Ghash.ofBitVec 0xdeadbeef#128) : ByteArray) :
  Option BF128Ghash.ConcreteBF128Ghash) = some (BF128Ghash.ofBitVec 0xdeadbeef#128)
#guard (DeserializeOption.deserialize (serialize (AesField.ofBitVec 0xa7#8) : ByteArray) :
  Option AesField) = some (AesField.ofBitVec 0xa7#8)
#guard (DeserializeOption.deserialize
  (serialize (Fast.FastBT128.mk 0x0201 0x0403) : ByteArray) : Option Fast.FastBT128)
  = some (Fast.FastBT128.mk 0x0201 0x0403)
-- Exact-width decoding of a bit-pattern field never fails: the bound is `2 ^ (8 * width)`.
#guard (ByteCodec.ofByteArray? ⟨List.replicate 8 0xff |>.toArray⟩ : Option BF64) ≠ none
-- The total decoder truncates to the width.
#guard (Deserialize.deserialize (⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩ : ByteArray) : BF64)
  = BF64.ofBitVec 0x0807060504030201#64

/-! ## The two level-seven carriers agree -/

#guard (ByteCodec.toBytes (Fast.FastBT128.toConcrete (Fast.FastBT128.mk 0x0201 0x0403))).toList
  = (ByteCodec.toBytes (Fast.FastBT128.mk 0x0201 0x0403)).toList
example (v : Fast.FastBT128) :
    (ByteCodec.toBytes (Fast.FastBT128.toConcrete v)).toList = (ByteCodec.toBytes v).toList :=
  Fast.FastBT128.toList_toBytes_toConcrete v
example (v : Fast.FastBT128) :
    (serialize (Fast.FastBT128.toConcrete v) : ByteArray) = serialize v :=
  Fast.FastBT128.toByteArray_toConcrete v

/-! ## Round-trip theorems at the concrete types -/

example (x : BF64) : (Deserialize.deserialize (serialize x : ByteArray) : BF64) = x :=
  CanonicalNat.deserialize_serialize_byteArray rfl x
example (x : AesField) :
    (DeserializeOption.deserialize (serialize x : ByteArray) : Option AesField) = some x :=
  ByteCodec.deserialize_serialize x
example : Serialize.IsInjective (ConcreteBTField 7) ByteArray := inferInstance

end CompPolyTests.BinaryBytes
