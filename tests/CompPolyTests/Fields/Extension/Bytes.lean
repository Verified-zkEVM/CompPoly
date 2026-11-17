/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Fields.Extension.Bytes
public meta import CompPoly.Fields.BabyBear.Basic
public meta import CompPoly.Fields.BabyBear.Ext4
public meta import CompPoly.Fields.KoalaBear.Basic
public meta import CompPoly.Fields.KoalaBear.Ext6
public import CompPoly.Fields.Extension.Bytes
public import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Fields.BabyBear.Ext4
public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.KoalaBear.Ext6

/-!
# Serialization of field extensions

An extension element is its coefficient vector, coefficient `i` at byte offset `i * width F`.
-/

public meta section

namespace CompPolyTests.ExtensionBytes

open CompPoly CompPoly.Extension

#guard ByteCodec.width BabyBear.Ext4 = 16
#guard ByteCodec.width KoalaBear.Ext6 = 24
example : ByteCodec.width BabyBear.Ext4 = 16 := by decide

-- `ofBase c` is `c` in coefficient zero.
#guard (ByteCodec.toBytes (Ext.ofBase (-1) : BabyBear.Ext4)).toList
  = [0, 0, 0, 0x78] ++ List.replicate 12 0
-- `gen` is `1` in coefficient one.
#guard (ByteCodec.toBytes (Ext.gen : BabyBear.Ext4)).toList
  = [0, 0, 0, 0, 1, 0, 0, 0] ++ List.replicate 8 0
#guard (ByteCodec.toBytes (Ext.gen ^ 5 : KoalaBear.Ext6)).toList
  = List.replicate 20 0 ++ [1, 0, 0, 0]

-- Round trips through the partial decoder and its class form.
#guard (ByteCodec.ofBytes? (ByteCodec.toBytes (Ext.gen ^ 3 + 7 : BabyBear.Ext4)) :
  Option BabyBear.Ext4) = some (Ext.gen ^ 3 + 7)
#guard (DeserializeOption.deserialize (serialize (Ext.gen ^ 7 - 3 : KoalaBear.Ext6) : ByteArray) :
  Option KoalaBear.Ext6) = some (Ext.gen ^ 7 - 3)
-- A coefficient at or above `p` is refused.
#guard (ByteCodec.ofByteArray?
  ⟨(List.replicate 12 (0 : UInt8) ++ [0xff, 0xff, 0xff, 0xff]).toArray⟩ :
  Option BabyBear.Ext4) = none

-- The total decoder reads `d` challenges of `k` bytes each, coefficient by coefficient.
#guard (Deserialize.deserialize
  (Vector.ofFn (n := BabyBear.ext4Params.toExtensionParams.d * 8) fun i =>
    if i.1 = 0 then (1 : UInt8) else 0) : BabyBear.Ext4) = Ext.ofBase 1

example (x : BabyBear.Ext4) :
    (DeserializeOption.deserialize (serialize x : ByteArray) : Option BabyBear.Ext4) = some x :=
  ByteCodec.deserialize_serialize x
example : Serialize.IsInjective KoalaBear.Ext6 ByteArray := inferInstance

end CompPolyTests.ExtensionBytes
