/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Fields.Goldilocks.Bytes
public import CompPoly.Fields.Goldilocks.Bytes

/-!
# Serialization of the fast Goldilocks carrier
-/

public meta section

namespace CompPolyTests.GoldilocksBytes

open CompPoly

#guard ByteCodec.width Goldilocks.Fast.Field = 8
#guard (ByteCodec.toBytes (Goldilocks.Fast.ofField (-1))).toList
  = [0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]
#guard (ByteCodec.toBytes (Goldilocks.Fast.ofField (-1))).toList
  = (ByteCodec.toBytes (-1 : Goldilocks.Field)).toList
#guard (DeserializeOption.deserialize (serialize (Goldilocks.Fast.ofNat 12345) : ByteArray) :
  Option Goldilocks.Fast.Field) = some (Goldilocks.Fast.ofNat 12345)
#guard (Deserialize.deserialize (serialize (Goldilocks.Fast.ofNat 12345) : ByteArray) :
  Goldilocks.Fast.Field) = Goldilocks.Fast.ofNat 12345
-- `p` itself is refused.
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]⟩ :
  Option Goldilocks.Fast.Field) = none

example (n : Goldilocks.Field) :
    ByteCodec.toBytes (Goldilocks.Fast.ofField n) = ByteCodec.toBytes n :=
  Goldilocks.Fast.toBytes_ofField n
example (x : Goldilocks.Fast.Field) :
    (Deserialize.deserialize (serialize x : ByteArray) : Goldilocks.Fast.Field) = x :=
  CanonicalNat.deserialize_serialize_byteArray rfl x

end CompPolyTests.GoldilocksBytes
