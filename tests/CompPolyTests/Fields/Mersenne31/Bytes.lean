/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Fields.Mersenne31.Bytes
public import CompPoly.Fields.Mersenne31.Bytes

/-!
# Serialization of the fast Mersenne31 carrier
-/

public meta section

namespace CompPolyTests.Mersenne31Bytes

open CompPoly

#guard ByteCodec.width Mersenne31.Fast.Field = 4
-- `p = 2^31 - 1`, so `-1 = 0x7ffffffe`.
#guard (ByteCodec.toBytes (Mersenne31.Fast.ofField (-1))).toList = [0xfe, 0xff, 0xff, 0x7f]
#guard (ByteCodec.toBytes (Mersenne31.Fast.ofField (-1))).toList
  = (ByteCodec.toBytes (-1 : Mersenne31.Field)).toList
#guard (DeserializeOption.deserialize (serialize (Mersenne31.Fast.ofNat 4242) : ByteArray) :
  Option Mersenne31.Fast.Field) = some (Mersenne31.Fast.ofNat 4242)
-- `p` itself and anything with the top bit set are refused.
#guard (ByteCodec.ofByteArray? ⟨#[0xff, 0xff, 0xff, 0x7f]⟩ : Option Mersenne31.Fast.Field) = none
#guard (ByteCodec.ofByteArray? ⟨#[0, 0, 0, 0x80]⟩ : Option Mersenne31.Fast.Field) = none

example (n : Mersenne31.Field) :
    ByteCodec.toBytes (Mersenne31.Fast.ofField n) = ByteCodec.toBytes n :=
  Mersenne31.Fast.toBytes_ofField n
example (x : Mersenne31.Fast.Field) :
    (Deserialize.deserialize (serialize x : ByteArray) : Mersenne31.Fast.Field) = x :=
  CanonicalNat.deserialize_serialize_byteArray rfl x

end CompPolyTests.Mersenne31Bytes
