/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Data.Bytes.Vector
public meta import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Data.Bytes.Vector
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Concatenation codec of vectors
-/

public meta section

namespace CompPolyTests.VectorBytes

open CompPoly

-- `ZMod 257` is two bytes wide, so a vector of three is six bytes, entries in order.
#guard ByteCodec.width (Vector (ZMod 257) 3) = 6
#guard (ByteCodec.toBytes (#v[1, 2, 256] : Vector (ZMod 257) 3)).toList = [1, 0, 2, 0, 0, 1]
#guard (ByteCodec.toBytes (#v[] : Vector (ZMod 257) 0)).toList = []

#guard (ByteCodec.ofBytes? (ByteCodec.toBytes (#v[1, 2, 256] : Vector (ZMod 257) 3)) :
  Option (Vector (ZMod 257) 3)) = some #v[1, 2, 256]
#guard (DeserializeOption.deserialize (serialize (#v[5, 6] : Vector (ZMod 257) 2) : ByteArray) :
  Option (Vector (ZMod 257) 2)) = some #v[5, 6]
-- One bad entry fails the whole vector.
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 1, 1, 0, 0]⟩ : Option (Vector (ZMod 257) 3)) = none
-- Wrong total size fails.
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 2, 0, 0]⟩ : Option (Vector (ZMod 257) 3)) = none

-- Total entry-by-entry decoding: `n * k` bytes to `n` challenges, `k` bytes each, reduced.
-- The instance is stated at `Vector UInt8 (n * k)`, so the byte length is passed as a product.
#guard Vector.ofBytesEach (F := ZMod 257) (k := 2) 2 #v[2, 0, 5, 0] = #v[2, 5]
#guard Vector.ofBytesEach (F := ZMod 257) (k := 2) 2 #v[1, 1, 3, 1] = #v[0, 2]
#guard Vector.ofBytesEach (F := ZMod 257) (k := 3) 2 #v[2, 0, 0, 5, 0, 0] = #v[2, 5]
#guard (Deserialize.deserialize (β := Vector UInt8 (2 * 2)) #v[2, 0, 5, 0] : Vector (ZMod 257) 2)
  = #v[2, 5]

example (v : Vector (ZMod 257) 3) :
    (DeserializeOption.deserialize (serialize v : ByteArray) : Option (Vector (ZMod 257) 3))
      = some v :=
  ByteCodec.deserialize_serialize v
example : Serialize.IsInjective (Vector (ZMod 257) 3) ByteArray := inferInstance

end CompPolyTests.VectorBytes
