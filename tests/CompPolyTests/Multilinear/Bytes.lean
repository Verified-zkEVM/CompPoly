/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Multilinear.Bytes
public meta import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Multilinear.Bytes
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of multilinear polynomials

`CMlPolynomial R n` is `Vector R (2 ^ n)`, so it has the vector codec: `2 ^ n` coefficients in
little-endian index order.
-/

public meta section

namespace CompPolyTests.MultilinearBytes

open CompPoly

abbrev F := ZMod 257

#guard ByteCodec.width (CMlPolynomial F 2) = 8
example : ByteCodec.width (CMlPolynomial F 3) = 16 := by decide

#guard (ByteCodec.toBytes (#v[1, 2, 3, 256] : CMlPolynomial F 2)).toList = [1, 0, 2, 0, 3, 0, 0, 1]
#guard (ByteCodec.toBytes (#v[1, 2, 3, 256] : CMlPolynomialEval F 2)).toList
  = [1, 0, 2, 0, 3, 0, 0, 1]
#guard (ByteCodec.ofBytes? (ByteCodec.toBytes (#v[1, 2, 3, 256] : CMlPolynomial F 2)) :
  Option (CMlPolynomial F 2)) = some #v[1, 2, 3, 256]
#guard (DeserializeOption.deserialize (serialize (#v[5, 6, 7, 8] : CMlPolynomial F 2) : ByteArray) :
  Option (CMlPolynomial F 2)) = some #v[5, 6, 7, 8]
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 2, 0, 3, 0]⟩ : Option (CMlPolynomial F 2)) = none

example (p : CMlPolynomial F 4) :
    (DeserializeOption.deserialize (serialize p : ByteArray) : Option (CMlPolynomial F 4))
      = some p :=
  ByteCodec.deserialize_serialize p
example : Serialize.IsInjective (CMlPolynomial F 4) ByteArray := inferInstance
example : HasSize (CMlPolynomial F 4) UInt8 := inferInstance

end CompPolyTests.MultilinearBytes
