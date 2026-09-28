/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Bivariate.Bytes
public meta import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Bivariate.Bytes
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of bivariate polynomials

The univariate codec nested: a count of `Y`-coefficients, each a univariate polynomial in `X`.
-/

public meta section

namespace CompPolyTests.BivariateBytes

open CompPoly CompPoly.CPolynomial CompPoly.DelimitedCodec

abbrev F := ZMod 257

/-- `1 + (2X) Y`: `Y`-coefficient `0` is the constant `1`, `Y`-coefficient `1` is `2X`. -/
def f : CBivariate F := ofArray #[ofArray #[1], ofArray #[0, 2]]

#guard encode f = [2, 0, 0, 0, 0, 0, 0, 0]
  ++ ([1, 0, 0, 0, 0, 0, 0, 0] ++ [1, 0])
  ++ ([2, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 2, 0])
#guard encode (ofArray #[] : CBivariate F) = List.replicate 8 0
#guard (ofByteArray? (toByteArray f) : Option (CBivariate F)) = some f
#guard (DeserializeOption.deserialize (serialize f : ByteArray) : Option (CBivariate F)) = some f
-- A zero inner polynomial in the last position is trimmed away on decoding.
#guard (ofByteArray? ⟨([(2 : UInt8), 0, 0, 0, 0, 0, 0, 0]
  ++ ([1, 0, 0, 0, 0, 0, 0, 0] ++ [1, 0]) ++ List.replicate 8 0).toArray⟩ : Option (CBivariate F))
  = some (ofArray #[ofArray #[1]])

example (g : CBivariate F) (h : Valid g) :
    (DeserializeOption.deserialize (serialize g : ByteArray) : Option (CBivariate F)) = some g :=
  deserialize_serialize h

end CompPolyTests.BivariateBytes
