/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Univariate.Bytes
public meta import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Univariate.Bytes
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of univariate polynomials

The fixed-width codec of `degreeLT n` and the self-delimiting codec of `CPolynomial`, over
`ZMod 257` (two bytes per coefficient) so that the byte layout is legible.
-/

public meta section

namespace CompPolyTests.UnivariateBytes

open CompPoly CompPoly.CPolynomial CompPoly.DelimitedCodec

abbrev F := ZMod 257

/-! ## Fixed width: `degreeLT n` -/

#guard ByteCodec.width ↥(degreeLT (R := F) 4) = 8
example : ByteCodec.width ↥(degreeLT (R := F) 4) = 8 := by decide

-- `1 + 2X`, padded to four coefficients.
#guard (ByteCodec.toBytes (ofCoeffVector 4 (#v[1, 2, 0, 0] : Vector F 4))).toList
  = [1, 0, 2, 0, 0, 0, 0, 0]
-- Padding does not change the polynomial.
#guard (ofCoeffVector 4 (#v[1, 2, 0, 0] : Vector F 4)).1 = ofArray #[1, 2]
#guard (ofCoeffVector 4 (#v[0, 0, 0, 0] : Vector F 4)).1 = 0
-- Round trip, with the decoded polynomial trimmed.
#guard ((ByteCodec.ofBytes? (ByteCodec.toBytes (ofCoeffVector 3 (#v[5, 0, 7] : Vector F 3))) :
  Option ↥(degreeLT (R := F) 3)).map Subtype.val) = some (ofArray #[5, 0, 7])
#guard ((ByteCodec.ofByteArray? ⟨#[1, 0, 2, 0, 0, 0, 0, 0]⟩ :
  Option ↥(degreeLT (R := F) 4)).map Subtype.val) = some (ofArray #[1, 2])
-- A coefficient at or above `p` is refused.
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 1, 1, 0, 0, 0, 0]⟩ : Option ↥(degreeLT (R := F) 4)) = none
-- Wrong length is refused.
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 2, 0]⟩ : Option ↥(degreeLT (R := F) 4)) = none

example (p : ↥(degreeLT (R := F) 4)) :
    (DeserializeOption.deserialize (serialize p : ByteArray) : Option ↥(degreeLT (R := F) 4))
      = some p :=
  ByteCodec.deserialize_serialize p
example : Serialize.IsInjective ↥(degreeLT (R := F) 4) ByteArray := inferInstance
example : HasSize ↥(degreeLT (R := F) 4) UInt8 := inferInstance

/-! ## Self-delimiting: `CPolynomial` -/

-- `1 + 2X + 256X^2`: a `u64` count of three, then the coefficients.
#guard encode (ofArray #[1, 2, 256] : CPolynomial F) = [3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1]
-- The zero polynomial is an empty coefficient list.
#guard encode (0 : CPolynomial F) = List.replicate 8 0
-- Trailing zeros are not stored, so they are not encoded.
#guard encode (ofArray #[1, 0, 0] : CPolynomial F) = [1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
-- Round trips.
#guard (ofByteArray? (toByteArray (ofArray #[1, 2, 256] : CPolynomial F)) : Option (CPolynomial F))
  = some (ofArray #[1, 2, 256])
#guard (DeserializeOption.deserialize (serialize (ofArray #[9, 0, 9] : CPolynomial F) : ByteArray) :
  Option (CPolynomial F)) = some (ofArray #[9, 0, 9])
-- Decoding trims: a stream that spells out trailing zeros still yields the canonical polynomial.
#guard (ofByteArray? ⟨#[2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]⟩ : Option (CPolynomial F))
  = some (ofArray #[1])
-- Missing coefficients and leftover bytes are refused.
#guard (ofByteArray? ⟨#[1, 0, 0, 0, 0, 0, 0, 0]⟩ : Option (CPolynomial F)) = none
#guard (ofByteArray? ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]⟩ : Option (CPolynomial F)) = none
-- Decoding consumes one polynomial and returns the rest.
#guard decode? (α := CPolynomial F) [1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 8, 8]
  = some (ofArray #[4], [8, 8])

-- The self-delimiting encoding is the count followed by the fixed-width encoding at `n = size`.
#guard encode (ofArray #[1, 2, 256] : CPolynomial F)
  = encodeU64 3 ++ (ByteCodec.toBytes (ofCoeffVector 3 (#v[1, 2, 256] : Vector F 3))).toList
example (p : CPolynomial F) :
    encode p = encodeU64 p.val.size
      ++ (ByteCodec.toBytes (⟨p, mem_degreeLT_iff_size_le.mpr le_rfl⟩ :
          ↥(degreeLT (R := F) p.val.size))).toList :=
  encode_eq_encodeU64_append_toBytes p

/-! ## Round trip and injectivity for every polynomial that fits -/

example (p : CPolynomial F) (h : p.val.size < 2 ^ 64) :
    (DeserializeOption.deserialize (serialize p : ByteArray) : Option (CPolynomial F)) = some p :=
  deserialize_serialize ((valid_iff_size_lt p).mpr h)
example (p q : CPolynomial F) (hp : p.val.size < 2 ^ 64) (hq : q.val.size < 2 ^ 64)
    (h : encode p = encode q) : p = q :=
  encode_inj ((valid_iff_size_lt p).mpr hp) ((valid_iff_size_lt q).mpr hq) h

end CompPolyTests.UnivariateBytes
