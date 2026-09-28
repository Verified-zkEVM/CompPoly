/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Multivariate.Bytes
public meta import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Multivariate.Bytes
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of multivariate polynomials

A `u64` term count, then the terms in key order, each `n` exponents as `u64` words and a
coefficient. Terms are compared by their `toList` after decoding, which is how `Lawful`
decides equality.
-/

public meta section

namespace CompPolyTests.MultivariateBytes

open CompPoly CompPoly.DelimitedCodec CPoly

abbrev F := ZMod 257

/-- `3 + 5 X₀² X₁` in two variables. -/
def p : CMvPolynomial 2 F := Lawful.fromUnlawful (Unlawful.ofList [(#m[2, 1], 5), (#m[0, 0], 3)])

/-! ## Monomials -/

#guard encode (#m[2, 1] : CMvMonomial 2) = [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
#guard decode? (α := CMvMonomial 2) [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9]
  = some (#m[2, 1], [9])

/-! ## Polynomials -/

-- Two terms, the constant term first in key order.
#guard encode p = [2, 0, 0, 0, 0, 0, 0, 0]
  ++ ([0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [3, 0])
  ++ ([2, 0, 0, 0, 0, 0, 0, 0] ++ [1, 0, 0, 0, 0, 0, 0, 0] ++ [5, 0])
#guard encode (0 : CMvPolynomial 2 F) = List.replicate 8 0

#guard (ofByteArray? (toByteArray p) : Option (CMvPolynomial 2 F)) = some p
#guard (DeserializeOption.deserialize (serialize p : ByteArray) : Option (CMvPolynomial 2 F))
  = some p
-- Decoding drops zero coefficients, so a stream with a zero term yields the canonical polynomial.
#guard (ofByteArray?
  ⟨([(1 : UInt8)] ++ List.replicate 7 0 ++ List.replicate 16 0 ++ [0, 0]).toArray⟩ :
  Option (CMvPolynomial 2 F)) = some 0
-- Decoding sorts, so term order in the stream does not matter for the decoded polynomial.
#guard (ofByteArray? ⟨([(2 : UInt8), 0, 0, 0, 0, 0, 0, 0]
  ++ ([2, 0, 0, 0, 0, 0, 0, 0] ++ [1, 0, 0, 0, 0, 0, 0, 0] ++ [5, 0])
  ++ ([0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [3, 0])).toArray⟩ :
  Option (CMvPolynomial 2 F)) = some p
-- A truncated term is refused.
#guard (ofByteArray? ⟨([(1 : UInt8), 0, 0, 0, 0, 0, 0, 0] ++ [2, 0, 0, 0, 0, 0, 0, 0]).toArray⟩ :
  Option (CMvPolynomial 2 F)) = none

example (q : CMvPolynomial 2 F) (h : q.1.toList.length < 2 ^ 64)
    (he : ∀ t ∈ q.1.toList, ∀ e ∈ (t.1 : Vector ℕ 2).toList, e < 2 ^ 64) :
    (DeserializeOption.deserialize (serialize q : ByteArray) : Option (CMvPolynomial 2 F))
      = some q :=
  deserialize_serialize ((CMvPolynomial.valid_iff q).mpr ⟨h, fun t ht => ⟨he t ht, trivial⟩⟩)

end CompPolyTests.MultivariateBytes
