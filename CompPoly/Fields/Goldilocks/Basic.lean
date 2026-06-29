/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Varun Thakore
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.PrattCertificate

/-!
# Goldilocks Prime Field `2^{64} - 2^{32} + 1`

This module defines the canonical `ZMod` model of the Goldilocks prime field.
-/

namespace Goldilocks
namespace Basic

/-- The Goldilocks prime modulus, `2^64 - 2^32 + 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 64 - 2 ^ 32 + 1

/-- The canonical mathematical Goldilocks field, implemented as integers modulo
`fieldSize`. -/
abbrev Field := ZMod fieldSize

/-- The Goldilocks modulus is prime, verified by a Pratt certificate. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

/-- Register primality of `fieldSize` for Mathlib instances such as `ZMod.instField`. -/
instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

/-- The canonical Goldilocks carrier is a field because its modulus is prime. -/
instance : _root_.Field Field := ZMod.instField fieldSize

/-- Goldilocks has characteristic different from two. -/
instance : NonBinaryField Field where
  char_neq_2 := by
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 64 - 2 ^ 32 + 1)) ≠ 0)

end Basic
end Goldilocks
