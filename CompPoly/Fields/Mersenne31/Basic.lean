/-
Copyright (c) 2024 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Varun Thakore
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.PrattCertificate

/-!
  # Mersenne prime field `2^{31} - 1`

  This is the field used in Circle STARKs.
-/

namespace Mersenne31
namespace Basic

/-- The Mersenne31 prime modulus `2^31 - 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 31 - 1

/-- The canonical mathematical Mersenne31 field, implemented as integers modulo
`fieldSize`. -/
abbrev Field := ZMod fieldSize

/-- The Mersenne31 modulus is prime, verified by a Pratt certificate. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

/-- Register primality of `fieldSize` for Mathlib instances such as `ZMod.instField`. -/
instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

/-- The canonical Mersenne31 carrier is a field because its modulus is prime. -/
instance : _root_.Field Field := ZMod.instField fieldSize

/-- Mersenne31 has characteristic different from two. -/
instance : NonBinaryField Field where
  char_neq_2 := by
    -- `decide` can discharge this concrete ZMod equality.
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 1)) ≠ 0)

end Basic
end Mersenne31
