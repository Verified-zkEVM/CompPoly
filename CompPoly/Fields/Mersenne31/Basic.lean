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

@[reducible]
def fieldSize : Nat := 2 ^ 31 - 1

abbrev Field := ZMod fieldSize

theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance : _root_.Field Field := ZMod.instField fieldSize

instance : NonBinaryField Field where
  char_neq_2 := by
    -- `decide` can discharge this concrete ZMod equality.
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 1)) ≠ 0)

end Basic
end Mersenne31
