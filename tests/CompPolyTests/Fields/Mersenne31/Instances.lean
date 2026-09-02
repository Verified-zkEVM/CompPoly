/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/
module

public import CompPoly.Fields.Mersenne31.Fast

/-!
# Mersenne31 Field Instance Tests

Regression checks for the canonical and fast Mersenne31 field instances.
-/

public section

namespace Mersenne31

example : Fact (Nat.Prime fieldSize) := inferInstance

example : _root_.Field Field := inferInstance

example : NonBinaryField Field := inferInstance

example : (2 : Field) ≠ 0 := by
  exact NonBinaryField.char_neq_2

end Mersenne31

namespace Mersenne31.Fast

example : _root_.Field Field := inferInstance

example : NonBinaryField Field := inferInstance

end Mersenne31.Fast
