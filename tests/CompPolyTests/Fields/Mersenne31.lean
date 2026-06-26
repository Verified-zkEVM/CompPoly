/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Lacombe
-/

import CompPoly.Fields.Mersenne31

/-!
# Mersenne31 Field Tests

Regression checks for the canonical and fast Mersenne31 field surfaces.
-/

namespace Mersenne31

example : Fact (Nat.Prime Basic.fieldSize) := inferInstance

example : _root_.Field Basic.Field := inferInstance

example : NonBinaryField Basic.Field := inferInstance

example : (2 : Basic.Field) ≠ 0 := by
  exact NonBinaryField.char_neq_2

end Mersenne31

namespace Mersenne31.Fast

example : _root_.Field Field := inferInstance

example : NonBinaryField Field := inferInstance

#guard raw (0 : Field) = 0
#guard raw (1 : Field) = 1
#guard toNat (ofNat Basic.fieldSize) = 0
#guard toNat (ofNat (Basic.fieldSize + 37)) = 37
#guard toNat ((ofNat (Basic.fieldSize - 1)) + (2 : Field)) = 1
#guard toNat ((ofNat (Basic.fieldSize - 1)) + (ofNat (Basic.fieldSize - 1))) =
  Basic.fieldSize - 2
#guard toNat ((9 : Field) - (5 : Field)) = 4
#guard toNat ((5 : Field) - (9 : Field)) = Basic.fieldSize - 4
#guard toNat (-(0 : Field)) = 0
#guard toNat (-(1 : Field)) = Basic.fieldSize - 1
#guard toNat ((ofNat (Basic.fieldSize - 1)) * (ofNat (Basic.fieldSize - 1))) = 1
#guard toNat (square (12345 : Field)) = 152399025
#guard toNat ((37 : Field) ^ 0) = 1
#guard toNat ((37 : Field) ^ 1) = 37
#guard toField ((123456789 : Field) ^ 17) = ((123456789 : Basic.Field) ^ 17)
#guard toField ((123456789 : Field) ^ 255) = ((123456789 : Basic.Field) ^ 255)
#guard toNat ((0 : Field)⁻¹) = 0
#guard toNat ((37 : Field)⁻¹ * (37 : Field)) = 1
#guard toNat ((37 : Field) / (37 : Field)) = 1
#guard toField ((37 : Field)⁻¹) = ((37 : Basic.Field)⁻¹)
#guard toField ((37 : Field) ^ (-3 : Int)) = ((37 : Basic.Field) ^ (-3 : Int))
#guard ringEquiv ((123 : Field) + 456) = ((123 : Basic.Field) + 456)
#guard ringEquiv ((123 : Field) * 456) = ((123 : Basic.Field) * 456)

end Mersenne31.Fast
