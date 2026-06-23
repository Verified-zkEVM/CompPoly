/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast

/-!
# Fast BabyBear Field Tests

Regression checks for the executable Montgomery representation.
-/

namespace BabyBear.Fast

#guard raw (0 : Field) = 0
#guard raw (1 : Field) = rModModulus
#guard toCanonicalUInt32 (ofNat 37) = (37 : UInt32)
#guard toNat (ofNat BabyBear.fieldSize) = 0
#guard toNat (ofNat (BabyBear.fieldSize + 37)) = 37
#guard toNat ((ofNat (BabyBear.fieldSize - 1)) + (2 : Field)) = 1
#guard toNat ((ofNat (BabyBear.fieldSize - 1)) + (ofNat (BabyBear.fieldSize - 1))) =
  BabyBear.fieldSize - 2
#guard toNat ((9 : Field) - (5 : Field)) = 4
#guard toNat ((5 : Field) - (9 : Field)) = BabyBear.fieldSize - 4
#guard toNat (-(0 : Field)) = 0
#guard toNat (-(1 : Field)) = BabyBear.fieldSize - 1
#guard toNat ((ofNat (BabyBear.fieldSize - 1)) * (ofNat (BabyBear.fieldSize - 1))) = 1
#guard toNat (square (12345 : Field)) = 152399025
#guard toNat ((37 : Field) ^ 0) = 1
#guard toNat ((37 : Field) ^ 1) = 37
#guard toField ((123456789 : Field) ^ 17) = ((123456789 : BabyBear.Field) ^ 17)
#guard toField ((123456789 : Field) ^ 255) = ((123456789 : BabyBear.Field) ^ 255)
#guard toNat ((0 : Field)⁻¹) = 0
#guard toNat ((37 : Field)⁻¹ * (37 : Field)) = 1
#guard toNat ((37 : Field) / (37 : Field)) = 1
#guard toField ((37 : Field)⁻¹) = ((37 : BabyBear.Field)⁻¹)
#guard toField ((37 : Field) ^ (-3 : Int)) = ((37 : BabyBear.Field) ^ (-3 : Int))

end BabyBear.Fast
