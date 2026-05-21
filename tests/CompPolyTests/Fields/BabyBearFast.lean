/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.BabyBear.Fast

/-!
# Fast BabyBear Field Tests

Regression checks for the executable Montgomery representation.
-/

namespace BabyBear.Fast

#guard raw (0 : Element) = 0
#guard raw (1 : Element) = rModModulus
#guard toCanonicalUInt32 (ofNat 37) = (37 : UInt32)
#guard toNat (ofNat BabyBear.fieldSize) = 0
#guard toNat (ofNat (BabyBear.fieldSize + 37)) = 37
#guard toNat ((ofNat (BabyBear.fieldSize - 1)) + (2 : Element)) = 1
#guard toNat ((ofNat (BabyBear.fieldSize - 1)) + (ofNat (BabyBear.fieldSize - 1))) =
  BabyBear.fieldSize - 2
#guard toNat ((9 : Element) - (5 : Element)) = 4
#guard toNat ((5 : Element) - (9 : Element)) = BabyBear.fieldSize - 4
#guard toNat (-(0 : Element)) = 0
#guard toNat (-(1 : Element)) = BabyBear.fieldSize - 1
#guard toNat ((ofNat (BabyBear.fieldSize - 1)) * (ofNat (BabyBear.fieldSize - 1))) = 1
#guard toNat (square (12345 : Element)) = 152399025
#guard toNat ((37 : Element) ^ 0) = 1
#guard toNat ((37 : Element) ^ 1) = 37
#guard toField ((123456789 : Element) ^ 17) = ((123456789 : BabyBear.Field) ^ 17)
#guard toField ((123456789 : Element) ^ 255) = ((123456789 : BabyBear.Field) ^ 255)
#guard toNat ((0 : Element)⁻¹) = 0
#guard toNat ((37 : Element)⁻¹ * (37 : Element)) = 1
#guard toNat ((37 : Element) / (37 : Element)) = 1
#guard toField ((37 : Element)⁻¹) = ((37 : BabyBear.Field)⁻¹)
#guard toField ((37 : Element) ^ (-3 : Int)) = ((37 : BabyBear.Field) ^ (-3 : Int))

end BabyBear.Fast
