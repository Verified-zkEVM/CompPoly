/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.KoalaBear.Fast

/-!
# Fast KoalaBear Field Tests

Regression checks for the executable Montgomery representation.
-/

namespace KoalaBear.Fast

#guard raw (0 : Element) = 0
#guard raw (1 : Element) = rModModulus
#guard toCanonicalUInt32 (ofNat 37) = (37 : UInt32)
#guard toNat (ofNat KoalaBear.fieldSize) = 0
#guard toNat (ofNat (KoalaBear.fieldSize + 37)) = 37
#guard toNat ((ofNat (KoalaBear.fieldSize - 1)) + (2 : Element)) = 1
#guard toNat ((5 : Element) - (9 : Element)) = KoalaBear.fieldSize - 4
#guard toNat (-(1 : Element)) = KoalaBear.fieldSize - 1
#guard toNat ((ofNat (KoalaBear.fieldSize - 1)) * (ofNat (KoalaBear.fieldSize - 1))) = 1
#guard toNat (square (12345 : Element)) = 152399025
#guard toField ((123456789 : Element) ^ 17) = ((123456789 : KoalaBear.Field) ^ 17)
#guard toNat ((0 : Element)⁻¹) = 0
#guard toNat ((37 : Element)⁻¹ * (37 : Element)) = 1
#guard toNat ((37 : Element) / (37 : Element)) = 1
#guard toField ((37 : Element)⁻¹) = ((37 : KoalaBear.Field)⁻¹)
#guard toField ((37 : Element) ^ (-3 : Int)) = ((37 : KoalaBear.Field) ^ (-3 : Int))

end KoalaBear.Fast
