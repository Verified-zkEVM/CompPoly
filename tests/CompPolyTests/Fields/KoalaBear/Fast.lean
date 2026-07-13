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

#guard (0 : Field).val = 0
#guard (1 : Field).val =
  Montgomery.Native32.Mont32Field.rModModulus (modulus := KoalaBear.fieldSize)
#guard (37 : Field).toUInt32 = (37 : UInt32)
#guard (KoalaBear.fieldSize : Field).toNat = 0
#guard (KoalaBear.fieldSize + 37 : Field).toNat = 37
#guard ((KoalaBear.fieldSize - 1 : Field) + 2).toNat = 1
#guard ((KoalaBear.fieldSize - 1 : Field) + (KoalaBear.fieldSize - 1 : Field)).toNat =
  KoalaBear.fieldSize - 2
#guard ((9 : Field) - 5).toNat = 4
#guard ((5 : Field) - 9).toNat = KoalaBear.fieldSize - 4
#guard (-(0 : Field)).toNat = 0
#guard (-(1 : Field)).toNat = KoalaBear.fieldSize - 1
#guard ((KoalaBear.fieldSize - 1 : Field) * (KoalaBear.fieldSize - 1 : Field)).toNat = 1
#guard (square (12345 : Field)).toNat = 152399025
#guard ((37 : Field) ^ 0).toNat = 1
#guard ((37 : Field) ^ 1).toNat = 37
#guard ((123456789 : Field) ^ 17).toField = ((123456789 : KoalaBear.Field) ^ 17)
#guard ((123456789 : Field) ^ 255).toField = ((123456789 : KoalaBear.Field) ^ 255)
#guard ((0 : Field)⁻¹).toNat = 0
#guard ((37 : Field)⁻¹ * 37).toNat = 1
#guard ((37 : Field) / 37).toNat = 1
#guard ((37 : Field)⁻¹).toField = ((37 : KoalaBear.Field)⁻¹)
#guard ((37 : Field) ^ (-3 : Int)).toField = ((37 : KoalaBear.Field) ^ (-3 : Int))

end KoalaBear.Fast
