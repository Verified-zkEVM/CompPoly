/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

public meta import CompPoly.Fields.Mersenne31.Fast

/-!
# Fast Mersenne31 Field Tests

Regression checks for the executable native-word representation.
-/

public meta section

namespace Mersenne31.Fast

#guard (0 : Field).val = 0
#guard (1 : Field).val = 1
#guard toNat (ofUInt32 37) = 37
#guard toNat (Mersenne31.fieldSize : Field) = 0
#guard toNat (Mersenne31.fieldSize + 37 : Field) = 37
#guard toNat ((Mersenne31.fieldSize - 1 : Field) + 2) = 1
#guard toNat ((Mersenne31.fieldSize - 1 : Field) + (Mersenne31.fieldSize - 1 : Field)) =
  Mersenne31.fieldSize - 2
#guard toNat ((9 : Field) - 5) = 4
#guard toNat ((5 : Field) - 9) = Mersenne31.fieldSize - 4
#guard toNat (-(0 : Field)) = 0
#guard toNat (-(1 : Field)) = Mersenne31.fieldSize - 1
#guard toNat ((Mersenne31.fieldSize - 1 : Field) * (Mersenne31.fieldSize - 1 : Field)) = 1
#guard toNat ((12345 : Field) * 12345) = 152399025
#guard toNat ((37 : Field) ^ 0) = 1
#guard toNat ((37 : Field) ^ 1) = 37
#guard toField ((123456789 : Field) ^ 17) = ((123456789 : Mersenne31.Field) ^ 17)
#guard toField ((123456789 : Field) ^ 255) = ((123456789 : Mersenne31.Field) ^ 255)
#guard toNat ((0 : Field)⁻¹) = 0
#guard toNat ((37 : Field)⁻¹ * 37) = 1
#guard toNat ((37 : Field) / 37) = 1
#guard toField ((37 : Field)⁻¹) = ((37 : Mersenne31.Field)⁻¹)
#guard toField ((37 : Field) ^ (-3 : Int)) = ((37 : Mersenne31.Field) ^ (-3 : Int))
#guard ringEquiv ((123 : Field) + 456) = ((123 : Mersenne31.Field) + 456)
#guard ringEquiv ((123 : Field) * 456) = ((123 : Mersenne31.Field) * 456)

end Mersenne31.Fast
