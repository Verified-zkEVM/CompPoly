/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast

/-!
# Fast Goldilocks Field Tests

Regression checks for the verified `UInt64` fast representation.

Run this file with:
`lake build CompPolyTests.Fields.Goldilocks.Fast`
-/

namespace Goldilocks.Fast

private def p : Nat := Goldilocks.Basic.fieldSize

#guard raw (0 : Field) = 0
#guard raw (1 : Field) = 1
#guard toNat (ofNat 73) = 73
#guard toNat (ofNat p) = 0
#guard toNat (ofNat (p + 73)) = 73
#guard toNat (ofUInt64 (UInt64.ofNat (UInt64.size - 1))) = 4294967294
#guard toNat ((ofNat (p - 1)) + (4 : Field)) = 3
#guard toNat ((ofNat (p - 1)) + (ofNat (p - 1))) = p - 2
#guard toNat ((17 : Field) - (6 : Field)) = 11
#guard toNat ((6 : Field) - (17 : Field)) = p - 11
#guard toNat (-(0 : Field)) = 0
#guard toNat (-(1 : Field)) = p - 1
#guard toNat ((ofNat (p - 1)) * (ofNat (p - 1))) = 1
#guard toField (square (54321 : Field)) = ((54321 : Goldilocks.Basic.Field) ^ 2)
#guard toNat ((73 : Field) ^ 0) = 1
#guard toNat ((73 : Field) ^ 1) = 73
#guard toField ((987654321 : Field) ^ 19) = ((987654321 : Goldilocks.Basic.Field) ^ 19)
#guard toField ((987654321 : Field) ^ 511) = ((987654321 : Goldilocks.Basic.Field) ^ 511)
#guard toNat ((0 : Field)⁻¹) = 0
#guard toNat ((73 : Field)⁻¹ * (73 : Field)) = 1
#guard toNat ((73 : Field) / (73 : Field)) = 1
#guard toField ((73 : Field)⁻¹) = ((73 : Goldilocks.Basic.Field)⁻¹)
#guard toField ((73 : Field) ^ (-5 : Int)) = ((73 : Goldilocks.Basic.Field) ^ (-5 : Int))

end Goldilocks.Fast
