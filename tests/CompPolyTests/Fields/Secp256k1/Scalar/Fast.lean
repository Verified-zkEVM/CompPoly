/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Secp256k1.Scalar.Fast

/-!
# Fast secp256k1 Scalar Tests

Regression checks for the pure-Lean 4x64 scalar implementation.
-/

namespace Secp256k1.Scalar.Fast

private def n : Nat := Secp256k1.Scalar.Basic.CARD

#synth CommRing Field
#synth _root_.Field Field
#synth NonBinaryField Field

#guard mul64Hi 0xffffffffffffffff 0xffffffffffffffff = 0xfffffffffffffffe
#guard mul64Hi 0x123456789abcdef0 0xfedcba9876543210 = 0x121fa00ad77d7422

#guard toNat (0 : Field) = 0
#guard toNat (1 : Field) = 1
#guard toNat (ofNat n) = 0
#guard toNat (ofNat (n + 17)) = 17
#guard toNat (ofNat (n - 1) + 1) = 0
#guard toNat (ofNat (n - 1) + ofNat (n - 1)) = n - 2
#guard toNat ((17 : Field) - (6 : Field)) = 11
#guard toNat ((6 : Field) - (17 : Field)) = n - 11
#guard toNat (-(0 : Field)) = 0
#guard toNat (-(1 : Field)) = n - 1
#guard toNat (ofNat (n - 1) * ofNat (n - 1)) = 1
#guard toField ((0x123456789abcdef : Field) * (0xfedcba987654321 : Field)) =
  (0x123456789abcdef : Secp256k1.Scalar.Basic.Field) *
    (0xfedcba987654321 : Secp256k1.Scalar.Basic.Field)
#guard toField (square (0xdeadbeef01234567 : Field)) =
  (0xdeadbeef01234567 : Secp256k1.Scalar.Basic.Field) ^ 2
#guard toNat ((73 : Field) ^ 0) = 1
#guard toNat ((73 : Field) ^ 1) = 73
#guard toField ((987654321 : Field) ^ 19) =
  (987654321 : Secp256k1.Scalar.Basic.Field) ^ 19
#guard toNat ((0 : Field)⁻¹) = 0
#guard toNat ((1 : Field)⁻¹) = 1
#guard toNat (invFermat 73 * 73) = 1
#guard toNat ((73 : Field) * (73 : Field)⁻¹) = 1
#guard toNat ((ofNat (n - 1))⁻¹) = n - 1
#guard toNat ((987654321 : Field) * (987654321 : Field)⁻¹) = 1
#guard toField ((73 : Field) / (19 : Field)) =
  (73 : Secp256k1.Scalar.Basic.Field) / (19 : Secp256k1.Scalar.Basic.Field)

end Secp256k1.Scalar.Fast
