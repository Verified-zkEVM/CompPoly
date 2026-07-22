/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Binary.Tower.Fast

/-!
# Fast Binary Tower Tests

Regression checks for the packed-word tower representation. The multiplication,
generator, squaring, and inversion constants are cross-validated against
`ConcreteBinaryTower.concrete_mul` / `concrete_inv` on full-width operands.
-/

namespace ConcreteBinaryTower.Fast

-- Additive structure
#guard ((ofNat 6 0xDEAD + ofNat 6 0xBEEF).val = (0xDEAD ^^^ 0xBEEF : UInt64))
#guard (ofNat 6 0xDEAD + ofNat 6 0xDEAD : BT64) = 0
#guard (0 + ofNat 5 0x12345678 : BT32) = ofNat 5 0x12345678

-- Multiplication, cross-checked against `concrete_mul`
#guard ((ofNat 3 0xAB * ofNat 3 0x3D : BT8)).val = 0xCF
#guard ((ofNat 4 0xABCD * ofNat 4 0x1234 : BT16)).val = 0xCF0C
#guard ((ofNat 5 0xDEADBEEF * ofNat 5 0x12345678 : BT32)).val = 0x94E989A6
#guard ((ofNat 6 0xDEADBEEFCAFEBABE * ofNat 6 0x123456789ABCDEF0 : BT64)).val
  = 0x4AE10FB8464BA9F5
#guard ((ofNat 6 0xDEADBEEFCAFEBABE * 1 : BT64)).val = 0xDEADBEEFCAFEBABE

-- Generator multiplication, cross-checked against `concrete_mul (Z k) ·`
#guard (ofNat 3 0xAB).mulByZ.val = 0xDA
#guard (ofNat 6 0xDEADBEEFCAFEBABE).mulByZ.val = 0x04CF6413DEADBEEF

-- Squaring and inversion at the word level, cross-checked against `concrete_inv`
#guard sq64 0xDEADBEEFCAFEBABE = 0x8459990BA3148442
#guard inv64 0xDEADBEEFCAFEBABE = 0x94D7EC832FAF447F
#guard mul64 0xDEADBEEFCAFEBABE (inv64 0xDEADBEEFCAFEBABE) = 1
#guard inv64 0 = 0
#guard inv64 1 = 1

-- Level 7, cross-checked against `concrete_mul` / `concrete_inv` at `k = 7`
private def a128 : FastBT128 := ⟨0xDEADBEEFCAFEBABE, 0x0123456789ABCDEF⟩
private def b128 : FastBT128 := ⟨0x123456789ABCDEF0, 0xFEDCBA9876543210⟩

#guard (a128 * b128) = ⟨0x29A88537675DA9F5, 0x899953DAF02F7327⟩
#guard a128.inv = ⟨0xDD97DC695DE13852, 0xAC3CB6A3957A8E7C⟩
#guard a128.square = ⟨0x06D8181BCEC18442, 0xA547828182818110⟩
#guard a128.mulByZ = ⟨0x0123456789ABCDEF, 0x21607223CBDDFFD9⟩
#guard (a128 * a128.inv) = 1
#guard (a128 + a128) = 0
#guard (a128 * b128) = (b128 * a128)

end ConcreteBinaryTower.Fast
