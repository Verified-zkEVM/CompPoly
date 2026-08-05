/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public meta import CompPoly.Fields.Binary.Tower.Fast

/-!
# Fast Binary Tower Tests

Regression checks for the packed-word tower. Word-level constants are cross-validated
against `ConcreteBinaryTower.concrete_mul` / `concrete_inv` on full-width operands;
carrier guards exercise the `Field` instances.
-/

public meta section

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

-- Field structure on the carrier: inversion, division, powers, squaring
#guard ((ofNat 6 0xDEADBEEFCAFEBABE : BT64)⁻¹).val = 0x94D7EC832FAF447F
#guard (ofNat 6 0xDEADBEEFCAFEBABE * (ofNat 6 0xDEADBEEFCAFEBABE : BT64)⁻¹) = 1
#guard ((0 : BT64)⁻¹) = 0
#guard ((1 : BT32)⁻¹) = 1
#guard (ofNat 5 0xDEADBEEF / ofNat 5 0xDEADBEEF : BT32) = 1
#guard ((ofNat 3 0xAB : BT8) ^ 3) = ofNat 3 0xAB * ofNat 3 0xAB * ofNat 3 0xAB
#guard (ofNat 6 0xDEADBEEFCAFEBABE).square.val = 0x8459990BA3148442
#guard (ofNat 3 0xAB).square = ofNat 3 0xAB * ofNat 3 0xAB

-- Numerals reduce mod the characteristic; raw packed values go through `ofNat`
#guard (5 : BT16) = 1
#guard (2 : BT64) = 0
#guard (-3 : BT8) = 1

-- Table rungs agree with the ladder on full-width words
#guard mul64T 0xDEADBEEFCAFEBABE 0x123456789ABCDEF0
  = mul64 0xDEADBEEFCAFEBABE 0x123456789ABCDEF0
#guard inv64T 0xDEADBEEFCAFEBABE = inv64 0xDEADBEEFCAFEBABE
#guard sq64T 0xDEADBEEFCAFEBABE = sq64 0xDEADBEEFCAFEBABE
#guard mulByZ6T 0xDEADBEEFCAFEBABE = mulByZ6 0xDEADBEEFCAFEBABE

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

-- Field structure at level 7
#guard (a128 * a128⁻¹) = 1
#guard (a128 / b128) * b128 = a128
#guard (a128 ^ 2) = a128 * a128
#guard (5 : FastBT128) = 1
#guard (2 : FastBT128) = 0

-- Ring equivalence round trips
#guard ringEquivBT8.symm (ringEquivBT8 (ofNat 3 0xAB)) = ofNat 3 0xAB
#guard ringEquivBT64.symm (ringEquivBT64 (ofNat 6 0xDEADBEEF)) = ofNat 6 0xDEADBEEF
#guard FastBT128.ringEquiv.symm (FastBT128.ringEquiv a128) = a128

end ConcreteBinaryTower.Fast
