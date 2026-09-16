/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Aes.Ghash
public import CompPoly.Fields.Binary.Aes.Ghash

/-!
# AES to GHASH embedding regressions

The public homomorphism executes its coefficient evaluation and preserves field operations.
The coordinate vectors distinguish the selected embedding from raw byte zero-extension.
The pinned source references for the selected root and table are in the production module.
-/

public meta section

namespace CompPolyTests.AesGhash

open AesField BF128Ghash CompPoly.Extension

example : CharP ConcreteBF128Ghash 2 := inferInstance

example (a : AesField) :
    toGhash a = ∑ i : Fin params.d,
      ZMod.castHom (dvd_refl 2) ConcreteBF128Ghash (Ext.coeff a i) * ghashRoot ^ (i : ℕ) := rfl

example (a b : AesField) : toGhash (a + b) = toGhash a + toGhash b := map_add toGhash a b
example (a b : AesField) : toGhash (a * b) = toGhash a * toGhash b := map_mul toGhash a b
example (a : AesField) : toGhash a⁻¹ = (toGhash a)⁻¹ := map_inv₀ toGhash a
example (a : AesField) (n : ℕ) : toGhash (a ^ n) = toGhash a ^ n := map_pow toGhash a n
example (a b : AesField) : toGhash a = toGhash b ↔ a = b := toGhash_injective.eq_iff
example : toGhash gen = ghashRoot := toGhash_gen

example (_a : AesField) (_b : ConcreteBF128Ghash) : True := by
  fail_if_success
    let _x : ConcreteBF128Ghash := _a
  fail_if_success
    let _x : AesField := _b
  fail_if_success
    let _x := @Mul.mul AesField inferInstance _a _b
  trivial

#guard toGhash 0 == 0
#guard toGhash 1 == 1
#guard (toGhash (AesField.ofBitVec (2#8))).toBitVec ==
  0x0dcb364640a222fe6b8330483c2e9849#128
#guard (toGhash (AesField.ofBitVec (4#8))).toBitVec ==
  0x3d5bd35c94646a247573da4a5f7710ed#128
#guard (toGhash (AesField.ofBitVec (0x80#8))).toBitVec ==
  0x93252331bf042b11512625b1f09fa87e#128
#guard toGhash ((AesField.ofBitVec (0x53#8))⁻¹) ==
  (toGhash (AesField.ofBitVec (0x53#8)))⁻¹
#guard toGhash ((0 : AesField)⁻¹) == (0 : ConcreteBF128Ghash)

-- Raw word 2 is not a root of the AES modulus in GHASH.
private def wrongRoot : ConcreteBF128Ghash := BF128Ghash.ofBitVec (2#128)
#guard wrongRoot ^ 8 + wrongRoot ^ 4 + wrongRoot ^ 3 + wrongRoot + 1 != 0

-- Zero-extension sends the AES product to 0x1b, but multiplies the raw images to 0x100.
private def zeroExtend (a : AesField) : ConcreteBF128Ghash :=
  BF128Ghash.ofBitVec (a.toBitVec.zeroExtend 128)
#guard zeroExtend (AesField.ofBitVec (0x80#8) * AesField.ofBitVec (2#8)) !=
  zeroExtend (AesField.ofBitVec (0x80#8)) * zeroExtend (AesField.ofBitVec (2#8))
#guard toGhash (AesField.ofBitVec (0x80#8) * AesField.ofBitVec (2#8)) ==
  toGhash (AesField.ofBitVec (0x80#8)) * toGhash (AesField.ofBitVec (2#8))

end CompPolyTests.AesGhash
