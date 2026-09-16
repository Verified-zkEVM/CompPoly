/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Aes.Basic
public meta import CompPoly.Fields.Binary.Tower.Concrete.Core
public import CompPoly.Fields.Binary.Aes.Basic
public import CompPoly.Fields.Binary.Tower.Concrete.Core

/-!
# AES certified presentation regressions

These checks distinguish byte coordinates, the level-three binary tower, and characteristic-two
numerals. Generic field callers exercise the certified canonical operations. Corrupting the
modulus or a Frobenius remainder must invalidate the irreducibility certificate.
-/

public meta section

namespace CompPolyTests.Aes

open AesField CompPoly.Extension CompPoly.RabinCert

example (_a : AesField) : True := by
  fail_if_success
    let _x : BitVec 8 := _a
  fail_if_success
    let _x : ConcreteBinaryTower.ConcreteBTField 3 := _a
  trivial

example (_a : BitVec 8) (_b : ConcreteBinaryTower.ConcreteBTField 3) : True := by
  fail_if_success
    let _x : AesField := _a
  fail_if_success
    let _x : AesField := _b
  trivial

example (_a : AesField) (_b : ConcreteBinaryTower.ConcreteBTField 3) : True := by
  fail_if_success
    let _x := @Mul.mul AesField inferInstance _a _b
  fail_if_success
    let _x := @Mul.mul (ConcreteBinaryTower.ConcreteBTField 3) inferInstance _b _a
  trivial

private def inverse {F : Type*} [Field F] (a : F) : F := a⁻¹
private def divide {F : Type*} [Field F] (a b : F) : F := a / b

example (a : AesField) : inverse a = a ^ (254 : ℕ) := rfl
example (a b : AesField) : divide a b = a * b ^ (254 : ℕ) := rfl
example (a b : AesField) :
    (inferInstance : Field AesField).mul a b = Ext.mul a b := rfl
example (n : ℕ) (a : AesField) :
    (inferInstance : Field AesField).npow n a = npowBinRec n a := rfl
example : CharP AesField 2 := inferInstance
example : Nat.card AesField = 256 := AesField.nat_card

#guard (2 : AesField) == 0
#guard ofBitVec (2#8) != 0
#guard gen == ofBitVec (2#8)
#guard ((ofBitVec (2#8)) * ofBitVec (2#8)).toBitVec == 4#8
#guard (ConcreteBinaryTower.concrete_mul (k := 3)
  (ConcreteBinaryTower.fromNat 2) (ConcreteBinaryTower.fromNat 2)).toNat == 3
#guard (inverse (ofBitVec (0x53#8))).toBitVec == 0xca#8
#guard inverse (0 : AesField) == 0
#guard divide (ofBitVec (0x80#8)) 0 == 0
#guard divide (ofBitVec (0x80#8)) (ofBitVec (0x80#8)) == 1

-- A changed constant coefficient cannot reuse the certificate for the AES modulus.
#guard runChain 2 [0, 1, 0, 1, 1, 0, 0, 0, 1] [0, 1] Certificate.traceSteps == none
-- Nor can a corrupted final Frobenius remainder pass the same modulus checker.
#guard runChain 2 [1, 1, 0, 1, 1, 0, 0, 0, 1] [0, 1]
  (Certificate.traceSteps.set 7 ⟨false, [0, 1, 0, 0, 1, 0, 1], [0]⟩) == none

end CompPolyTests.Aes
