/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF128Ghash.Impl
public meta import CompPoly.Fields.Binary.Tower.Concrete.Core
public import CompPoly.Fields.Binary.BF128Ghash.Impl
public import CompPoly.Fields.Binary.Tower.Concrete.Core

/-!
# GHASH presentation regressions

The polynomial-basis carrier requires explicit conversion to raw words and remains distinct
from the 128-bit binary tower. Modulus-crossing vectors check multiplication and the typed
inversion chain. Inverse reference values use polynomial extended Euclidean division over
`GF(2)`, independently of the Itoh-Tsujii chain. These checks exercise the named executable
algorithm; they do not assert computability of the generic field dictionary.
-/

public meta section

namespace CompPolyTests.GhashPresentation

open BF128Ghash ConcreteBinaryTower

example (_x : ConcreteBF128Ghash) : True := by
  fail_if_success
    let _word : BitVec 128 := _x
  fail_if_success
    let _tower : ConcreteBTField 7 := _x
  trivial

example (_word : BitVec 128) (_tower : ConcreteBTField 7) : True := by
  fail_if_success
    let _x : ConcreteBF128Ghash := _word
  fail_if_success
    let _x : ConcreteBF128Ghash := _tower
  trivial

example (_x : ConcreteBF128Ghash) (_y : ConcreteBTField 7) : True := by
  fail_if_success
    let _z := @Mul.mul ConcreteBF128Ghash inferInstance _x _y
  fail_if_success
    let _z := @Mul.mul (ConcreteBTField 7) inferInstance _y _x
  trivial

example (b : BitVec 128) : (ofBitVec b).toBitVec = b := rfl
example (a : ConcreteBF128Ghash) : ofBitVec a.toBitVec = a := rfl
example : LawfulBEq ConcreteBF128Ghash := inferInstance
example : Finite ConcreteBF128Ghash := inferInstance

-- The imported field must not replace the ordinary raw-word operations or numerals.
example : (inferInstance : Mul (BitVec 128)) = BitVec.instMul := rfl
example : (2 : BitVec 128) = 2#128 := rfl
#guard (3#128) + (3#128) == 6#128
#guard (3#128) * (3#128) == 9#128
#guard ((0x80000000000000000000000000000000#128) * (2#128)) == 0#128

-- A field numeral is a sum of ones; a raw coordinate word can instead denote X.
#guard (2 : ConcreteBF128Ghash) == 0
#guard ofBitVec (2#128) != 0

example (a b : ConcreteBF128Ghash) :
    (a * b).toBitVec = reduce_clMul (clMul a.toBitVec b.toBitVec) := toBitVec_mul a b
example (a b : ConcreteBF128Ghash) : toQuot (a * b) = toQuot a * toQuot b := toQuot_mul a b

-- The final field dictionary retains these operations and characteristic-two casts.
example (a b : ConcreteBF128Ghash) :
    (inferInstance : Field ConcreteBF128Ghash).mul a b = BF128Ghash.mul a b := rfl
example (a b : ConcreteBF128Ghash) :
    (inferInstance : Field ConcreteBF128Ghash).add a b = ofBitVec (a.toBitVec ^^^ b.toBitVec) := rfl
example (n : ℕ) :
    (inferInstance : Field ConcreteBF128Ghash).natCast n = BF128Ghash.natCast n := rfl
example (n : ℤ) :
    (inferInstance : Field ConcreteBF128Ghash).intCast n = BF128Ghash.intCast n := rfl

-- X^128 reduces to X^7 + X^2 + X + 1, whereas raw-word multiplication overflows.
#guard ((ofBitVec (0x80000000000000000000000000000000#128)) * ofBitVec (2#128)).toBitVec ==
  0x87#128
#guard ((ofBitVec (2#128)) * ofBitVec (2#128)).toBitVec == 4#128
#guard (concrete_mul (k := 7) (2#128) (2#128)).toNat == 3

-- Squaring and inversion must retain reduced polynomial multiplication inside the chain.
#guard (invItohTsujii (ofBitVec (2#128))).toBitVec ==
  0x80000000000000000000000000000043#128
#guard (square (ofBitVec (0x80000000000000000000000000000000#128))).toBitVec ==
  0xc0000000000000000000000000001067#128
#guard (invItohTsujii (ofBitVec (0x80000000000000000000000000000000#128))).toBitVec ==
  0x0b604395d27ef1a8b604395d27ef1a8ee#128
#guard (invItohTsujii (ofBitVec (0x0123456789abcdeffedcba9876543210#128))).toBitVec ==
  0xac20a8a9f088c918e7a4a93e6b40984a#128
#guard (invItohTsujii 0).toBitVec == 0#128

end CompPolyTests.GhashPresentation
