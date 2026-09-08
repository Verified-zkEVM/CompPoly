/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF64.Impl
public meta import CompPoly.Fields.Binary.Tower.Fast
public import CompPoly.Fields.Binary.BF64.Impl
public import CompPoly.Fields.Binary.Tower.Fast

/-!
# Polynomial-basis field presentation regressions

BF64 elements require explicit conversion to raw words and cannot be reinterpreted as
binary-tower elements. The same raw word has different multiplication in the two fields;
field numerals and raw polynomial-basis coordinates remain distinct.
-/

public meta section

namespace CompPolyTests.BF64Presentation

open BF64 ConcreteBinaryTower

example (_x : BF64) : True := by
  fail_if_success
    let _word : BitVec 64 := _x
  fail_if_success
    let _tower : ConcreteBTField 6 := _x
  trivial

example (_word : BitVec 64) (_tower : ConcreteBTField 6) : True := by
  fail_if_success
    let _x : BF64 := _word
  fail_if_success
    let _x : BF64 := _tower
  trivial

example (_x : BF64) (_y : ConcreteBTField 6) : True := by
  fail_if_success
    let _z := @Mul.mul BF64 inferInstance _x _y
  fail_if_success
    let _z := @Mul.mul (ConcreteBTField 6) inferInstance _y _x
  trivial

example (b : BitVec 64) : (ofBitVec b).toBitVec = b := rfl
example (x : BF64) : ofBitVec x.toBitVec = x := rfl
example : LawfulBEq BF64 := inferInstance

-- Importing the field leaves raw-word arithmetic at its ordinary modular operations.
example : (inferInstance : Mul (BitVec 64)) = BitVec.instMul := rfl
#guard ((0x8000000000000000#64) * (2#64)).toNat == 0

-- A field numeral denotes repeated addition of one, not a polynomial-basis word.
#guard (2 : BF64) == 0
#guard (0xffffffffffffffff : BF64) == 1
#guard (0xfffffffffffffffe : BF64) == 0
#guard ofBitVec (2#64) != 0

-- The same coordinates do not identify the two multiplication laws.
#guard ((ofBitVec (2#64)) * ofBitVec (2#64)).toBitVec == 4#64
#guard (concrete_mul (k := 6) (2#64) (2#64)).toNat == 3

-- Generic field code retains the canonical executable operations and casts.
example (x y : BF64) : (inferInstance : Field BF64).mul x y = BF64.mul x y := rfl
example (x : BF64) : (inferInstance : Field BF64).inv x = invItohTsujii x := rfl
example (x y : BF64) : (inferInstance : Field BF64).div x y = x * invItohTsujii y := rfl
example (x : BF64) (n : ℕ) :
    (inferInstance : Field BF64).npow n x = npowBinRec n x := rfl
example (n : ℕ) : (inferInstance : Field BF64).natCast n = (n : BF64) := rfl
example (n : ℤ) : (inferInstance : Field BF64).intCast n = (n : BF64) := rfl

end CompPolyTests.BF64Presentation
