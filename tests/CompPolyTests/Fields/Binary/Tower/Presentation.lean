/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly
public import CompPoly

/-!
# Concrete tower presentation regressions

The aggregate import preserves the nominal boundary between tower elements, raw words, and
polynomial-basis field elements. Canonical field dictionaries retain the executable operations,
characteristic-two casts and scalar actions, including the concrete additive NTT alias.
-/

public meta section

namespace CompPolyTests.TowerPresentation

open ConcreteBinaryTower

example (_x : ConcreteBTField 6) (_word : BitVec 64) (_y : _root_.BF64) : True := by
  fail_if_success
    let _raw : BitVec 64 := _x
  fail_if_success
    let _field : ConcreteBTField 6 := _word
  fail_if_success
    let _field : ConcreteBTField 6 := _y
  fail_if_success
    let _field : _root_.BF64 := _x
  fail_if_success
    let _mixed := _x * _word
  fail_if_success
    let _mixed := _word * _x
  fail_if_success
    let _mixed := _x * _y
  fail_if_success
    let _literal := ((2#2 : ConcreteBTField 1) ^ (2 : ℕ)).toNat
  trivial

example (p : ConcreteBTFieldProps k) (x y : ConcreteBTField k) :
    (mkFieldInstance p).add x y = add x y := rfl
example (p : ConcreteBTFieldProps k) (x : ConcreteBTField k) :
    (mkFieldInstance p).neg x = x := rfl
example (p : ConcreteBTFieldProps k) (x y : ConcreteBTField k) :
    (mkFieldInstance p).sub x y = add x y := rfl
example (p : ConcreteBTFieldProps k) (x y : ConcreteBTField k) :
    (mkFieldInstance p).mul x y = concrete_mul x y := rfl
example (p : ConcreteBTFieldProps k) (x : ConcreteBTField k) :
    (mkFieldInstance p).inv x = concrete_inv x := rfl
example (p : ConcreteBTFieldProps k) (x y : ConcreteBTField k) :
    (mkFieldInstance p).div x y = concrete_mul x (concrete_inv y) := rfl
example (p : ConcreteBTFieldProps k) (n : ℕ) :
    (mkFieldInstance p).natCast n = (if n % 2 = 0 then zero else one) := rfl
example (p : ConcreteBTFieldProps k) (n : ℤ) :
    (mkFieldInstance p).intCast n = (if n % 2 = 0 then zero else one) := rfl
example (p : ConcreteBTFieldProps k) (n : ℕ) (x : ConcreteBTField k) :
    (mkFieldInstance p).nsmul n x = (if n % 2 = 0 then zero else x) := rfl
example (p : ConcreteBTFieldProps k) (n : ℤ) (x : ConcreteBTField k) :
    (mkFieldInstance p).zsmul n x = (if n % 2 = 0 then zero else x) := rfl

example (x y : ConcreteBTField k) :
    (inferInstance : Field (ConcreteBTField k)).mul x y = concrete_mul x y := rfl
example (x : ConcreteBTField k) :
    (inferInstance : Field (ConcreteBTField k)).inv x = concrete_inv x := rfl
example (x : ConcreteBTField k) (n : ℕ) :
    (inferInstance : Field (ConcreteBTField k)).npow n x = x ^ n := rfl
example (x : ConcreteBTField k) (n : ℤ) :
    (inferInstance : Field (ConcreteBTField k)).zpow n x = x ^ n := rfl
example (x y : ConcreteBTField k) : x + y = add x y := rfl
example (x y : ConcreteBTField k) : x * y = concrete_mul x y := rfl
example (x y : ConcreteBTField k) : x / y = concrete_mul x (concrete_inv y) := rfl
example (x y : ConcreteBTField k) : (x < y) = (x.toNat < y.toNat) := rfl
example (x y : ConcreteBTField k) : (x ≤ y) = (x.toNat ≤ y.toNat) := rfl

example : (inferInstance : Field AdditiveNTT.BTF₃) =
    (instFieldConcrete : Field (ConcreteBTField 3)) := rfl
example : (inferInstance : DecidableEq AdditiveNTT.BTF₃) =
    instDecidableEqConcreteBTField 3 := rfl
example : (inferInstance : Fintype AdditiveNTT.BTF₃) =
    Fintype.ofEquiv (Fin (2 ^ (2 ^ 3)))
      ((ConcreteBTField.equivBitVec 3).trans (BitVec.equivFin (m := 2 ^ 3))).symm := rfl
example (x y : AdditiveNTT.BTF₃) : x * y = concrete_mul x y := rfl
example (x : AdditiveNTT.BTF₃) : x⁻¹ = concrete_inv x := rfl
example : Fintype.card AdditiveNTT.BTF₃ = 256 :=
  (Fintype.card_congr
    ((ConcreteBTField.equivBitVec 3).trans (BitVec.equivFin (m := 2 ^ 3)))).trans
      (Fintype.card_fin _)

#guard (2 : ConcreteBTField 6) == 0
#guard (3 : ConcreteBTField 6) == 1
#guard ((-2 : ℤ) : ConcreteBTField 6) == 0
#guard (2 : ℕ) • fromNat (k := 3) 0x80 == 0
#guard (-3 : ℤ) • fromNat (k := 3) 0x80 == fromNat (k := 3) 0x80
#guard (fromNat (k := 1) 2 ^ (2 : ℕ)).toNat == 3
#guard (fromNat (k := 2) 2 ^ (2 : ℕ)).toNat == 3
#guard (2#2) ^ (2 : ℕ) == 0#2
#guard (2#4) ^ (2 : ℕ) == 4#4
#guard (1#4) + (1#4) == 2#4

end CompPolyTests.TowerPresentation
