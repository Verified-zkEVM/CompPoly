/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Tower.Concrete.Arithmetic
public import CompPoly.Fields.Binary.Tower.Concrete.Arithmetic

/-!
# Standalone concrete tower arithmetic

The executable carrier and word operations remain available without finite-field certificates
or a constructed field dictionary. A negative import guard protects that dependency boundary;
word round trips, high/low coordinates and named arithmetic are exercised through this import.
-/

public meta section

namespace CompPolyTests.TowerArithmetic

open ConcreteBinaryTower

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if name.toString.startsWith "CompPoly.Fields.Binary.Tower.Support." ||
        name == `CompPoly.Fields.Binary.Tower.Concrete.Core ||
        name == `Mathlib.FieldTheory.Finite.GaloisField then
      throwError "Arithmetic imported field-construction support: {name}"
  for name in #[`ConcreteBinaryTower.toConcreteBTF0, `ConcreteBinaryTower.fromConcreteBTF0,
      `ConcreteBinaryTower.coeffsToBitVec, `ConcreteBinaryTower.ConcreteBTFAddCommGroupProps,
      `ConcreteBinaryTower.ConcreteBTFieldProps, `ConcreteBinaryTower.ConcreteBTFStepResult,
      `ConcreteBinaryTower.mkFieldInstance, `ConcreteBinaryTower.getBTFResult] do
    if env.contains name then
      throwError "Arithmetic exposed a Core declaration: {name}"

example (x : ConcreteBTField k) : ConcreteBTField.ofBitVec x.toBitVec = x :=
  ConcreteBTField.ofBitVec_toBitVec x
example (h : 0 < k) (x : ConcreteBTField k) :
    join h (split h x).1 (split h x).2 = x := by
  exact (join_of_split h x _ _ rfl).symm

example (_x : ConcreteBTField k) (_word : BitVec (2 ^ k)) : True := by
  fail_if_success
    let _raw : BitVec (2 ^ k) := _x
  fail_if_success
    let _field : ConcreteBTField k := _word
  trivial

#guard (concrete_mul (k := 1) (fromNat 2) (fromNat 2)).toNat == 3
#guard (concrete_inv (k := 1) (fromNat 2)).toNat == 3
#guard concrete_inv (k := 3) zero == zero
#guard concrete_pow_nat (k := 3) zero 0 == one
#guard (concrete_pow_nat (k := 1) (fromNat 2) (2 ^ 128)).toNat == 2
#guard (split (k := 7) (by decide) (fromNat (2 ^ 127 + 2 ^ 64 + 7))).1.toNat ==
  2 ^ 63 + 1
#guard (split (k := 7) (by decide) (fromNat (2 ^ 127 + 2 ^ 64 + 7))).2.toNat == 7

end CompPolyTests.TowerArithmetic
