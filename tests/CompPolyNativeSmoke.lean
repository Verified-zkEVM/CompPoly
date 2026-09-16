/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Ext3
public import CompPoly.Fields.Binary.Tower.Concrete.Field

/-!
# Native field startup and arithmetic checks

This executable checks canonical arithmetic in BF64, its cubic extension, and the binary tower.
The test guide documents resource limits for native initialization and execution.
Unlike compile-time guards, this target exercises the linked executable's module initializers.
The extension product uses the reference vector from the existing BF64 regression tests.
These checks provide implementation evidence; they are not kernel proofs or benchmarks.
-/

public section

namespace CompPolyTests.NativeSmoke

/-- Construct the three extension coefficients from polynomial-basis words in ascending order. -/
private def fromWords (c0 c1 c2 : BitVec 64) : BF64.Ext3 :=
  CompPoly.Extension.Ext.ofFn fun i =>
    BF64.ofBitVec (if i.val = 0 then c0 else if i.val = 1 then c1 else c2)

/-- Fail the native executable when an arithmetic result differs from its expected value. -/
private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"Native field check failed: `{label}`")

/-- Exercise multiplication and inversion through generic field data. -/
private def inverseProduct {F : Type*} [Field F] (x : F) : F := x * x⁻¹

/-- Check large signed powers through the field dictionary at a nonzero tower element. -/
@[noinline, nospecialize]
private def checkTowerPowers {F : Type*} [Field F] [BEq F] (x : F) : IO Unit := do
  check "tower natural power" (x ^ (2 ^ 128 : ℕ) == x)
  check "tower integer power" (x ^ (-((2 ^ 128 : ℕ) : ℤ)) == x⁻¹)
  check "tower zero natural exponent" ((0 : F) ^ (0 : ℕ) == 1)
  check "tower zero integer exponent" ((0 : F) ^ (0 : ℤ) == 1)
  check "tower positive power of zero" ((0 : F) ^ (2 ^ 128 : ℕ) == 0)
  check "tower negative power of zero" ((0 : F) ^ (-((2 ^ 128 : ℕ) : ℤ)) == 0)

/-- Check reduction, a reference product, total inversion, and large tower powers. -/
def run : IO Unit := do
  check "BF64 reduction"
    (((BF64.ofBitVec (0x8000000000000000#64)) * BF64.ofBitVec (2#64)).toBitVec == 0x1b#64)
  let x := BF64.ofBitVec (0x01090913877ed8ed#64)
  check "BF64 addition" ((x + 1).toBitVec == 0x01090913877ed8ec#64)
  check "BF64 inverse" (inverseProduct x == 1)
  check "BF64 zero inverse" ((0 : BF64)⁻¹ == 0)
  let a := fromWords 0x950e87d7f5606615 0x2c61275c9e6b6cf8 0x1f00bca0042db923
  let b := fromWords 0x6dbca290a9eab706 0x4c10a4fe30cffdda 0xf26fff4cc4fd394d
  let product := fromWords 0x888a0fc35abaf5f6 0x68a84cbc132b0649 0x9fdeaf613003cabe
  check "Ext3 reference product" (a * b == product)
  check "Ext3 addition"
    (a + 1 == fromWords 0x950e87d7f5606614 0x2c61275c9e6b6cf8 0x1f00bca0042db923)
  check "Ext3 inverse" (inverseProduct a == 1)
  check "Ext3 zero inverse" ((0 : BF64.Ext3)⁻¹ == 0)
  let towerGenerator := ConcreteBinaryTower.fromNat (k := 1) 2
  check "tower power encoding" ((towerGenerator ^ (2 : ℕ)).toNat == 3)
  checkTowerPowers towerGenerator
  checkTowerPowers (F := ConcreteBinaryTower.ConcreteBTField 3)
    (ConcreteBinaryTower.fromNat 0x80)
  checkTowerPowers (F := ConcreteBinaryTower.ConcreteBTField 7)
    (ConcreteBinaryTower.fromNat 0x80000000000000000000000000000000)
  IO.println "Native field startup and arithmetic checks passed."

end CompPolyTests.NativeSmoke

/-- Entry point for the bounded native smoke test. -/
def main : IO Unit := CompPolyTests.NativeSmoke.run
