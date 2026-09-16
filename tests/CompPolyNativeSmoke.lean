/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.Aes.Basic
public import CompPoly.Fields.Binary.BF128Ghash.Impl
public import CompPoly.Fields.Binary.BF64.Ext3

/-!
# Native field startup and arithmetic checks

This executable imports AES, BF64, its cubic extension, and GHASH to check canonical arithmetic.
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

/-- Exercise the actual generic field dictionary without inlining or specialization. -/
@[noinline, nospecialize]
private def checkGhashOperations {F : Type*} [Field F] [BEq F]
    (x expectedInverse : F) : IO Unit := do
  check "GHASH generic inverse" (x⁻¹ == expectedInverse)
  check "GHASH generic zero inverse" ((0 : F)⁻¹ == 0)
  check "GHASH generic division" (x / x == 1)
  check "GHASH division by zero" (x / 0 == 0)
  check "GHASH zero numerator" ((0 : F) / x == 0)
  check "GHASH natural power" (x ^ (2 ^ 128 - 2 : ℕ) == expectedInverse)
  check "GHASH integer power" (x ^ (-((2 ^ 128 - 1 : ℕ) : ℤ)) == 1)
  check "GHASH zero power" ((0 : F) ^ (0 : ℕ) == 1)
  check "GHASH positive power of zero" ((0 : F) ^ (2 ^ 128 : ℕ) == 0)
  check "GHASH negative power of zero" ((0 : F) ^ (-1 : ℤ) == 0)
  check "GHASH natural cast" ((2 : F) == 0)
  check "GHASH integer cast" (((-3 : ℤ) : F) == 1)
  check "GHASH natural scalar" ((2 : ℕ) • x == 0)
  check "GHASH integer scalar" ((-3 : ℤ) • x == x)
  check "GHASH rational cast" (((3 / 5 : ℚ) : F) == 1)
  check "GHASH vanishing rational denominator" (((1 / 2 : ℚ) : F) == 0)
  check "GHASH nonnegative rational cast" (((3 / 5 : ℚ≥0) : F) == 1)
  check "GHASH vanishing nonnegative rational denominator" (((1 / 2 : ℚ≥0) : F) == 0)
  check "GHASH rational scalar" ((-3 / 5 : ℚ) • x == x)
  check "GHASH vanishing rational scalar" ((1 / 2 : ℚ) • x == 0)
  check "GHASH nonnegative rational scalar" ((3 / 5 : ℚ≥0) • x == x)
  check "GHASH vanishing nonnegative rational scalar" ((1 / 2 : ℚ≥0) • x == 0)

/-- Check reduction, reference products, and total field operations in the four presentations. -/
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
  let aes := AesField.ofBitVec (0x53#8)
  check "AES reduction"
    (((AesField.ofBitVec (0x80#8)) * AesField.ofBitVec (2#8)).toBitVec == 0x1b#8)
  check "AES reference product"
    (((AesField.ofBitVec (0x57#8)) * AesField.ofBitVec (0x13#8)).toBitVec == 0xfe#8)
  check "AES inverse vector" (aes⁻¹.toBitVec == 0xca#8)
  check "AES generic inverse" (inverseProduct aes == 1)
  check "AES zero inverse" ((0 : AesField)⁻¹ == 0)
  let high := BF128Ghash.ofBitVec (0x80000000000000000000000000000000#128)
  let expectedInverse := BF128Ghash.ofBitVec (0x0b604395d27ef1a8b604395d27ef1a8ee#128)
  check "GHASH reduction" ((high * BF128Ghash.ofBitVec (2#128)).toBitVec == 0x87#128)
  check "GHASH named inverse" (BF128Ghash.invItohTsujii high == expectedInverse)
  checkGhashOperations high expectedInverse
  IO.println "Native field startup and arithmetic checks passed."

end CompPolyTests.NativeSmoke

/-- Entry point for the bounded native smoke test. -/
def main : IO Unit := CompPolyTests.NativeSmoke.run
