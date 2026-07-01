/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast
import CompPoly.Fields.Goldilocks.FastExt

/-!
# Extern-Backed Fast Goldilocks Tests

Runtime regression checks for `Goldilocks.Fast.Ext`. These tests compare the
extern-backed operations against the verified `Goldilocks.Fast` implementation.

The checks live in an executable rather than `#guard`s because Lean's module
interpreter cannot call project-local C externs during elaboration.

Run this file with:
`lake exe CompPolyGoldilocksFastExtTests`
-/

namespace CompPolyTests.Fields.Goldilocks.FastExt

private def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    return true
  else
    IO.eprintln s!"failed: {name}"
    return false

private def a : Goldilocks.Fast.Field := 987654321

private def b : Goldilocks.Fast.Field := 54321

private def c : Goldilocks.Fast.Field := 73

private def nearTop : Goldilocks.Fast.Field :=
  Goldilocks.Fast.ofNat (Goldilocks.Basic.fieldSize - 1)

private def maxUInt64 : Goldilocks.Fast.Field :=
  Goldilocks.Fast.ofUInt64 (UInt64.ofNat (UInt64.size - 1))

private def runChecks : IO Bool := do
  let ok1 ← check "mulWithMulHi" (Goldilocks.Fast.Ext.mulWithMulHi a b = a * b)
  let ok2 ← check "mulNative" (Goldilocks.Fast.Ext.mulNative a b = a * b)
  let ok3 ←
    check "squareWithMulHi" (Goldilocks.Fast.Ext.squareWithMulHi a = Goldilocks.Fast.square a)
  let ok4 ←
    check "squareNative" (Goldilocks.Fast.Ext.squareNative a = Goldilocks.Fast.square a)
  let ok5 ←
    check "squareNNative" (Goldilocks.Fast.Ext.squareNNative a 8 = Goldilocks.Fast.squareN a 8)
  let ok6 ← check "invNative" (Goldilocks.Fast.Ext.invNative c = c⁻¹)
  let ok7 ← check "divNative" (Goldilocks.Fast.Ext.divNative a c = a / c)
  let ok8 ←
    check "mulNative near modulus"
      (Goldilocks.Fast.Ext.mulNative nearTop nearTop = nearTop * nearTop)
  let ok9 ←
    check "mulNative max UInt64" (Goldilocks.Fast.Ext.mulNative maxUInt64 a = maxUInt64 * a)
  let ok10 ←
    check "divNative nontrivial" (Goldilocks.Fast.Ext.divNative b c = b / c)
  return ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 && ok10

end CompPolyTests.Fields.Goldilocks.FastExt

/-- Run the extern-backed Goldilocks regression checks. -/
def main : IO UInt32 := do
  if ← CompPolyTests.Fields.Goldilocks.FastExt.runChecks then
    return 0
  else
    return 1
