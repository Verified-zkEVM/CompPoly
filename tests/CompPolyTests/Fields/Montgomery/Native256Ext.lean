/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256Ext
import CompPoly.Fields.BLS12_377.Fast
import CompPoly.Fields.BLS12_381.Fast
import CompPoly.Fields.BN254.Fast
import CompPoly.Fields.Secp256k1.Fq.Fast
import CompPoly.Fields.Secp256k1.Fr.Fast

/-!
# Extern-Backed 256-bit Montgomery Tests

Runtime regression checks for `Montgomery.Native256.Ext`: the operations built on the
extern widening-mul primitive are compared against the verified implementation over
every 256-bit Montgomery field, on boundary values and a deterministic pseudorandom
sweep. The Lean models are already proved equal to the verified operations; what these
checks exercise is the trusted C in `native/comppoly_mont256.c`, which proofs cannot
see. They live in an executable because the module interpreter cannot call
project-local externs.

Run this file with: `lake exe CompPolyMont256ExtTests`
-/

namespace CompPolyTests.Fields.Montgomery.Native256Ext

open Montgomery.Native256

private def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    return true
  else
    IO.eprintln s!"failed: {name}"
    return false

/-- One step of Knuth's MMIX 64-bit LCG. -/
private def lcg (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- Draw a 256-bit natural (and the advanced state) from four LCG steps. -/
private def drawNat (s : UInt64) : Nat × UInt64 :=
  let s1 := lcg s
  let s2 := lcg s1
  let s3 := lcg s2
  let s4 := lcg s3
  (s1.toNat + (s2.toNat <<< 64) + (s3.toNat <<< 128) + (s4.toNat <<< 192), s4)

/-- `n` deterministic pseudorandom field samples from seed `s`. -/
private def samples (modulus : ℕ) [Mont256Field modulus] :
    ℕ → UInt64 → List (FastField modulus)
  | 0, _ => []
  | n + 1, s =>
    let (v, s') := drawNat s
    (v : FastField modulus) :: samples modulus n s'

/-- Boundary values: small residues, residues at the top of the canonical range, and
inputs exercising the literal reduction from the top of the 256-bit range. -/
private def edgeCases (modulus : ℕ) [Mont256Field modulus] : List (FastField modulus) :=
  [(0 : FastField modulus), 1, 2, (modulus - 1 : ℕ), (modulus - 2 : ℕ),
    (2 ^ 255 : ℕ), (2 ^ 256 - 1 : ℕ)]

/-- Per-element checks: squaring through the extern widening-mul primitive. -/
private def checkOne (modulus : ℕ) [P : Mont256Field modulus] (label : String)
    (x : FastField modulus) : IO Bool := do
  check s!"{label}: squareWithMulHi" (Ext.squareWithMulHi x = square x)

/-- Per-pair checks: multiplication through the extern widening-mul primitive. -/
private def checkPair (modulus : ℕ) [Mont256Field modulus] (label : String)
    (x y : FastField modulus) : IO Bool := do
  check s!"{label}: mulWithMulHi" (Ext.mulWithMulHi x y = mul x y)

/-- Run all checks for one 256-bit Montgomery field. -/
private def checkField (modulus : ℕ) [Mont256Field modulus] (label : String) : IO Bool := do
  let xs := edgeCases modulus ++ samples modulus 12 0xC0FFEE
  let mut ok := true
  for x in xs do
    ok := (← checkOne modulus label x) && ok
    for y in xs do
      ok := (← checkPair modulus label x y) && ok
  return ok

/-- Aggregate result over all five 256-bit Montgomery fields. -/
private def runChecks : IO Bool := do
  let ok1 ← checkField BN254.scalarFieldSize "BN254.Fr"
  let ok2 ← checkField BLS12_381.scalarFieldSize "BLS12_381.Fr"
  let ok3 ← checkField BLS12_377.scalarFieldSize "BLS12_377.Fr"
  let ok4 ← checkField Secp256k1.SCALAR_FIELD_CARD "secp256k1.Fr"
  let ok5 ← checkField Secp256k1.BASE_FIELD_CARD "secp256k1.Fq"
  return ok1 && ok2 && ok3 && ok4 && ok5

end CompPolyTests.Fields.Montgomery.Native256Ext

/-- Run the extern-backed 256-bit Montgomery regression checks. -/
def main : IO UInt32 := do
  if ← CompPolyTests.Fields.Montgomery.Native256Ext.runChecks then
    IO.println "all extern-backed Montgomery checks passed"
    return 0
  else
    return 1
