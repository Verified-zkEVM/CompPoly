/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
module

public meta import CompPoly.Fields.Binary.Common

/-!
# Carryless Multiplication Regression Tests

`carryLessMul` replaced a `Finset.fold` over `Fin 256` that took `B256` inputs.
The removed implementation is kept here as `clMulBaseline`, generalized to the
operand width, and the two are required to agree, so the replacement stays
pinned to the behaviour it replaced.

Both instantiations in use are covered: `clMul`, the 128-bit one the GHASH
development multiplies through, and the 64-bit one behind `BF64.mul`. The
baseline takes operands already widened to the result width, which is where the
original fold met them.
-/

public meta section

namespace CompPolyTests.Fields.Binary

open BinaryField

/-- The removed implementation: a `Finset.fold` over the operand width, on
inputs already widened to the result width. -/
private def clMulBaseline {w : ℕ} (a b : BitVec w) : BitVec w :=
  (Finset.univ : Finset (Fin w)).fold BitVec.xor 0
    (fun i => if a.getLsb i then b <<< i.val else 0)

private def denseA : B128 := (0xDEADBEEFCAFEBABE0123456789ABCDEF : B128)
private def denseB : B128 := (0xFEEDFACEFEEDFACE1122334455667788 : B128)

/-- A sparse operand of the shape `fold_step` produces as `R_val`. -/
private def sparseB : B128 := (0x87 : B128)

#guard clMul denseA denseB == clMulBaseline (to256 denseA) (to256 denseB)
#guard clMul denseA sparseB == clMulBaseline (to256 denseA) (to256 sparseB)
#guard clMul denseA 1 == to256 denseA
#guard clMul denseA 0 == 0

/-! ## The 64-bit instance

`BF64.mul` is `reduce (carryLessMul (w := 128) a b)`, so the width-64 operand
case carries the same obligation as the width-128 one above. `0x1B` is the low
part of the `GF(2^64)` modulus, a sparse operand of the shape `reduce` feeds
back in. -/

private def dense64A : BitVec 64 := (0x0123456789ABCDEF : BitVec 64)
private def dense64B : BitVec 64 := (0xFEEDFACECAFEBABE : BitVec 64)
private def sparse64B : BitVec 64 := (0x1B : BitVec 64)

#guard carryLessMul (w := 128) dense64A dense64B
       == clMulBaseline (zeroExtendTo (w := 128) dense64A) (zeroExtendTo (w := 128) dense64B)
#guard carryLessMul (w := 128) dense64A sparse64B
       == clMulBaseline (zeroExtendTo (w := 128) dense64A) (zeroExtendTo (w := 128) sparse64B)
#guard carryLessMul (w := 128) dense64A 1 == zeroExtendTo (w := 128) dense64A
#guard carryLessMul (w := 128) dense64A 0 == 0

end CompPolyTests.Fields.Binary
