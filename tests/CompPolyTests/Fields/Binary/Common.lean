/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
module

public meta import CompPoly.Fields.Binary.Common

/-!
# Carryless Multiplication Regression Tests

`clMul : B128 → B128 → B256` replaced a `Finset.fold` over `Fin 256` that took
`B256` inputs. The removed implementation is kept here as `clMulBaseline` and the
two are required to agree, so the replacement stays pinned to the behaviour it
replaced.
-/

public meta section

namespace CompPolyTests.Fields.Binary

open BinaryField

/-- The removed implementation: `Finset.fold` over `Fin 256`, on `B256` inputs. -/
private def clMulBaseline (a b : B256) : B256 :=
  (Finset.univ : Finset (Fin 256)).fold BitVec.xor 0
    (fun i => if a.getLsb i then b <<< i.val else 0)

private def denseA : B128 := (0xDEADBEEFCAFEBABE0123456789ABCDEF : B128)
private def denseB : B128 := (0xFEEDFACEFEEDFACE1122334455667788 : B128)

/-- A sparse operand of the shape `fold_step` produces as `R_val`. -/
private def sparseB : B128 := (0x87 : B128)

#guard clMul denseA denseB == clMulBaseline (to256 denseA) (to256 denseB)
#guard clMul denseA sparseB == clMulBaseline (to256 denseA) (to256 sparseB)
#guard clMul denseA 1 == to256 denseA
#guard clMul denseA 0 == 0

end CompPolyTests.Fields.Binary
