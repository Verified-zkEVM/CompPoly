/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Fields.Binary.Common

/-!
  # Benchmarks on new `clMul` vs. the old implementation

  The new `clMul : B128 → B128 → B256` uses `Fin.foldl` and widens with
  `to256 b`. The old implementation was removed from Common.lean; it is
  included below as `clMul_baseline : B256 → B256 → B256`.

  This file is not imported by `CompPolyTests.lean` so `lake test` stays
  fast.

  ## Running

  ```bash
  lake build CompPolyTests.Fields.Binary.CommonBench
  ```
-/

open BinaryField

/-- Old baseline: `Finset.fold` over `Fin 256`, takes `B256` inputs. -/
private def clMul_baseline (a b : B256) : B256 :=
  (Finset.univ : Finset (Fin 256)).fold BitVec.xor 0
    (fun i => if a.getLsb i then b <<< i.val else 0)

/-! ## Correctness — baseline and new version must agree -/

private def tv_a : B128 := (0xDEADBEEFCAFEBABE0123456789ABCDEF : B128)
private def tv_b : B128 := (0xFEEDFACEFEEDFACE1122334455667788 : B128)

-- Reference: widen then baseline
private def ref_result : B256 := clMul_baseline (to256 tv_a) (to256 tv_b)

#guard clMul tv_a tv_b == ref_result

-- Sparse operand (like `R_val` in `fold_step`)
private def tv_sparse : B128 := (0x87 : B128)
private def ref_sparse : B256 := clMul_baseline (to256 tv_a) (to256 tv_sparse)

#guard clMul tv_a tv_sparse == ref_sparse

-- Identity and zero
#guard clMul tv_a 1 == to256 tv_a
#guard clMul tv_a 0 == 0

/-! ## Benchmarks — fixed dense inputs -/

private def benchFixedBaseline (n : Nat) (a b : B256) : IO B256 := do
  let mut r : B256 := 0
  for _ in List.range n do
    r := clMul_baseline a b
  return r

private def benchFixedNew (n : Nat) (a b : B128) : IO B256 := do
  let mut r : B256 := 0
  for _ in List.range n do
    r := clMul a b
  return r

#eval timeit "=== Fixed dense 128x128 (10000 iters) ===" (pure ())
#eval timeit "  clMul_baseline(to256)" (benchFixedBaseline 10000 (to256 tv_a) (to256 tv_b))
#eval timeit "  clMul (new)          " (benchFixedNew 10000 tv_a tv_b)

/-! ## Benchmarks — varied inputs -/

private def benchVariedBaseline (n : Nat) (a b : B256) : IO B256 := do
  let mut r : B256 := 0
  for i in List.range n do
    let a' := a ^^^ (BitVec.ofNat 256 (i * 0x9E3779B97F4A7C15))
    let b' := b ^^^ (BitVec.ofNat 256 (i * 0x6C62272E07BB0142))
    r := clMul_baseline a' b'
  return r

private def benchVariedNew (n : Nat) (a b : B128) : IO B256 := do
  let mut r : B256 := 0
  for i in List.range n do
    let a' := a ^^^ (BitVec.ofNat 128 (i * 0x9E3779B97F4A7C15))
    let b' := b ^^^ (BitVec.ofNat 128 (i * 0x6C62272E07BB0142))
    r := clMul a' b'
  return r

#eval timeit "=== Varied inputs 128x128 (10000 iters) ===" (pure ())
#eval timeit "  clMul_baseline(to256)" (benchVariedBaseline 10000 (to256 tv_a) (to256 tv_b))
#eval timeit "  clMul (new)          " (benchVariedNew 10000 tv_a tv_b)

/-! ## Benchmarks — sparse inputs (128×8 bit, like fold_step) -/

#eval timeit "=== Sparse 128x8 bit (10000 iters) ===" (pure ())
#eval timeit "  clMul_baseline(to256)" (benchFixedBaseline 10000 (to256 tv_a) (to256 tv_sparse))
#eval timeit "  clMul (new)          " (benchFixedNew 10000 tv_a tv_sparse)
