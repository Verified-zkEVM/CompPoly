/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Fields.Arith
public import CompPoly.Fields.Binary.Tower.FastDefs

/-!
# Binary tower scalar kernels: table-driven against recursive

`Tower/FastDefs.lean` carries each of `GF(2^8)` multiplication, `GF(2^64)`
multiplication and `GF(2^64)` inversion twice: once as the recursive tower
construction and once driven by a precomputed table. The two are proved equal,
and nothing measured which is faster — which is the whole reason the table
exists.

All six are `UInt64 → UInt64` or `UInt64 → UInt64 → UInt64` on a bare machine
word, so they are the cleanest possible chain targets: no carrier to unbox and
no allocation. `fields-tower-bt128-mul` and `-inv` remain the group for the
128-bit packed representation against its `BitVec` spec; these are a level
below that.

The table rows load a `ByteArray` at module initialisation, so their first
iterations touch cold memory. The calibration ramp doubles as warmup and is
long enough that this does not reach the samples.
-/

public section

open ConcreteBinaryTower

namespace CompPolyBench

/-- Word-level operands for the tower's scalar kernels.

`GF(2^64)` addition is `xor`, so `nonzeroPool` is not needed: the inversion
chain's step already mixes with a fixed operand, and `inv64 0 = 0` is only
reachable if the seed and the constant coincide. -/
private def towerWordRep (suffix representation field : String) (pool : Array UInt64) :
    ChainRep UInt64 :=
  { representation := representation, field := field, suffix := suffix,
    pool := pool, constant := pool.getD 0 1,
    checksum := fun x ↦ x.toNat, sink := u64Sink }

/-- Draw a pool of nonzero words below `2 ^ bits` from the group's stream.

The bound is not cosmetic. `mul8T_eq_mul8` (`Tower/Fast.lean:441`) holds only
for operands below `2 ^ 8`, because `mul8T` indexes a 65536-entry table with
`(a <<< 8) + b`; fed a full machine word it reads out of range, `get!` returns
zero, and the group reports a digest mismatch and a meaningless time. The
level-6 kernels take the whole word. -/
private def towerWordPool (bits : Nat) (gen : StdGen) : Array UInt64 × StdGen :=
  let (values, gen) := (randomNatArray fieldPoolSize (2 ^ bits - 2)).run gen
  (values.map fun n ↦ UInt64.ofNat (n + 1), gen)

/-- Time `GF(2^8)` multiplication, recursive against table-driven. -/
private def runTowerMul8 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (pool, gen) := towerWordPool 8 gen
  let group ← runBinOpGroup "fields-tower-bt8-mul"
    "Binary tower multiplication (GF(2^8)), table against recursive"
    "tower-bt8" "mul" chainRounds throughputRounds
    (towerWordRep "rec" "UInt64" "GF(2^8) recursive" pool) Fast.mul8
    (towerWordRep "table" "UInt64" "GF(2^8) table" pool) Fast.mul8T preset
  pure (group, gen)

/-- Time `GF(2^64)` multiplication, recursive against table-driven. -/
private def runTowerMul64 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (pool, gen) := towerWordPool 64 gen
  let group ← runBinOpGroup "fields-tower-bt64-mul"
    "Binary tower multiplication (GF(2^64)), table against recursive"
    "tower-bt64" "mul" chainRounds throughputRounds
    (towerWordRep "rec" "UInt64" "GF(2^64) recursive" pool) Fast.mul64
    (towerWordRep "table" "UInt64" "GF(2^64) table" pool) Fast.mul64T preset
  pure (group, gen)

/-- Time `GF(2^64)` inversion, recursive against table-driven. -/
private def runTowerInv64 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (pool, gen) := towerWordPool 64 gen
  let group ← runUnOpGroup "fields-tower-bt64-inv-word"
    "Binary tower inversion (GF(2^64)), table against recursive"
    "tower-bt64" "inv" "inv (recursive)" "inv (table)"
    (towerWordRep "rec" "UInt64" "GF(2^64) recursive" pool) (· ^^^ ·) Fast.inv64
    (towerWordRep "table" "UInt64" "GF(2^64) table" pool) (· ^^^ ·) Fast.inv64T preset
  pure (group, gen)

/-- Registry entries for the tower's scalar kernels. -/
def towerScalarTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt8-mul",
      "Binary tower multiplication (GF(2^8)), table against recursive"⟩
    runTowerMul8,
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt64-mul",
      "Binary tower multiplication (GF(2^64)), table against recursive"⟩
    runTowerMul64,
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt64-inv-word",
      "Binary tower inversion (GF(2^64)), table against recursive"⟩
    runTowerInv64
]

end CompPolyBench
