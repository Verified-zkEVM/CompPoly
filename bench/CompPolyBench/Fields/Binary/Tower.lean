/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Binary.Tower.Fast

/-!
# Binary tower field benchmarks

Times GF(2^128) multiplication and inversion, `BitVec` spec vs packed-word
implementation, cross-checked by the group checksum. Sub-microsecond rows include the
harness's fixed per-iteration cost (roughly 0.4 us), so they are regression
indicators, not operation latencies.
-/

public section

open ConcreteBinaryTower

namespace CompPolyBench

/-- Input-shape label shared by the tower benchmarks. -/
private def towerShape : String := "64 random 128-bit elements, pairwise"

/-- Benchmark group metadata for the binary tower field. -/
def towerGroupInfos : List BenchGroupInfo := [
  ⟨"fields-tower-bt128-mul", "Binary tower multiplication (GF(2^128))"⟩,
  ⟨"fields-tower-bt128-inv", "Binary tower inversion (GF(2^128))"⟩
]

/-- Limb-fold checksum for packed tower elements; avoids building the 128-bit value. -/
def checksumFastBT128 (x : Fast.FastBT128) : Nat := x.lo.toNat ^^^ x.hi.toNat

/-- The same limb fold on the concrete representation. -/
def checksumConcreteBt128 (x : ConcreteBTField 7) : Nat :=
  BitVec.toNat x % 2 ^ 64 ^^^ BitVec.toNat x >>> 64

/-- Pairwise operand sampler over a fixed pool. -/
@[inline] private def towerSampler {E : Type} (xs : Array E) (one : E) : Nat → E × E :=
  fun i ↦ (xs.getD (i % xs.size) one, xs.getD ((i + 17) % xs.size) one)

/-- Time one GF(2^128) operation over the spec and the packed implementation. -/
@[specialize] private def runTowerGroup (groupKey title method : String)
    (concreteOp : ConcreteBTField 7 → ConcreteBTField 7 → ConcreteBTField 7)
    (fastOp : Fast.FastBT128 → Fast.FastBT128 → Fast.FastBT128)
    (concreteBudget fastBudget : BenchPreset → Nat)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (values, gen) := (randomNatArray 64 (2 ^ 128 - 1)).run gen
  let concreteSample := towerSampler
    (values.map fun n ↦ (fromNat n : ConcreteBTField 7)) (fromNat 1)
  let fastSample := towerSampler (values.map Fast.FastBT128.ofNat) (.ofNat 1)
  let warmup := warmupIterations preset
  let concreteMeasured := concreteBudget preset
  let fastMeasured := fastBudget preset
  let checksumIterations := groupChecksumIterations concreteMeasured [fastMeasured]
  let concreteRecord ← runTimed "tower-bt128" "ConcreteBTField"
    (method ++ " (ConcreteBTField)") "GF(2^128)"
    towerShape preset warmup concreteMeasured
    (fun i ↦ let (a, b) := concreteSample i; concreteOp a b)
    checksumConcreteBt128 (checksumIterations := checksumIterations)
  let fastRecord ← runTimed "tower-bt128-fast" "FastBT128"
    (method ++ " (FastBT128)") "GF(2^128)"
    towerShape preset warmup fastMeasured
    (fun i ↦ let (a, b) := fastSample i; fastOp a b)
    checksumFastBT128 (checksumIterations := checksumIterations)
  pure ({ groupKey := groupKey, title := title,
          records := #[concreteRecord, fastRecord] }, gen)

/-- Run the GF(2^128) multiplication benchmark. -/
private def runTowerMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runTowerGroup "fields-tower-bt128-mul" "Binary tower multiplication (GF(2^128))" "mul"
    concrete_mul Fast.FastBT128.mul
    (fun p ↦ p.selectNat 1000 150 30) (fun p ↦ p.selectNat 2000000 300000 60000)
    preset gen

/-- Run the GF(2^128) inversion benchmark. -/
private def runTowerInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runTowerGroup "fields-tower-bt128-inv" "Binary tower inversion (GF(2^128))" "inv"
    (fun a _ ↦ concrete_inv a) (fun a _ ↦ a.inv)
    (fun p ↦ p.selectNat 500 75 15) (fun p ↦ p.selectNat 500000 75000 15000)
    preset gen

/-- Registry entries for the binary tower benchmarks. -/
def towerTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt128-mul", "Binary tower multiplication (GF(2^128))"⟩
    runTowerMul,
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt128-inv", "Binary tower inversion (GF(2^128))"⟩
    runTowerInv
]

end CompPolyBench
