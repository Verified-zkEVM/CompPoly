/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Binary.Tower.Fast.Multilinear

/-!
# Binary tower field benchmarks

Times GF(2^128) multiplication and inversion, concrete tower vs packed-word
implementation, cross-checked by the group checksum. Sub-microsecond rows include the
harness's fixed per-iteration cost (roughly 0.4 us), so they are regression
indicators, not operation latencies. The coefficient-evaluation group compares the generic eager
product accumulator with concrete coefficient evaluation, using complete output words.
-/

public section

open ConcreteBinaryTower

namespace CompPolyBench

/-- Input-shape label shared by the tower benchmarks. -/
private def towerShape : String := "64 random 128-bit elements, pairwise"

/-- Limb-fold checksum for packed tower elements; avoids building the 128-bit value. -/
def checksumFastBT128 (x : Fast.FastBT128) : Nat := x.lo.toNat ^^^ x.hi.toNat

/-- The same limb fold on the concrete representation. -/
def checksumConcreteBt128 (x : ConcreteBTField 7) : Nat :=
  ConcreteBTField.toNat x % 2 ^ 64 ^^^ ConcreteBTField.toNat x >>> 64

/-- Pairwise operand sampler over a fixed pool. -/
@[inline] private def towerSampler {E : Type} (xs : Array E) (one : E) : Nat → E × E :=
  fun i ↦ (xs.getD (i % xs.size) one, xs.getD ((i + 17) % xs.size) one)

/-- Time one GF(2^128) operation over the spec and the packed implementation. -/
@[specialize] private def runTowerGroup (groupKey title method : String)
    (concreteOp : ConcreteBTField 7 → ConcreteBTField 7 → ConcreteBTField 7)
    (fastOp : Fast.FastBT128 → Fast.FastBT128 → Fast.FastBT128)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (values, gen) := (randomNatArray 64 (2 ^ 128 - 1)).run gen
  let concreteSample := towerSampler
    (values.map fun n ↦ (fromNat n : ConcreteBTField 7)) (fromNat 1)
  let fastSample := towerSampler (values.map Fast.FastBT128.ofNat) (.ofNat 1)
  let checksumIterations := digestPeriod values.size
  let concreteRecord ← runTimedSpec
    { name := "tower-bt128", representation := "ConcreteBTField",
      method := (method ++ " (ConcreteBTField)"), field := "GF(2^128)", inputShape := towerShape,
      digestIterations := checksumIterations }
    preset (fun i ↦ let (a, b) := concreteSample i; concreteOp a b)
    checksumConcreteBt128
  let fastRecord ← runTimedSpec
    { name := "tower-bt128-fast", representation := "FastBT128",
      method := (method ++ " (FastBT128)"), field := "GF(2^128)", inputShape := towerShape,
      digestIterations := checksumIterations }
    preset (fun i ↦ let (a, b) := fastSample i; fastOp a b) checksumFastBT128
  pure ({ groupKey := groupKey, title := title,
          records := #[concreteRecord, fastRecord] }, gen)

/-- Run the GF(2^128) multiplication benchmark. -/
private def runTowerMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runTowerGroup "fields-tower-bt128-mul" "Binary tower multiplication (GF(2^128))" "mul"
    concrete_mul Fast.FastBT128.mul
    preset gen

/-- Run the GF(2^128) inversion benchmark. -/
private def runTowerInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runTowerGroup "fields-tower-bt128-inv" "Binary tower inversion (GF(2^128))" "inv"
    (fun a _ ↦ concrete_inv a) (fun a _ ↦ a.inv)
    preset gen

/-- Compare eager packed coefficient accumulation with concrete evaluation at eight points. -/
private def runTowerCoeffEval (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (randomNatArray 48 (2 ^ 128 - 1)).run gen
  let coefficients : Vector Nat 16 := Vector.ofFn fun i ↦ values.getD i.val 0
  let points : Vector (Vector Nat 4) 8 := Vector.ofFn fun i ↦
    Vector.ofFn fun j ↦ values.getD (16 + 4 * i.val + j.val) 0
  let concreteCoefficients := coefficients.map (fromNat (k := 7))
  let fastCoefficients := coefficients.map Fast.FastBT128.ofNat
  let concretePoints := points.map (Vector.map (fromNat (k := 7)))
  let fastPoints := points.map (Vector.map Fast.FastBT128.ofNat)
  let shape := "16 coefficients, 4 variables, 8 points; random 128-bit words"
  let concreteRecord ← runTimedSpec
    { name := "tower-bt128-coeff-eval", representation := "ConcreteBTField",
      method := "coefficient evaluation", field := "GF(2^128)", inputShape := shape,
      digestIterations := digestPeriod 8 }
    preset (fun i ↦ CompPoly.CMlPolynomial.eval concreteCoefficients
      concretePoints[i % 8]) ConcreteBTField.toNat
  let fastRecord ← runTimedSpec
    { name := "tower-bt128-fast-coeff-eval", representation := "FastBT128",
      method := "eager product accumulation", field := "GF(2^128)", inputShape := shape,
      digestIterations := digestPeriod 8 }
    preset (fun i ↦ CompPoly.CMlPolynomial.evalWithProducts (· * ·)
      (AddMonoidHom.id Fast.FastBT128) fastCoefficients fastPoints[i % 8]) Fast.FastBT128.toNat
  pure ({ groupKey := "fields-tower-bt128-coeff-eval",
          title := "Binary tower coefficient evaluation (GF(2^128))",
          records := #[concreteRecord, fastRecord] }, gen)

/-- Registry entries for the binary tower benchmarks. -/
def towerTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt128-mul", "Binary tower multiplication (GF(2^128))"⟩
    runTowerMul,
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt128-inv", "Binary tower inversion (GF(2^128))"⟩
    runTowerInv,
  BenchTask.fromGroupRunner
    ⟨"fields-tower-bt128-coeff-eval", "Binary tower coefficient evaluation (GF(2^128))"⟩
    runTowerCoeffEval
]

end CompPolyBench
