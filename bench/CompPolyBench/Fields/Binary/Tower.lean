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

The coefficient-evaluation group compares the generic eager product accumulator with
concrete coefficient evaluation, using complete output words. Scalar operations live in
`Tower/Scalar.lean` and use workloads matched with Binius.
-/

public section

open ConcreteBinaryTower

namespace CompPolyBench

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
    ⟨"fields-tower-bt128-coeff-eval", "Binary tower coefficient evaluation (GF(2^128))"⟩
    runTowerCoeffEval
]

end CompPolyBench
