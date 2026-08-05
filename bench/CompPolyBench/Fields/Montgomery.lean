/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.BN254
public import CompPoly.Fields.BLS12_381
public import CompPoly.Fields.BLS12_377

/-!
# Scalar-field inversion benchmarks

Times inversion over the eight-limb Montgomery scalar fields. Each group runs three
implementations of the same operation on shared inputs: the canonical `ZMod` inverse,
the checked binary-GCD inverse, and Fermat exponentiation, so the group checksum
cross-checks all three.
-/

public section

open Montgomery.Native64x8 (FastField Mont64x8Field GcdData)

namespace CompPolyBench

/-- Input-shape label shared by the scalar inversion benchmarks. -/
private def scalarInvShape : String := "256 random elements"

/-- Benchmark group metadata for scalar-field inversion. -/
def montgomeryInvGroupInfos : List BenchGroupInfo := [
  ⟨"fields-mont64x8-bn254-inv", "Scalar-field inversion (BN254)"⟩,
  ⟨"fields-mont64x8-bls12-381-inv", "Scalar-field inversion (BLS12-381)"⟩,
  ⟨"fields-mont64x8-bls12-377-inv", "Scalar-field inversion (BLS12-377)"⟩
]

/-- Time the three inversion implementations of one scalar field as a single group. -/
private def runScalarInv (modulus : Nat) [Mont64x8Field modulus] [GcdData modulus]
    (groupKey title fieldName fastFieldName : String)
    (zmodBudget gcdBudget fermatBudget : BenchPreset → Nat)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (values, gen) := (zmodArray modulus 256 false).run gen
  let fastValues := values.map FastField.ofField
  let warmup := warmupIterations preset
  let zmodMeasured := zmodBudget preset
  let gcdMeasured := gcdBudget preset
  let fermatMeasured := fermatBudget preset
  let checksumIterations := groupChecksumIterations zmodMeasured [gcdMeasured, fermatMeasured]
  let zmodRecord ← runTimed "scalar-inv-xgcd" "ZMod" "inv (xgcd)" fieldName
    scalarInvShape preset warmup zmodMeasured
    (fun i ↦ (values.getD (i % values.size) 1)⁻¹)
    checksumZMod (checksumIterations := checksumIterations)
  let gcdRecord ← runTimed "scalar-inv-gcd" "Mont64x8" "inv (binary GCD)" fastFieldName
    scalarInvShape preset warmup gcdMeasured
    (fun i ↦ (fastValues.getD (i % fastValues.size) 1).invGcd)
    (fun x ↦ x.toNat) (checksumIterations := checksumIterations)
  let fermatRecord ← runTimed "scalar-inv-fermat" "Mont64x8" "inv (Fermat)" fastFieldName
    scalarInvShape preset warmup fermatMeasured
    (fun i ↦ (fastValues.getD (i % fastValues.size) 1).inv)
    (fun x ↦ x.toNat) (checksumIterations := checksumIterations)
  pure ({ groupKey := groupKey, title := title,
          records := #[zmodRecord, gcdRecord, fermatRecord] }, gen)

/-- Run the BN254 scalar inversion benchmark. -/
private def runBn254ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv BN254.scalarFieldSize "fields-mont64x8-bn254-inv"
    "Scalar-field inversion (BN254)" "BN254.ScalarField" "BN254.Fast.ScalarField"
    (fun p ↦ p.selectNat 20000 3000 600) (fun p ↦ p.selectNat 100000 15000 3000)
    (fun p ↦ p.selectNat 24000 3600 720) preset gen

/-- Run the BLS12-381 scalar inversion benchmark. -/
private def runBls12_381ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv BLS12_381.scalarFieldSize "fields-mont64x8-bls12-381-inv"
    "Scalar-field inversion (BLS12-381)" "BLS12_381.ScalarField" "BLS12_381.Fast.ScalarField"
    (fun p ↦ p.selectNat 20000 3000 600) (fun p ↦ p.selectNat 100000 15000 3000)
    (fun p ↦ p.selectNat 24000 3600 720) preset gen

/-- Run the BLS12-377 scalar inversion benchmark. -/
private def runBls12_377ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv BLS12_377.scalarFieldSize "fields-mont64x8-bls12-377-inv"
    "Scalar-field inversion (BLS12-377)" "BLS12_377.ScalarField" "BLS12_377.Fast.ScalarField"
    (fun p ↦ p.selectNat 20000 3000 600) (fun p ↦ p.selectNat 100000 15000 3000)
    (fun p ↦ p.selectNat 24000 3600 720) preset gen

/-- Registry entries for the scalar-field inversion benchmarks. -/
def montgomeryInvTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-bn254-inv", "Scalar-field inversion (BN254)"⟩
    runBn254ScalarInv,
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-bls12-381-inv", "Scalar-field inversion (BLS12-381)"⟩
    runBls12_381ScalarInv,
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-bls12-377-inv", "Scalar-field inversion (BLS12-377)"⟩
    runBls12_377ScalarInv
]

end CompPolyBench
