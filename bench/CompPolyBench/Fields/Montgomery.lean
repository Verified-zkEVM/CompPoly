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
public import CompPoly.Fields.Secp256k1

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

/-- Time the three inversion implementations of one scalar field as a single group. -/
private def runScalarInv (modulus : Nat) [Mont64x8Field modulus] [GcdData modulus]
    (groupKey title fieldName fastFieldName : String)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let (values, gen) := (zmodArray modulus 256 false).run gen
  let fastValues := values.map FastField.ofField
  let checksumIterations := digestPeriod values.size
  let zmodRecord ← runTimedSpec
    { name := "scalar-inv-xgcd", representation := "ZMod", method := "inv (xgcd)",
      field := fieldName, inputShape := scalarInvShape, digestIterations := checksumIterations }
    preset (fun i ↦ (values.getD (i % values.size) 1)⁻¹) checksumZMod
  let gcdRecord ← runTimedSpec
    { name := "scalar-inv-gcd", representation := "Mont64x8", method := "inv (binary GCD)",
      field := fastFieldName, inputShape := scalarInvShape, digestIterations := checksumIterations }
    preset (fun i ↦ (fastValues.getD (i % fastValues.size) 1).invGcd)
    (fun x ↦ x.toNat)
  let fermatRecord ← runTimedSpec
    { name := "scalar-inv-fermat", representation := "Mont64x8", method := "inv (Fermat)",
      field := fastFieldName, inputShape := scalarInvShape, digestIterations := checksumIterations }
    preset (fun i ↦ (fastValues.getD (i % fastValues.size) 1).inv)
    (fun x ↦ x.toNat)
  pure ({ groupKey := groupKey, title := title,
          records := #[zmodRecord, gcdRecord, fermatRecord] }, gen)

/-- Run the BN254 scalar inversion benchmark. -/
private def runBn254ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv BN254.scalarFieldSize "fields-mont64x8-bn254-inv"
    "Scalar-field inversion (BN254)" "BN254.ScalarField" "BN254.Fast.ScalarField"
    preset gen

/-- Run the BLS12-381 scalar inversion benchmark. -/
private def runBls12_381ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv BLS12_381.scalarFieldSize "fields-mont64x8-bls12-381-inv"
    "Scalar-field inversion (BLS12-381)" "BLS12_381.ScalarField" "BLS12_381.Fast.ScalarField"
    preset gen

/-- Run the BLS12-377 scalar inversion benchmark. -/
private def runBls12_377ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv BLS12_377.scalarFieldSize "fields-mont64x8-bls12-377-inv"
    "Scalar-field inversion (BLS12-377)" "BLS12_377.ScalarField" "BLS12_377.Fast.ScalarField"
    preset gen

/-- Run the secp256k1 scalar-field inversion benchmark. -/
private def runSecp256k1ScalarInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv Secp256k1.scalarFieldSize "fields-mont64x8-secp256k1-scalar-inv"
    "Scalar-field inversion (secp256k1)" "Secp256k1.ScalarField" "Secp256k1.Fast.ScalarField"
    preset gen

/-- Run the secp256k1 base-field inversion benchmark. -/
private def runSecp256k1BaseInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runScalarInv Secp256k1.baseFieldSize "fields-mont64x8-secp256k1-base-inv"
    "Base-field inversion (secp256k1)" "Secp256k1.BaseField" "Secp256k1.Fast.BaseField"
    preset gen

/-- Registry entries for the eight-limb field inversion benchmarks. -/
def montgomeryInvTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-bn254-inv", "Scalar-field inversion (BN254)"⟩
    runBn254ScalarInv,
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-bls12-381-inv", "Scalar-field inversion (BLS12-381)"⟩
    runBls12_381ScalarInv,
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-bls12-377-inv", "Scalar-field inversion (BLS12-377)"⟩
    runBls12_377ScalarInv,
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-secp256k1-scalar-inv", "Scalar-field inversion (secp256k1)"⟩
    runSecp256k1ScalarInv,
  BenchTask.fromGroupRunner
    ⟨"fields-mont64x8-secp256k1-base-inv", "Base-field inversion (secp256k1)"⟩
    runSecp256k1BaseInv
]

end CompPolyBench
