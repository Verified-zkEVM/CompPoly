/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/

import CompPolyBench.Common
import CompPoly.Fields.BabyBear.Ext4
import CompPoly.Fields.KoalaBear.Ext4

/-!
# Degree-4 extension-field benchmarks

Times the two extension-field operations a STARK verifier spends its budget on: multiplication
and inversion.

Multiplication and inversion are in *separate* groups because the harness cross-checks that all
records within a group produce the same checksum — a group is a set of alternative
implementations of one operation, not a set of different operations.

Comparing the two reported averages is the measurement behind the "replace Fermat with a
norm-based inverse" note in `docs/wiki/field-extensions.md`: inversion is currently
`x ^ (q^d - 2)`, so it should cost on the order of `d · log q` multiplications.
-/

open CompPoly CompPoly.Extension

namespace CompPolyBench

/-- Input-shape label shared by the degree-4 extension benchmarks. -/
private def ext4Shape : String := "64 random degree-4 elements, pairwise"

/-- Checksum for KoalaBear degree-4 extension elements. -/
def checksumKoalaBearExt4 (x : KoalaBear.Ext4) : Nat :=
  x.coeffs.toArray.foldl (fun acc z ↦ acc + z.val) 0

/-- Checksum for BabyBear degree-4 extension elements. -/
def checksumBabyBearExt4 (x : BabyBear.Ext4) : Nat :=
  x.coeffs.toArray.foldl (fun acc z ↦ acc + z.val) 0

/-- Benchmark group metadata for the degree-4 extension fields. -/
def extensionGroupInfos : List BenchGroupInfo := [
  ⟨"fields-extension-koalabear-ext4-mul", "Degree-4 extension multiplication (KoalaBear)"⟩,
  ⟨"fields-extension-koalabear-ext4-inv", "Degree-4 extension inversion (KoalaBear)"⟩,
  ⟨"fields-extension-babybear-ext4-mul", "Degree-4 extension multiplication (BabyBear)"⟩,
  ⟨"fields-extension-babybear-ext4-inv", "Degree-4 extension inversion (BabyBear)"⟩
]

/--
Time one degree-4 extension operation over a field-specific sample, packaged as a single-record
group.

`sample` maps an iteration index to an operand pair; `op` is the operation under test.
-/
private def runExt4Op {E : Type} (groupKey title name method fieldName : String)
    (checksum : E → Nat) (sample : Nat → E × E) (op : E → E → E)
    (measured : Nat) (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let record ← runTimed name "Extension.Ext" method fieldName ext4Shape preset
    (warmupIterations preset) measured
    (fun i ↦ let (a, b) := sample i; op a b) checksum
  pure ({ groupKey := groupKey, title := title, records := #[record] }, gen)

/-- Build the pairwise operand sampler for a degree-4 extension over a `ZMod` base field. -/
private def ext4Sampler {F : Type*} [Field F] [Fintype F] {P : BinomialParams F}
    (values : Array F) : Nat → Ext P × Ext P :=
  let elem (i : Nat) : Ext P :=
    Ext.ofFn fun j ↦ values.getD ((i * P.d + j.val) % values.size) 0
  let xs : Array (Ext P) := Array.ofFn (n := 64) fun i ↦ elem i.val
  fun i ↦ (xs.getD (i % 64) 1, xs.getD ((i + 17) % 64) 1)

/-- Run the KoalaBear degree-4 multiplication benchmark. -/
private def runKoalaBearExt4Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExt4Op "fields-extension-koalabear-ext4-mul"
    "Degree-4 extension multiplication (KoalaBear)" "extension-mul" "mul" "KoalaBear.Ext4"
    checksumKoalaBearExt4 (ext4Sampler (P := KoalaBear.ext4Params) values) (· * ·)
    (preset.selectNat 200000 30000 6000) preset gen

/-- Run the KoalaBear degree-4 inversion benchmark. -/
private def runKoalaBearExt4Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExt4Op "fields-extension-koalabear-ext4-inv"
    "Degree-4 extension inversion (KoalaBear)" "extension-inv" "inv (Fermat)" "KoalaBear.Ext4"
    checksumKoalaBearExt4 (ext4Sampler (P := KoalaBear.ext4Params) values) (fun a _ ↦ a⁻¹)
    (preset.selectNat 2000 300 60) preset gen

/-- Run the BabyBear degree-4 multiplication benchmark. -/
private def runBabyBearExt4Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (babyBearArray 256 false).run gen
  runExt4Op "fields-extension-babybear-ext4-mul"
    "Degree-4 extension multiplication (BabyBear)" "extension-mul" "mul" "BabyBear.Ext4"
    checksumBabyBearExt4 (ext4Sampler (P := BabyBear.ext4Params) values) (· * ·)
    (preset.selectNat 200000 30000 6000) preset gen

/-- Run the BabyBear degree-4 inversion benchmark. -/
private def runBabyBearExt4Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (babyBearArray 256 false).run gen
  runExt4Op "fields-extension-babybear-ext4-inv"
    "Degree-4 extension inversion (BabyBear)" "extension-inv" "inv (Fermat)" "BabyBear.Ext4"
    checksumBabyBearExt4 (ext4Sampler (P := BabyBear.ext4Params) values) (fun a _ ↦ a⁻¹)
    (preset.selectNat 2000 300 60) preset gen

/-- Registry entries for the degree-4 extension benchmarks. -/
def extensionTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-extension-koalabear-ext4-mul", "Degree-4 extension multiplication (KoalaBear)"⟩
    runKoalaBearExt4Mul,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-koalabear-ext4-inv", "Degree-4 extension inversion (KoalaBear)"⟩
    runKoalaBearExt4Inv,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-babybear-ext4-mul", "Degree-4 extension multiplication (BabyBear)"⟩
    runBabyBearExt4Mul,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-babybear-ext4-inv", "Degree-4 extension inversion (BabyBear)"⟩
    runBabyBearExt4Inv
]

end CompPolyBench
