/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.BabyBear.Ext4
public import CompPoly.Fields.KoalaBear.Ext4
public import CompPoly.Fields.KoalaBear.Ext5
public import CompPoly.Fields.KoalaBear.Ext6

/-!
# Extension-field benchmarks

Times the two extension-field operations a STARK verifier spends its budget on: multiplication
and inversion. Covers the degree-4 binomial extensions plus the two general-modulus KoalaBear
extensions, `Ext5` (`X^5 + X^2 - 1`) and `Ext6` (`X^6 + X^3 + 1`).

Multiplication and inversion are in *separate* groups because the harness cross-checks that all
records within a group produce the same checksum — a group is a set of alternative
implementations of one operation, not a set of different operations.

Two comparisons are the point of this file:

* `mul` across degrees 4, 5 and 6 tracks how `Ext.mul` scales in `d`. Since `mul_eq_mulTbl`
  routes compilation through the `red` reduction table, the growth should be roughly `O(d^3)`;
  before that change it was `O(d^5)`.
* `mul` against `inv` at the same degree is the measurement behind the "replace Fermat with a
  norm-based inverse" note in `docs/wiki/field-extensions.md`: inversion is currently
  `x ^ (q^d - 2)`, so it should cost on the order of `d · log q` multiplications.
-/

public section

open CompPoly CompPoly.Extension

namespace CompPolyBench

/-- Input-shape label for the extension benchmarks at a given degree. -/
private def extShape (d : Nat) : String := s!"64 random degree-{d} elements, pairwise"

/-- Checksum for KoalaBear degree-4 extension elements. -/
def checksumKoalaBearExt4 (x : KoalaBear.Ext4) : Nat :=
  x.coeffs.toArray.foldl (fun acc z ↦ acc + z.val) 0

/-- Checksum for BabyBear degree-4 extension elements. -/
def checksumBabyBearExt4 (x : BabyBear.Ext4) : Nat :=
  x.coeffs.toArray.foldl (fun acc z ↦ acc + z.val) 0

/-- Checksum for KoalaBear degree-5 extension elements. -/
def checksumKoalaBearExt5 (x : KoalaBear.Ext5) : Nat :=
  x.coeffs.toArray.foldl (fun acc z ↦ acc + z.val) 0

/-- Checksum for KoalaBear degree-6 extension elements. -/
def checksumKoalaBearExt6 (x : KoalaBear.Ext6) : Nat :=
  x.coeffs.toArray.foldl (fun acc z ↦ acc + z.val) 0

/--
Time one extension operation over a field-specific sample, packaged as a single-record group.

`sample` maps an iteration index to an operand pair; `op` is the operation under test.
-/
private def runExtOp {E : Type} (groupKey title name method fieldName shape : String)
    (checksum : E → Nat) (sample : Nat → E × E) (op : E → E → E)
    (measured : Nat) (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let record ← runTimed name "Extension.Ext" method fieldName shape preset
    (warmupIterations preset) measured
    (fun i ↦ let (a, b) := sample i; op a b) checksum
  pure ({ groupKey := groupKey, title := title, records := #[record] }, gen)

/-- Build the pairwise operand sampler for an extension over a `ZMod` base field. -/
private def extSampler {F : Type*} [Field F] [Fintype F] {P : ExtensionParams F}
    (values : Array F) : Nat → Ext P × Ext P :=
  let elem (i : Nat) : Ext P :=
    Ext.ofFn fun j ↦ values.getD ((i * P.d + j.val) % values.size) 0
  let xs : Array (Ext P) := Array.ofFn (n := 64) fun i ↦ elem i.val
  fun i ↦ (xs.getD (i % 64) 1, xs.getD ((i + 17) % 64) 1)

/-- Run the KoalaBear degree-4 multiplication benchmark. -/
private def runKoalaBearExt4Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExtOp "fields-extension-koalabear-ext4-mul"
    "Degree-4 extension multiplication (KoalaBear)" "extension-mul" "mul" "KoalaBear.Ext4"
    (extShape 4)
    checksumKoalaBearExt4 (extSampler (P := KoalaBear.ext4Params.toExtensionParams) values) (· * ·)
    (preset.selectNat 200000 30000 6000) preset gen

/-- Run the KoalaBear degree-4 inversion benchmark. -/
private def runKoalaBearExt4Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExtOp "fields-extension-koalabear-ext4-inv"
    "Degree-4 extension inversion (KoalaBear)" "extension-inv" "inv (Fermat)" "KoalaBear.Ext4"
    (extShape 4)
    checksumKoalaBearExt4 (extSampler (P := KoalaBear.ext4Params.toExtensionParams) values)
      (fun a _ ↦ a⁻¹)
    (preset.selectNat 2000 300 60) preset gen

/-- Run the BabyBear degree-4 multiplication benchmark. -/
private def runBabyBearExt4Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (babyBearArray 256 false).run gen
  runExtOp "fields-extension-babybear-ext4-mul"
    "Degree-4 extension multiplication (BabyBear)" "extension-mul" "mul" "BabyBear.Ext4"
    (extShape 4)
    checksumBabyBearExt4 (extSampler (P := BabyBear.ext4Params.toExtensionParams) values) (· * ·)
    (preset.selectNat 200000 30000 6000) preset gen

/-- Run the BabyBear degree-4 inversion benchmark. -/
private def runBabyBearExt4Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (babyBearArray 256 false).run gen
  runExtOp "fields-extension-babybear-ext4-inv"
    "Degree-4 extension inversion (BabyBear)" "extension-inv" "inv (Fermat)" "BabyBear.Ext4"
    (extShape 4)
    checksumBabyBearExt4 (extSampler (P := BabyBear.ext4Params.toExtensionParams) values)
      (fun a _ ↦ a⁻¹)
    (preset.selectNat 2000 300 60) preset gen

/-- Run the KoalaBear degree-5 multiplication benchmark. -/
private def runKoalaBearExt5Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExtOp "fields-extension-koalabear-ext5-mul"
    "Degree-5 extension multiplication (KoalaBear)" "extension-mul" "mul" "KoalaBear.Ext5"
    (extShape 5)
    checksumKoalaBearExt5 (extSampler (P := KoalaBear.ext5Params) values) (· * ·)
    (preset.selectNat 200000 30000 6000) preset gen

/-- Run the KoalaBear degree-5 inversion benchmark. -/
private def runKoalaBearExt5Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExtOp "fields-extension-koalabear-ext5-inv"
    "Degree-5 extension inversion (KoalaBear)" "extension-inv" "inv (Fermat)" "KoalaBear.Ext5"
    (extShape 5)
    checksumKoalaBearExt5 (extSampler (P := KoalaBear.ext5Params) values) (fun a _ ↦ a⁻¹)
    (preset.selectNat 2000 300 60) preset gen

/-- Run the KoalaBear degree-6 multiplication benchmark. -/
private def runKoalaBearExt6Mul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExtOp "fields-extension-koalabear-ext6-mul"
    "Degree-6 extension multiplication (KoalaBear)" "extension-mul" "mul" "KoalaBear.Ext6"
    (extShape 6)
    checksumKoalaBearExt6 (extSampler (P := KoalaBear.ext6Params) values) (· * ·)
    (preset.selectNat 200000 30000 6000) preset gen

/-- Run the KoalaBear degree-6 inversion benchmark. -/
private def runKoalaBearExt6Inv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (koalaBearArray 256 false).run gen
  runExtOp "fields-extension-koalabear-ext6-inv"
    "Degree-6 extension inversion (KoalaBear)" "extension-inv" "inv (Fermat)" "KoalaBear.Ext6"
    (extShape 6)
    checksumKoalaBearExt6 (extSampler (P := KoalaBear.ext6Params) values) (fun a _ ↦ a⁻¹)
    (preset.selectNat 2000 300 60) preset gen

/-- Registry entries for the extension benchmarks. -/
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
    runBabyBearExt4Inv,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-koalabear-ext5-mul", "Degree-5 extension multiplication (KoalaBear)"⟩
    runKoalaBearExt5Mul,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-koalabear-ext5-inv", "Degree-5 extension inversion (KoalaBear)"⟩
    runKoalaBearExt5Inv,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-koalabear-ext6-mul", "Degree-6 extension multiplication (KoalaBear)"⟩
    runKoalaBearExt6Mul,
  BenchTask.fromGroupRunner
    ⟨"fields-extension-koalabear-ext6-inv", "Degree-6 extension inversion (KoalaBear)"⟩
    runKoalaBearExt6Inv
]

end CompPolyBench
