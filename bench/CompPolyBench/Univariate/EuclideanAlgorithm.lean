/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Univariate.EuclideanAlgorithm

/-!
# Univariate Euclidean-Algorithm Benchmarks

Benchmarks comparing the specialized monic gcd path with the normalized
extended-gcd implementation over deterministic KoalaBear workloads.
-/

open CompPoly

namespace CompPolyBench

private def gcdCommonSeeds : List Nat :=
  (List.range 16).map (fun i ↦ i + 3)

private def gcdLeftTailSeeds : List Nat :=
  (List.range 32).map (fun i ↦ i + 101)

private def gcdRightTailSeeds : List Nat :=
  (List.range 32).map (fun i ↦ i + 1001)

private def gcdCoprimeLeftSeeds : List Nat :=
  (List.range 48).map (fun i ↦ i + 17)

private def gcdCoprimeRightSeeds : List Nat :=
  (List.range 48).map (fun i ↦ i + 257)

private def gcdUnevenLeftTailSeeds : List Nat :=
  (List.range 72).map (fun i ↦ i + 409)

private def gcdUnevenRightTailSeeds : List Nat :=
  (List.range 8).map (fun i ↦ i + 2003)

private def gcdPartialThreshold : Nat := 24

private def euclideanWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 3 1 0

private def euclideanMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 100 20 5

private def euclideanFastMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 200 40 10

private def productOfLinearSeeds {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (seeds : List Nat) : CPolynomial F :=
  seeds.foldl
    (fun p (seed : Nat) ↦ p * CPolynomial.linearFactor (seed : F))
    1

private def gcdInputsFromSeeds {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (common leftTail rightTail : List Nat) : CPolynomial F × CPolynomial F :=
  let g := productOfLinearSeeds common
  (g * productOfLinearSeeds leftTail, g * productOfLinearSeeds rightTail)

private def sharedGcdInputs {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial F × CPolynomial F :=
  gcdInputsFromSeeds gcdCommonSeeds gcdLeftTailSeeds gcdRightTailSeeds

private def coprimeGcdInputs {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial F × CPolynomial F :=
  gcdInputsFromSeeds [] gcdCoprimeLeftSeeds gcdCoprimeRightSeeds

private def unevenGcdInputs {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial F × CPolynomial F :=
  gcdInputsFromSeeds gcdCommonSeeds gcdUnevenLeftTailSeeds gcdUnevenRightTailSeeds

private def sharedGcdShape : String :=
  "shared factor degree=16, tails degree=32/32"

private def coprimeGcdShape : String :=
  "coprime products, degree=48/48"

private def unevenGcdShape : String :=
  "shared factor degree=16, tails degree=72/8"

private def partialXgcdShape : String :=
  s!"uneven workload, threshold={gcdPartialThreshold}"

private def checksumXgcdTriple {F : Type*} [Zero F] (checksum : F → Nat)
    (triple : CPolynomial F × CPolynomial F × CPolynomial F) : Nat :=
  mixChecksum
    (mixChecksum (checksumCPolynomial checksum triple.1)
      (checksumCPolynomial checksum triple.2.1))
    (checksumCPolynomial checksum triple.2.2)

private def monicXgcdFst {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p q : CPolynomial F) : CPolynomial F :=
  CPolynomial.monicNormalize ((CPolynomial.xgcd p q 0).1)

private def runGcdComparisonKoala
    (groupKey title inputShape : String)
    (inputs : CPolynomial KoalaBear.Field × CPolynomial KoalaBear.Field)
    (fastInputs : CPolynomial KoalaBear.Fast.Field × CPolynomial KoalaBear.Fast.Field)
    (preset : BenchPreset) (gen : StdGen) : IO (BenchGroup × StdGen) := do
  let warmup := euclideanWarmupIterations preset
  let measured := euclideanMeasuredIterations preset
  let fastMeasured := euclideanFastMeasuredIterations preset
  let checksumIterations := groupChecksumIterations measured [
    measured, measured, fastMeasured, fastMeasured, fastMeasured
  ]
  let gcdRow ← runTimed
    (groupKey ++ "-gcd-monic") "CPolynomial" "gcdMonic"
    "KoalaBear.Field" inputShape preset warmup measured
    (fun _ ↦ CPolynomial.gcdMonic inputs.1 inputs.2)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let normRow ← runTimed
    (groupKey ++ "-norm-xgcd-fst") "CPolynomial" "normXgcd first component"
    "KoalaBear.Field" inputShape preset warmup measured
    (fun _ ↦ (CPolynomial.normXgcd inputs.1 inputs.2).1)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let xgcdRow ← runTimed
    (groupKey ++ "-xgcd-fst-normalized") "CPolynomial" "xgcd first component, normalized"
    "KoalaBear.Field" inputShape preset warmup measured
    (fun _ ↦ monicXgcdFst inputs.1 inputs.2)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let fastGcdRow ← runTimed
    (groupKey ++ "-gcd-monic-fast") "CPolynomial" "gcdMonic"
    "KoalaBear.Fast.Field" inputShape preset warmup fastMeasured
    (fun _ ↦ CPolynomial.gcdMonic fastInputs.1 fastInputs.2)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  let fastNormRow ← runTimed
    (groupKey ++ "-norm-xgcd-fst-fast") "CPolynomial" "normXgcd first component"
    "KoalaBear.Fast.Field" inputShape preset warmup fastMeasured
    (fun _ ↦ (CPolynomial.normXgcd fastInputs.1 fastInputs.2).1)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  let fastXgcdRow ← runTimed
    (groupKey ++ "-xgcd-fst-normalized-fast") "CPolynomial"
    "xgcd first component, normalized"
    "KoalaBear.Fast.Field" inputShape preset warmup fastMeasured
    (fun _ ↦ monicXgcdFst fastInputs.1 fastInputs.2)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := groupKey
    title := title
    records := #[gcdRow, normRow, xgcdRow, fastGcdRow, fastNormRow, fastXgcdRow]
  }, gen)

private def runSharedGcdKoala (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runGcdComparisonKoala "univariate-euclidean-gcd-koalabear"
    "Univariate Euclidean gcd, shared factor (KoalaBear)"
    sharedGcdShape sharedGcdInputs sharedGcdInputs preset gen

private def runCoprimeGcdKoala (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runGcdComparisonKoala "univariate-euclidean-gcd-coprime-koalabear"
    "Univariate Euclidean gcd, coprime (KoalaBear)"
    coprimeGcdShape coprimeGcdInputs coprimeGcdInputs preset gen

private def runUnevenGcdKoala (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  runGcdComparisonKoala "univariate-euclidean-gcd-uneven-koalabear"
    "Univariate Euclidean gcd, uneven degrees (KoalaBear)"
    unevenGcdShape unevenGcdInputs unevenGcdInputs preset gen

private def runPartialXgcdKoala (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let inputs : CPolynomial KoalaBear.Field × CPolynomial KoalaBear.Field := unevenGcdInputs
  let fastInputs : CPolynomial KoalaBear.Fast.Field × CPolynomial KoalaBear.Fast.Field :=
    unevenGcdInputs
  let warmup := euclideanWarmupIterations preset
  let measured := euclideanMeasuredIterations preset
  let fastMeasured := euclideanFastMeasuredIterations preset
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row ← runTimed
    "univariate-euclidean-partial-xgcd" "CPolynomial"
    "xgcd thresholded triple"
    "KoalaBear.Field" partialXgcdShape preset warmup measured
    (fun _ ↦ CPolynomial.xgcd inputs.1 inputs.2 gcdPartialThreshold)
    (checksumXgcdTriple checksumKoalaBear) checksumIterations
  let fastRow ← runTimed
    "univariate-euclidean-partial-xgcd-fast" "CPolynomial"
    "xgcd thresholded triple"
    "KoalaBear.Fast.Field" partialXgcdShape preset warmup fastMeasured
    (fun _ ↦ CPolynomial.xgcd fastInputs.1 fastInputs.2 gcdPartialThreshold)
    (checksumXgcdTriple checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "univariate-euclidean-partial-xgcd-koalabear"
    title := "Univariate partial xgcd (KoalaBear)"
    records := #[row, fastRow]
  }, gen)

/-- Benchmark group metadata for univariate Euclidean algorithms. -/
def univariateEuclideanAlgorithmGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-euclidean-gcd-koalabear",
    "Univariate Euclidean gcd, shared factor (KoalaBear)"⟩,
  ⟨"univariate-euclidean-gcd-coprime-koalabear",
    "Univariate Euclidean gcd, coprime (KoalaBear)"⟩,
  ⟨"univariate-euclidean-gcd-uneven-koalabear",
    "Univariate Euclidean gcd, uneven degrees (KoalaBear)"⟩,
  ⟨"univariate-euclidean-partial-xgcd-koalabear",
    "Univariate partial xgcd (KoalaBear)"⟩
]

/-- Runnable univariate Euclidean benchmark tasks. -/
def univariateEuclideanAlgorithmTasks : List BenchTask := [
  BenchTask.fromGroupRunner (univariateEuclideanAlgorithmGroupInfos.getD 0
    ⟨"univariate-euclidean-gcd-koalabear", ""⟩)
    runSharedGcdKoala,
  BenchTask.fromGroupRunner (univariateEuclideanAlgorithmGroupInfos.getD 1
    ⟨"univariate-euclidean-gcd-coprime-koalabear", ""⟩)
    runCoprimeGcdKoala,
  BenchTask.fromGroupRunner (univariateEuclideanAlgorithmGroupInfos.getD 2
    ⟨"univariate-euclidean-gcd-uneven-koalabear", ""⟩)
    runUnevenGcdKoala,
  BenchTask.fromGroupRunner (univariateEuclideanAlgorithmGroupInfos.getD 3
    ⟨"univariate-euclidean-partial-xgcd-koalabear", ""⟩)
    runPartialXgcdKoala
]

end CompPolyBench
