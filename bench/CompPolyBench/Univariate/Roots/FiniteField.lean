/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear

/-!
# Finite-Field Root Benchmarks

Standalone smooth-subgroup univariate root-search benchmarks over canonical and
fast KoalaBear.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

private def rootWorkloadRootCount : Nat := 64

private def rootWorkloadDegree : Nat := rootWorkloadRootCount + 2

private def rootWorkloadDistinctRoots : Nat := rootWorkloadRootCount + 1

private def rootWorkloadRootSeeds : List Nat :=
  [3, 3] ++ (List.range rootWorkloadRootCount).map (fun i ↦ i + 5)

private def rootWorkloadShape : String :=
  s!"degree={rootWorkloadDegree}, {rootWorkloadDistinctRoots} distinct roots, " ++
    "repeated root at 3"

private def productOfLinearRootSeeds {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (seeds : List Nat) : CPolynomial F :=
  seeds.foldl
    (fun p (seed : Nat) ↦ p * CPolynomial.linearFactor (seed : F))
    1

private def nonlinearRootPolynomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] : CPolynomial F :=
  productOfLinearRootSeeds rootWorkloadRootSeeds

private def insertSortedNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insertSortedNat x ys

private def sortNatList (xs : List Nat) : List Nat :=
  xs.foldr insertSortedNat []

private def checksumNatList (xs : List Nat) : Nat :=
  xs.foldl (fun acc x ↦ mixChecksum acc x) 0

private def checksumNormalizedRoots {F : Type*} (toNat : F → Nat) (roots : Array F) : Nat :=
  checksumNatList (sortNatList (roots.toList.map toNat))

/-- Benchmark group metadata for finite-field root search. -/
def univariateFiniteFieldRootGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-roots-finite-field-koalabear",
    "Univariate finite-field smooth-subgroup root search (KoalaBear)"⟩
]

private def runKoalaBearFiniteFieldRoots (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let p : CPolynomial KoalaBear.Field := nonlinearRootPolynomial
  let fastP : CPolynomial KoalaBear.Fast.Field := nonlinearRootPolynomial
  let warmup := preset.selectNat 1 0 0
  let measured := preset.selectNat 10 1 1
  let nttMeasured := preset.selectNat 40 6 1
  let nttFastMeasured := preset.selectNat 120 17 3
  let fastMeasured := preset.selectNat 60 9 2
  let fastNttMeasured := preset.selectNat 120 17 3
  let fastNttFastMeasured := preset.selectNat 400 60 12
  let checksumIterations := groupChecksumIterations measured [
    nttMeasured, nttFastMeasured, fastMeasured, fastNttMeasured, fastNttFastMeasured
  ]
  let row <- runTimed
    "univariate-roots-finite-field-naive" "CPolynomial"
    "smooth cyclic, canonical"
    "KoalaBear.Field" rootWorkloadShape preset warmup measured
    (fun _ ↦ koalaBearFieldRootContext.rootsInField p)
    (checksumNormalizedRoots checksumKoalaBear) checksumIterations
  let nttRow <- runTimed
    "univariate-roots-finite-field-ntt" "CPolynomial"
    "smooth cyclic, NTT"
    "KoalaBear.Field" rootWorkloadShape preset warmup nttMeasured
    (fun _ ↦ koalaBearNttFieldRootContext.rootsInField p)
    (checksumNormalizedRoots checksumKoalaBear) checksumIterations
  let nttFastRow <- runTimed
    "univariate-roots-finite-field-nttfast" "CPolynomial"
    "smooth cyclic, NTTFast"
    "KoalaBear.Field" rootWorkloadShape preset warmup nttFastMeasured
    (fun _ ↦ koalaBearNttFastFieldRootContext.rootsInField p)
    (checksumNormalizedRoots checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "univariate-roots-finite-field-fast-naive" "CPolynomial"
    "smooth cyclic, canonical"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastMeasured
    (fun _ ↦ fastKoalaBearFieldRootContext.rootsInField fastP)
    (checksumNormalizedRoots checksumKoalaBearFast) checksumIterations
  let fastNttRow <- runTimed
    "univariate-roots-finite-field-fast-ntt" "CPolynomial"
    "smooth cyclic, NTT"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastNttMeasured
    (fun _ ↦ fastKoalaBearNttFieldRootContext.rootsInField fastP)
    (checksumNormalizedRoots checksumKoalaBearFast) checksumIterations
  let fastNttFastRow <- runTimed
    "univariate-roots-finite-field-fast-nttfast" "CPolynomial"
    "smooth cyclic, NTTFast"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastNttFastMeasured
    (fun _ ↦ fastKoalaBearNttFastFieldRootContext.rootsInField fastP)
    (checksumNormalizedRoots checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "univariate-roots-finite-field-koalabear",
    title := "Univariate finite-field smooth-subgroup root search (KoalaBear)",
    records := #[row, nttRow, nttFastRow, fastRow, fastNttRow, fastNttFastRow]
  }, gen)

/-- Runnable finite-field root benchmark tasks. -/
def univariateFiniteFieldRootTasks : List BenchTask := [
  BenchTask.fromGroupRunner (univariateFiniteFieldRootGroupInfos.getD 0
    ⟨"univariate-roots-finite-field-koalabear", ""⟩)
    runKoalaBearFiniteFieldRoots
]

end CompPolyBench
