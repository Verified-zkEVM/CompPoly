/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear
import CompPoly.Univariate.EuclideanAlgorithm

/-!
# Finite-Field Root Benchmarks

Standalone nonlinear univariate root-finding benchmarks over canonical and fast
KoalaBear.
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

private def rootProductGcdMonicWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (p : CPolynomial F) : CPolynomial F :=
  let pMonic := CPolynomial.monicNormalize p
  let witness := CPolynomial.ofArray (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic.val)
  CPolynomial.gcdMonic pMonic witness

private def rootProductNormXgcdWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (p : CPolynomial F) : CPolynomial F :=
  let pMonic := CPolynomial.monicNormalize p
  let witness := CPolynomial.ofArray (CPolynomial.Raw.xPowSubXModWith M D ctx.q pMonic.val)
  (CPolynomial.normXgcd pMonic witness).1

/-- Benchmark group metadata for finite-field root finding. -/
def univariateFiniteFieldRootGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-roots-finite-field-koalabear",
    "Univariate finite-field root finding (KoalaBear)"⟩,
  ⟨"univariate-roots-root-product-gcd-koalabear",
    "Univariate finite-field root product gcd (KoalaBear)"⟩
]

private def runKoalaBearFiniteFieldRoots (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let p : CPolynomial KoalaBear.Field := nonlinearRootPolynomial
  let fastP : CPolynomial KoalaBear.Fast.Field := nonlinearRootPolynomial
  let warmup := preset.selectNat 1 0 0
  let measured := preset.selectNat 10 1 1
  let nttMeasured := preset.selectNat 10 1 1
  let nttFastMeasured := preset.selectNat 10 1 1
  let fastMeasured := preset.selectNat 30 3 1
  let fastNttMeasured := preset.selectNat 30 3 1
  let fastNttFastMeasured := preset.selectNat 30 3 1
  let checksumIterations := groupChecksumIterations measured [
    nttMeasured, nttFastMeasured, fastMeasured, fastNttMeasured, fastNttFastMeasured
  ]
  let row <- runTimed
    "univariate-roots-finite-field-naive" "CPolynomial"
    "Finite-field roots, canonical multiplication and remainder"
    "KoalaBear.Field" rootWorkloadShape preset warmup measured
    (fun _ ↦ koalaBearFieldRootContext.rootsInField p)
    (checksumArray checksumKoalaBear) checksumIterations
  let nttRow <- runTimed
    "univariate-roots-finite-field-ntt" "CPolynomial"
    "Finite-field roots, NTT multiplication and reversal remainder"
    "KoalaBear.Field" rootWorkloadShape preset warmup nttMeasured
    (fun _ ↦ koalaBearNttFieldRootContext.rootsInField p)
    (checksumArray checksumKoalaBear) checksumIterations
  let nttFastRow <- runTimed
    "univariate-roots-finite-field-nttfast" "CPolynomial"
    "Finite-field roots, NTTFast multiplication and reversal remainder"
    "KoalaBear.Field" rootWorkloadShape preset warmup nttFastMeasured
    (fun _ ↦ koalaBearNttFastFieldRootContext.rootsInField p)
    (checksumArray checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "univariate-roots-finite-field-fast-naive" "CPolynomial"
    "Finite-field roots, canonical multiplication and remainder"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastMeasured
    (fun _ ↦ fastKoalaBearFieldRootContext.rootsInField fastP)
    (checksumArray checksumKoalaBearFast) checksumIterations
  let fastNttRow <- runTimed
    "univariate-roots-finite-field-fast-ntt" "CPolynomial"
    "Finite-field roots, NTT multiplication and reversal remainder"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastNttMeasured
    (fun _ ↦ fastKoalaBearNttFieldRootContext.rootsInField fastP)
    (checksumArray checksumKoalaBearFast) checksumIterations
  let fastNttFastRow <- runTimed
    "univariate-roots-finite-field-fast-nttfast" "CPolynomial"
    "Finite-field roots, NTTFast multiplication and reversal remainder"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastNttFastMeasured
    (fun _ ↦ fastKoalaBearNttFastFieldRootContext.rootsInField fastP)
    (checksumArray checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "univariate-roots-finite-field-koalabear",
    title := "Univariate finite-field root finding (KoalaBear)",
    records := #[row, nttRow, nttFastRow, fastRow, fastNttRow, fastNttFastRow]
  }, gen)

private def runKoalaBearRootProductGcd (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let p : CPolynomial KoalaBear.Field := nonlinearRootPolynomial
  let fastP : CPolynomial KoalaBear.Fast.Field := nonlinearRootPolynomial
  let warmup := preset.selectNat 1 0 0
  let measured := preset.selectNat 10 1 1
  let fastMeasured := preset.selectNat 30 3 1
  let checksumIterations := groupChecksumIterations measured [
    measured, measured, fastMeasured, fastMeasured, fastMeasured
  ]
  let rawRow <- runTimed
    "univariate-roots-root-product-raw-gcd-monic" "CPolynomial.Raw"
    "root product, raw gcdMonic"
    "KoalaBear.Field" rootWorkloadShape preset warmup measured
    (fun _ ↦ CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      koalaBearFiniteFieldContext p.val)
    (checksumRawPolynomial checksumKoalaBear) checksumIterations
  let gcdRow <- runTimed
    "univariate-roots-root-product-gcd-monic" "CPolynomial"
    "root product, canonical gcdMonic"
    "KoalaBear.Field" rootWorkloadShape preset warmup measured
    (fun _ ↦ rootProductGcdMonicWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      koalaBearFiniteFieldContext p)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let normRow <- runTimed
    "univariate-roots-root-product-norm-xgcd" "CPolynomial"
    "root product, normXgcd first component"
    "KoalaBear.Field" rootWorkloadShape preset warmup measured
    (fun _ ↦ rootProductNormXgcdWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      koalaBearFiniteFieldContext p)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let fastRawRow <- runTimed
    "univariate-roots-root-product-fast-raw-gcd-monic" "CPolynomial.Raw"
    "root product, raw gcdMonic"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastMeasured
    (fun _ ↦ CPolynomial.Raw.Roots.FiniteField.finiteFieldRootProductWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      fastKoalaBearFiniteFieldContext fastP.val)
    (checksumRawPolynomial checksumKoalaBearFast) checksumIterations
  let fastGcdRow <- runTimed
    "univariate-roots-root-product-fast-gcd-monic" "CPolynomial"
    "root product, canonical gcdMonic"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastMeasured
    (fun _ ↦ rootProductGcdMonicWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      fastKoalaBearFiniteFieldContext fastP)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  let fastNormRow <- runTimed
    "univariate-roots-root-product-fast-norm-xgcd" "CPolynomial"
    "root product, normXgcd first component"
    "KoalaBear.Fast.Field" rootWorkloadShape preset warmup fastMeasured
    (fun _ ↦ rootProductNormXgcdWith
      CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
      fastKoalaBearFiniteFieldContext fastP)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "univariate-roots-root-product-gcd-koalabear",
    title := "Univariate finite-field root product gcd (KoalaBear)",
    records := #[rawRow, gcdRow, normRow, fastRawRow, fastGcdRow, fastNormRow]
  }, gen)

/-- Runnable finite-field root benchmark tasks. -/
def univariateFiniteFieldRootTasks : List BenchTask := [
  BenchTask.fromGroupRunner (univariateFiniteFieldRootGroupInfos.getD 0
    ⟨"univariate-roots-finite-field-koalabear", ""⟩)
    runKoalaBearFiniteFieldRoots,
  BenchTask.fromGroupRunner (univariateFiniteFieldRootGroupInfos.getD 1
    ⟨"univariate-roots-root-product-gcd-koalabear", ""⟩)
    runKoalaBearRootProductGcd
]

end CompPolyBench
