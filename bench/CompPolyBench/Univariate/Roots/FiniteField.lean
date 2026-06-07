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

Standalone nonlinear univariate root-search benchmarks over canonical and fast
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

private def rootWorkloadLasVegasCutoff : Nat := 80

private def rootWorkloadLasVegasShape : String :=
  rootWorkloadShape ++ s!", Las Vegas cutoff={rootWorkloadLasVegasCutoff}"

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

private def seededLinearFactorProbeFamily {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (seed : Nat) :
    CPolynomial.Roots.FiniteField.ProbeFamily F where
  probe _q _factor attempt :=
    CPolynomial.linearFactor ((seed + attempt : Nat) : F)

private def lasVegasConfig (cutoff : Nat) :
    CPolynomial.Roots.FiniteField.LasVegasConfig where
  cutoff := cutoff
  tryOddRandomizedSplitting := true

private def lasVegasRootsWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : CPolynomial.Roots.FiniteField.FiniteFieldContext F)
    (enumeration : CPolynomial.Roots.FiniteField.FieldEnumeration F)
    (cfg : CPolynomial.Roots.FiniteField.LasVegasConfig)
    (probes : CPolynomial.Roots.FiniteField.ProbeFamily F)
    (p : CPolynomial F) : Array F :=
  CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith M D ctx
    (CPolynomial.Roots.FiniteField.lasVegasLinearFactorProductSplitterWith
      M D ctx enumeration cfg probes)
    p

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

/-- Benchmark group metadata for finite-field root search. -/
def univariateFiniteFieldRootGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-roots-finite-field-koalabear",
    "Univariate finite-field root search (KoalaBear)"⟩,
  ⟨"univariate-roots-root-product-gcd-koalabear",
    "Univariate finite-field root product gcd (KoalaBear)"⟩,
]

private def runKoalaBearFiniteFieldRoots (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let p : CPolynomial KoalaBear.Field := nonlinearRootPolynomial
  let fastP : CPolynomial KoalaBear.Fast.Field := nonlinearRootPolynomial
  let warmup := preset.selectNat 1 0 0
  -- Large counts balance row totals; medium is about large / 7, small about
  -- max (large / 35) 1, with rounded nice values.
  let measured := preset.selectNat 10 1 1
  let nttMeasured := preset.selectNat 40 6 1
  let nttFastMeasured := preset.selectNat 120 17 3
  let fastMeasured := preset.selectNat 60 9 2
  let fastNttMeasured := preset.selectNat 120 17 3
  let fastNttFastMeasured := preset.selectNat 400 60 12
  let lvMeasured := preset.selectNat 10 1 1
  let lvNttMeasured := preset.selectNat 15 2 1
  let lvNttFastMeasured := preset.selectNat 40 6 1
  let fastLvMeasured := preset.selectNat 40 6 1
  let fastLvNttMeasured := preset.selectNat 45 6 1
  let fastLvNttFastMeasured := preset.selectNat 120 17 3
  let checksumIterations := groupChecksumIterations measured [
    nttMeasured, nttFastMeasured, fastMeasured, fastNttMeasured, fastNttFastMeasured,
    lvMeasured, lvNttMeasured, lvNttFastMeasured,
    fastLvMeasured, fastLvNttMeasured, fastLvNttFastMeasured
  ]
  let lvCfg := lasVegasConfig rootWorkloadLasVegasCutoff
  let lvProbes := seededLinearFactorProbeFamily (F := KoalaBear.Field) 3
  let fastLvProbes := seededLinearFactorProbeFamily (F := KoalaBear.Fast.Field) 3
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
  let lvRow <- runTimed
    "univariate-roots-finite-field-las-vegas-naive" "CPolynomial"
    "Las Vegas, canonical"
    "KoalaBear.Field" rootWorkloadLasVegasShape preset warmup lvMeasured
    (fun _ ↦ lasVegasRootsWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive koalaBearFiniteFieldContext
      koalaBearFieldEnumeration lvCfg lvProbes p)
    (checksumNormalizedRoots checksumKoalaBear) checksumIterations
  let lvNttRow <- runTimed
    "univariate-roots-finite-field-las-vegas-ntt" "CPolynomial"
    "Las Vegas, NTT"
    "KoalaBear.Field" rootWorkloadLasVegasShape preset warmup lvNttMeasured
    (fun _ ↦ lasVegasRootsWith
      (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
      (CPolynomial.Raw.ModContext.reversalNtt CPolynomial.NTT.KoalaBear.bestDomainForLength?)
      koalaBearFiniteFieldContext koalaBearFieldEnumeration lvCfg lvProbes p)
    (checksumNormalizedRoots checksumKoalaBear) checksumIterations
  let lvNttFastRow <- runTimed
    "univariate-roots-finite-field-las-vegas-nttfast" "CPolynomial"
    "Las Vegas, NTTFast"
    "KoalaBear.Field" rootWorkloadLasVegasShape preset warmup lvNttFastMeasured
    (fun _ ↦ lasVegasRootsWith
      (CPolynomial.Raw.MulContext.nttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?)
      (CPolynomial.Raw.ModContext.reversalNttFast
        CPolynomial.NTT.KoalaBear.bestDomainForLength?)
      koalaBearFiniteFieldContext koalaBearFieldEnumeration lvCfg lvProbes p)
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
  let fastLvRow <- runTimed
    "univariate-roots-finite-field-fast-las-vegas-naive" "CPolynomial"
    "Las Vegas, canonical"
    "KoalaBear.Fast.Field" rootWorkloadLasVegasShape preset warmup fastLvMeasured
    (fun _ ↦ lasVegasRootsWith CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive fastKoalaBearFiniteFieldContext
      fastKoalaBearFieldEnumeration lvCfg fastLvProbes fastP)
    (checksumNormalizedRoots checksumKoalaBearFast) checksumIterations
  let fastLvNttRow <- runTimed
    "univariate-roots-finite-field-fast-las-vegas-ntt" "CPolynomial"
    "Las Vegas, NTT"
    "KoalaBear.Fast.Field" rootWorkloadLasVegasShape preset warmup fastLvNttMeasured
    (fun _ ↦ lasVegasRootsWith
      (CPolynomial.Raw.MulContext.ntt CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
      (CPolynomial.Raw.ModContext.reversalNtt
        CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
      fastKoalaBearFiniteFieldContext fastKoalaBearFieldEnumeration
      lvCfg fastLvProbes fastP)
    (checksumNormalizedRoots checksumKoalaBearFast) checksumIterations
  let fastLvNttFastRow <- runTimed
    "univariate-roots-finite-field-fast-las-vegas-nttfast" "CPolynomial"
    "Las Vegas, NTTFast"
    "KoalaBear.Fast.Field" rootWorkloadLasVegasShape preset warmup fastLvNttFastMeasured
    (fun _ ↦ lasVegasRootsWith
      (CPolynomial.Raw.MulContext.nttFast
        CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
      (CPolynomial.Raw.ModContext.reversalNttFast
        CPolynomial.NTT.KoalaBear.fastBestDomainForLength?)
      fastKoalaBearFiniteFieldContext fastKoalaBearFieldEnumeration
      lvCfg fastLvProbes fastP)
    (checksumNormalizedRoots checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "univariate-roots-finite-field-koalabear",
    title := "Univariate finite-field root search (KoalaBear)",
    records := #[
      row, nttRow, nttFastRow, lvRow, lvNttRow, lvNttFastRow,
      fastRow, fastNttRow, fastNttFastRow, fastLvRow, fastLvNttRow,
      fastLvNttFastRow
    ]
  }, gen)

private def runKoalaBearRootProductGcd (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let p : CPolynomial KoalaBear.Field := nonlinearRootPolynomial
  let fastP : CPolynomial KoalaBear.Fast.Field := nonlinearRootPolynomial
  let warmup := preset.selectNat 1 0 0
  -- Large counts balance row totals; medium is about large / 7, small about
  -- max (large / 35) 1, with rounded nice values.
  let measured := preset.selectNat 10 1 1
  let fastMeasured := preset.selectNat 50 7 1
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
