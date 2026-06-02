/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan
import CompPoly.Bivariate.GuruswamiSudan.Implementations
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for the dense interpolation path,
Roth-Ruckenstein root finding, and full backend-parametric `gsCore` and
`gsFilteredCore`.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

private def gsPointCount : Nat := 96

private def gsMessageDegree : Nat := 96

private def gsWeightedDegreeBound : Nat := gsMessageDegree - 1

private def gsMultiplicity : Nat := 1

private def gsCheckMultiplicity : Nat := 2

private def gsKoalaParams : GSInterpParams :=
  { messageDegree := gsMessageDegree
    multiplicity := gsMultiplicity
    weightedDegreeBound := gsWeightedDegreeBound }

private def gsInputShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsMultiplicity},D={gsWeightedDegreeBound}"

private def gsMultiplicityShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsCheckMultiplicity},Q=(Y-p)^2"

private def gsRootShape : String :=
  s!"k={gsMessageDegree},Q=(Y-p)(Y-(p+7))"

private def gsFilteredShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsMultiplicity},r=0"

private def codewordPoints {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Array (Prod F F) :=
  (List.range gsPointCount).map
    (fun i ↦
      let x : F := (i + 1 : Nat)
      (x, CPolynomial.eval x p)) |>.toArray

private def rootBenchmarkQ {F : Type*}
    [Ring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYFactor p

private def multiplicityBenchmarkQ {F : Type*}
    [Ring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  let Q := rootBenchmarkQ p
  Q * Q

private def koalaFieldRoots : FieldRootContext KoalaBear.Field :=
  koalaBearFieldRootContext

private def koalaFieldRootsFast : FieldRootContext KoalaBear.Field :=
  koalaBearNttFastFieldRootContext

private def koalaFastFieldRoots : FieldRootContext KoalaBear.Fast.Field :=
  fastKoalaBearFieldRootContext

private def koalaFastFieldRootsFast : FieldRootContext KoalaBear.Fast.Field :=
  fastKoalaBearNttFastFieldRootContext

private def nonlinearRootBenchmarkQ {F : Type*}
    [Ring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYFactor p * CBivariate.linearYFactor (p + CPolynomial.C 7)

private def checksumDenseMatrix {F : Type*} [Zero F]
    (checksum : F -> Nat) (M : DenseMatrix F) : Nat :=
  mixChecksum (mixChecksum M.rows M.cols) (checksumArray checksum M.data)

private def checksumOptionArray {F : Type*} (checksum : F -> Nat)
    (v? : Option (Array F)) : Nat :=
  match v? with
  | none => 0
  | some v => mixChecksum 1 (checksumArray checksum v)

private def checksumPolynomialArrayKoala (ps : Array (CPolynomial KoalaBear.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBear) ps

private def checksumPolynomialArrayKoalaFast
    (ps : Array (CPolynomial KoalaBear.Fast.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBearFast) ps

private def checksumBool (b : Bool) : Nat :=
  if b then 1 else 0

private def gsWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 10 1 0

/-- Benchmark group metadata for Guruswami-Sudan cost-center rows. -/
def guruswamiSudanGroupInfos : List BenchGroupInfo := [
  ⟨"guruswami-sudan-interp-system-koalabear",
    "Guruswami-Sudan interpolation system construction (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-solve-koalabear",
    "Guruswami-Sudan interpolation solving (KoalaBear)"⟩,
  ⟨"guruswami-sudan-hasse-koalabear",
    "Guruswami-Sudan Hasse multiplicity checking (KoalaBear)"⟩,
  ⟨"guruswami-sudan-compose-koalabear",
    "Guruswami-Sudan composition in Y (KoalaBear)"⟩,
  ⟨"guruswami-sudan-root-roth-koalabear",
    "Guruswami-Sudan Roth-Ruckenstein roots (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-koalabear",
    "Guruswami-Sudan full core (KoalaBear)"⟩,
  ⟨"guruswami-sudan-packed-filter-koalabear",
    "Guruswami-Sudan packed distance filtering (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-koalabear",
    "Guruswami-Sudan filtered core (KoalaBear)"⟩
]

private def runGsInterpolationSystemKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 30 3 1
  let fastMeasured := preset.selectNat 150 15 5
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-system" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ ↦ interpolationMatrix points gsKoalaParams)
    (checksumDenseMatrix checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-system-fast" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ ↦ interpolationMatrix fastPoints gsKoalaParams)
    (checksumDenseMatrix checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-system-koalabear",
    title := "Guruswami-Sudan interpolation system construction (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsInterpolationSolveKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let matrix := interpolationMatrix (codewordPoints message) gsKoalaParams
  let fastMatrix := interpolationMatrix (codewordPoints fastMessage) gsKoalaParams
  let kernelContext := denseLinearKernelContext KoalaBear.Field
  let fastKernelContext := denseLinearKernelContext KoalaBear.Fast.Field
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 10 1 1
  let fastMeasured := preset.selectNat 50 5 2
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-solve" "DenseMatrix" "Homogeneous interpolation solve"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ ↦ kernelContext.homogeneousWitness matrix)
    (checksumOptionArray checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-solve-fast" "DenseMatrix"
    "Homogeneous interpolation solve"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ ↦ fastKernelContext.homogeneousWitness fastMatrix)
    (checksumOptionArray checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-solve-koalabear",
    title := "Guruswami-Sudan interpolation solving (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsHasseKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let Q := multiplicityBenchmarkQ message
  let fastQ := multiplicityBenchmarkQ fastMessage
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 80 10 2
  let fastMeasured := preset.selectNat 500 50 10
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-hasse-check" "CBivariate" "Hasse multiplicity check"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ ↦ CBivariate.satisfiesMultiplicityConstraintsBool Q points gsCheckMultiplicity)
    checksumBool checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-hasse-check-fast" "CBivariate" "Hasse multiplicity check"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ ↦ CBivariate.satisfiesMultiplicityConstraintsBool fastQ fastPoints
      gsCheckMultiplicity)
    checksumBool checksumIterations
  pure ({
    groupKey := "guruswami-sudan-hasse-koalabear",
    title := "Guruswami-Sudan Hasse multiplicity checking (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsComposeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let Q := multiplicityBenchmarkQ message
  let fastQ := multiplicityBenchmarkQ fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 80 10 2
  let fastMeasured := preset.selectNat 500 50 10
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-compose-y" "CPolynomial" "Composition in Y"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ ↦ CBivariate.composeY Q message)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-compose-y-fast" "CPolynomial" "Composition in Y"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ ↦ CBivariate.composeY fastQ fastMessage)
    (checksumCPolynomial checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-compose-koalabear",
    title := "Guruswami-Sudan composition in Y (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsRootKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let Q := nonlinearRootBenchmarkQ message
  let fastQ := nonlinearRootBenchmarkQ fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 20 3 1
  let nttFastMeasured := preset.selectNat 20 3 1
  let fastMeasured := preset.selectNat 120 20 5
  let fastNttFastMeasured := preset.selectNat 120 20 5
  let checksumIterations := groupChecksumIterations measured [
    nttFastMeasured, fastMeasured, fastNttFastMeasured
  ]
  let row <- runTimed
    "guruswami-sudan-root-roth" "CBivariate"
    "Roth-Ruckenstein root finding with nonlinear field-root equations"
    "KoalaBear.Field" gsRootShape preset warmup measured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFieldRoots Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let nttFastRow <- runTimed
    "guruswami-sudan-root-roth-nttfast" "CBivariate"
    "Roth-Ruckenstein root finding with NTTFast field-root equations"
    "KoalaBear.Field" gsRootShape preset warmup nttFastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFieldRootsFast Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-root-roth-fast" "CBivariate"
    "Roth-Ruckenstein root finding with nonlinear field-root equations"
    "KoalaBear.Fast.Field" gsRootShape preset warmup fastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFastFieldRoots fastQ gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastNttFastRow <- runTimed
    "guruswami-sudan-root-roth-fast-nttfast" "CBivariate"
    "Roth-Ruckenstein root finding with NTTFast field-root equations"
    "KoalaBear.Fast.Field" gsRootShape preset warmup fastNttFastMeasured
    (fun _ ↦ rothRuckensteinRootsYDegreeLt koalaFastFieldRootsFast fastQ
      gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-root-roth-koalabear",
    title := "Guruswami-Sudan Roth-Ruckenstein roots (KoalaBear)",
    records := #[row, nttFastRow, fastRow, fastNttFastRow]
  }, gen)

private def runGsCoreKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let rootContext := koalaBearRothRootContext
  let rootContextFast := koalaBearRothNttFastRootContext
  let fastRootContext := fastKoalaBearRothRootContext
  let fastRootContextFast := fastKoalaBearRothNttFastRootContext
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 8 1 1
  let nttFastMeasured := preset.selectNat 8 1 1
  let fastMeasured := preset.selectNat 40 5 2
  let fastNttFastMeasured := preset.selectNat 40 5 2
  let checksumIterations := groupChecksumIterations measured [
    nttFastMeasured, fastMeasured, fastNttFastMeasured
  ]
  let row <- runTimed
    "guruswami-sudan-core-dense-roth" "CBivariate" "Dense interpolation plus root finding"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ ↦ gsCore points (denseInterpContext KoalaBear.Field) rootContext gsKoalaParams)
    checksumPolynomialArrayKoala checksumIterations
  let nttFastRow <- runTimed
    "guruswami-sudan-core-dense-roth-nttfast" "CBivariate"
    "Dense interpolation plus NTTFast field-root finding"
    "KoalaBear.Field" gsInputShape preset warmup nttFastMeasured
    (fun _ ↦
      gsCore points (denseInterpContext KoalaBear.Field) rootContextFast gsKoalaParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-core-dense-roth-fast" "CBivariate"
    "Dense interpolation plus root finding"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ ↦ gsCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRootContext
      gsKoalaParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastNttFastRow <- runTimed
    "guruswami-sudan-core-dense-roth-fast-nttfast" "CBivariate"
    "Dense interpolation plus root finding (fast mul/mod, fast KoalaBear)"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastNttFastMeasured
    (fun _ ↦
      gsCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRootContextFast
        gsKoalaParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-koalabear",
    title := "Guruswami-Sudan full core (KoalaBear)",
    records := #[row, nttFastRow, fastRow, fastNttFastRow]
  }, gen)

private def runGsFilteredCoreKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let rootContext := koalaBearRothRootContext
  let rootContextFast := koalaBearRothNttFastRootContext
  let fastRootContext := fastKoalaBearRothRootContext
  let fastRootContextFast := fastKoalaBearRothNttFastRootContext
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 8 1 1
  let nttFastMeasured := preset.selectNat 8 1 1
  let fastMeasured := preset.selectNat 40 5 2
  let fastNttFastMeasured := preset.selectNat 40 5 2
  let checksumIterations := groupChecksumIterations measured [
    nttFastMeasured, fastMeasured, fastNttFastMeasured
  ]
  let row <- runTimed
    "guruswami-sudan-filtered-core" "CBivariate"
    "Packed filtered core"
    "KoalaBear.Field" gsFilteredShape preset warmup measured
    (fun _ ↦
      gsFilteredCore points (denseInterpContext KoalaBear.Field) rootContext gsKoalaParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let nttFastRow <- runTimed
    "guruswami-sudan-filtered-core-nttfast" "CBivariate"
    "Packed filtered core (fast mul/mod)"
    "KoalaBear.Field" gsFilteredShape preset warmup nttFastMeasured
    (fun _ ↦
      gsFilteredCore points (denseInterpContext KoalaBear.Field) rootContextFast
        gsKoalaParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-filtered-core-fast" "CBivariate"
    "Packed filtered core"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastMeasured
    (fun _ ↦
      gsFilteredCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRootContext
        gsKoalaParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastNttFastRow <- runTimed
    "guruswami-sudan-filtered-core-fast-nttfast" "CBivariate"
    "Packed filtered core (fast mul/mod, fast KoalaBear)"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastNttFastMeasured
    (fun _ ↦
      gsFilteredCore fastPoints (denseInterpContext KoalaBear.Fast.Field)
        fastRootContextFast gsKoalaParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-koalabear",
    title := "Guruswami-Sudan filtered core (KoalaBear)",
    records := #[row, nttFastRow, fastRow, fastNttFastRow]
  }, gen)

private def runGsPackedFilterKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let radius : Nat := 0
  let candidateCount := preset.selectNat 128 64 32
  let inputShape := s!"n={gsPointCount},k={gsMessageDegree},cand={candidateCount},r={radius}"
  let candidates : Array (CPolynomial KoalaBear.Field) :=
    (List.range candidateCount).map (fun i ↦
      message + CPolynomial.C ((i + 1 : Nat) : KoalaBear.Field)) |>.toArray
  let fastCandidates : Array (CPolynomial KoalaBear.Fast.Field) :=
    (List.range candidateCount).map (fun i ↦
      fastMessage + CPolynomial.C ((i + 1 : Nat) : KoalaBear.Fast.Field)) |>.toArray
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 80 20 5
  let fastMeasured := preset.selectNat 200 50 10
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-packed-filter" "CPolynomial"
    "Packed distance filtering"
    "KoalaBear.Field" inputShape preset warmup measured
    (fun _ ↦ candidates.filter (passesCandidateDistance points radius))
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-packed-filter-fast" "CPolynomial"
    "Packed distance filtering"
    "KoalaBear.Fast.Field" inputShape preset warmup fastMeasured
    (fun _ ↦ fastCandidates.filter (passesCandidateDistance fastPoints radius))
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-packed-filter-koalabear",
    title := "Guruswami-Sudan packed distance filtering (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

/-- Runnable GS benchmark tasks. -/
def guruswamiSudanTasks : List BenchTask := [
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 0
    ⟨"guruswami-sudan-interp-system-koalabear", ""⟩) runGsInterpolationSystemKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 1
    ⟨"guruswami-sudan-interp-solve-koalabear", ""⟩) runGsInterpolationSolveKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 2
    ⟨"guruswami-sudan-hasse-koalabear", ""⟩) runGsHasseKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 3
    ⟨"guruswami-sudan-compose-koalabear", ""⟩) runGsComposeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 4
    ⟨"guruswami-sudan-root-roth-koalabear", ""⟩) runGsRootKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 5
    ⟨"guruswami-sudan-core-koalabear", ""⟩) runGsCoreKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 6
    ⟨"guruswami-sudan-packed-filter-koalabear", ""⟩) runGsPackedFilterKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 7
    ⟨"guruswami-sudan-filtered-core-koalabear", ""⟩) runGsFilteredCoreKoala
]

end CompPolyBench
