/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for the dense interpolation baseline,
Roth-Ruckenstein root finding, and full backend-parametric `gsCore`.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

private def gsPointCount : Nat := 32

private def gsMessageDegree : Nat := 32

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

private def codewordPoints {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Array (Prod F F) :=
  (List.range gsPointCount).map
    (fun i =>
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

private def koalaFieldRoots : FieldRootBackend KoalaBear.Field :=
  linearFieldRootBackend KoalaBear.Field

private def koalaFastFieldRoots : FieldRootBackend KoalaBear.Fast.Field :=
  linearFieldRootBackend KoalaBear.Fast.Field

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
    "Guruswami-Sudan full core (KoalaBear)"⟩
]

private def runGsInterpolationSystemKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 70 10 2
  let fastMeasured := preset.selectNat 350 50 10
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-system" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ => interpolationMatrix points gsKoalaParams)
    (checksumDenseMatrix checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-system-fast" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ => interpolationMatrix fastPoints gsKoalaParams)
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
  let kernelBackend := denseLinearKernelBackend KoalaBear.Field
  let fastKernelBackend := denseLinearKernelBackend KoalaBear.Fast.Field
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 20 3 1
  let fastMeasured := preset.selectNat 140 20 4
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-solve" "DenseMatrix" "Homogeneous interpolation solve"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ => kernelBackend.homogeneousWitness matrix)
    (checksumOptionArray checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-solve-fast" "DenseMatrix"
    "Homogeneous interpolation solve"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ => fastKernelBackend.homogeneousWitness fastMatrix)
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
  let measured := preset.selectNat 200 30 5
  let fastMeasured := preset.selectNat 1400 200 40
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-hasse-check" "CBivariate" "Hasse multiplicity check"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ => CBivariate.satisfiesMultiplicityConstraintsBool Q points gsCheckMultiplicity)
    checksumBool checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-hasse-check-fast" "CBivariate" "Hasse multiplicity check"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ => CBivariate.satisfiesMultiplicityConstraintsBool fastQ fastPoints
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
  let measured := preset.selectNat 200 30 5
  let fastMeasured := preset.selectNat 1400 200 40
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-compose-y" "CPolynomial" "Composition in Y"
    "KoalaBear.Field" gsMultiplicityShape preset warmup measured
    (fun _ => CBivariate.composeY Q message)
    (checksumCPolynomial checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-compose-y-fast" "CPolynomial" "Composition in Y"
    "KoalaBear.Fast.Field" gsMultiplicityShape preset warmup fastMeasured
    (fun _ => CBivariate.composeY fastQ fastMessage)
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
  let Q := rootBenchmarkQ message
  let fastQ := rootBenchmarkQ fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 70 10 2
  let fastMeasured := preset.selectNat 490 70 14
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-root-roth" "CBivariate" "Roth-Ruckenstein root finding"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ => rothRuckensteinRootsYDegreeLt koalaFieldRoots Q gsMessageDegree)
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-root-roth-fast" "CBivariate" "Roth-Ruckenstein root finding"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ => rothRuckensteinRootsYDegreeLt koalaFastFieldRoots fastQ gsMessageDegree)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-root-roth-koalabear",
    title := "Guruswami-Sudan Roth-Ruckenstein roots (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsCoreKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let rootBackend := rothRuckensteinRootBackend KoalaBear.Field koalaFieldRoots
  let fastRootBackend := rothRuckensteinRootBackend KoalaBear.Fast.Field koalaFastFieldRoots
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 20 3 1
  let fastMeasured := preset.selectNat 140 20 4
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-core-dense-roth" "CBivariate" "Dense interpolation plus root finding"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ => gsCore points (denseInterpBackend KoalaBear.Field) rootBackend gsKoalaParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-core-dense-roth-fast" "CBivariate"
    "Dense interpolation plus root finding"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ => gsCore fastPoints (denseInterpBackend KoalaBear.Fast.Field) fastRootBackend
      gsKoalaParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-koalabear",
    title := "Guruswami-Sudan full core (KoalaBear)",
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
    ⟨"guruswami-sudan-core-koalabear", ""⟩) runGsCoreKoala
]

end CompPolyBench
