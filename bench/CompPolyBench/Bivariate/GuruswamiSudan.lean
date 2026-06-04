/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan
import CompPoly.Bivariate.GuruswamiSudan.Implementations
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for the dense interpolation path,
Koetter interpolation path, Roth-Ruckenstein root finding, and full
backend-parametric `gsCore` and `gsFilteredCore`.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

private def gsPointCount : Nat := 128

private def gsMessageDegree : Nat := 32

private def gsWeightedDegreeBound : Nat := 4 * (gsMessageDegree - 1)

private def gsMultiplicity : Nat := 4

private def gsCheckMultiplicity : Nat := 2

private def gsKoalaParams : GSInterpParams :=
  { messageDegree := gsMessageDegree
    multiplicity := gsMultiplicity
    weightedDegreeBound := gsWeightedDegreeBound }

private def gsSmallPointCount : Nat := 64

private def gsSmallMessageDegree : Nat := 16

private def gsSmallWeightedDegreeBound : Nat :=
  5 * (gsSmallMessageDegree - 1)

private def gsSmallMultiplicity : Nat := 2

private def gsSmallParams : GSInterpParams :=
  { messageDegree := gsSmallMessageDegree
    multiplicity := gsSmallMultiplicity
    weightedDegreeBound := gsSmallWeightedDegreeBound }

private def gsInputShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsMultiplicity},D={gsWeightedDegreeBound}"

private def gsSmallInputShape : String :=
  s!"n={gsSmallPointCount},k={gsSmallMessageDegree}," ++
    s!"m={gsSmallMultiplicity},D={gsSmallWeightedDegreeBound}"

private def gsMultiplicityShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsCheckMultiplicity},Q=(Y-p)^2"

private def gsRootShape : String :=
  s!"k={gsMessageDegree},Q=(Y-p)(Y-(p+7))"

private def gsFilteredShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsMultiplicity},r=0"

private def gsSmallFilteredShape : String :=
  s!"n={gsSmallPointCount},k={gsSmallMessageDegree},m={gsSmallMultiplicity},r=0"

private def codewordPointsWithCount {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (pointCount : Nat) (p : CPolynomial F) : Array (Prod F F) :=
  (List.range pointCount).map
    (fun i ↦
      let x : F := (i + 1 : Nat)
      (x, CPolynomial.eval x p)) |>.toArray

private def codewordPoints {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Array (Prod F F) :=
  codewordPointsWithCount gsPointCount p

private def rootBenchmarkQ {F : Type*}
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYDivisor p

private def multiplicityBenchmarkQ {F : Type*}
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
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
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYDivisor p * CBivariate.linearYDivisor (p + CPolynomial.C 7)

private def checksumDenseMatrix {F : Type*} [Zero F]
    (checksum : F -> Nat) (M : DenseMatrix F) : Nat :=
  mixChecksum (mixChecksum M.rows M.cols) (checksumArray checksum M.data)

private def checksumOptionArray {F : Type*} (checksum : F -> Nat)
    (v? : Option (Array F)) : Nat :=
  match v? with
  | none => 0
  | some v => mixChecksum 1 (checksumArray checksum v)

private def checksumInterpolationWitnessOption {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (checksum : F -> Nat) (points : Array (F × F)) (params : GSInterpParams)
    (Q? : Option (CBivariate F)) : Nat :=
  match Q? with
  | none => 0
  | some Q =>
      let validity := if interpolationWitnessIsValidBool points params Q then 1 else 0
      match normalizeVector? (interpolationCoefficientVector params Q) with
      | none => validity
      | some coeffs => mixChecksum validity (checksumArray checksum coeffs)

private def checksumPolynomialMatrix {F : Type*} [Zero F]
    (checksum : F -> Nat) (M : PolynomialMatrix F) : Nat :=
  checksumArray (fun row ↦ checksumArray (checksumCPolynomial checksum) row) M

private def checksumPolynomialArrayKoala (ps : Array (CPolynomial KoalaBear.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBear) ps

private def checksumPolynomialArrayKoalaFast
    (ps : Array (CPolynomial KoalaBear.Fast.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBearFast) ps

private def checksumBool (b : Bool) : Nat :=
  if b then 1 else 0

private def gsWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 0 0

/-
Preset iteration counts are fixed per benchmark row to keep total runtimes
comparable within each group across `small`, `medium`, and `large` runs.
-/
/-- Benchmark group metadata for Guruswami-Sudan cost-center rows. -/
def guruswamiSudanGroupInfos : List BenchGroupInfo := [
  ⟨"guruswami-sudan-interp-system-small-koalabear",
    "Guruswami-Sudan dense interpolation system construction, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-solve-small-koalabear",
    "Guruswami-Sudan dense interpolation solving, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-small-koalabear",
    "Guruswami-Sudan interpolation, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-large-koalabear",
    "Guruswami-Sudan interpolation, large (KoalaBear)"⟩,
  ⟨"guruswami-sudan-lee-setup-large-koalabear",
    "Guruswami-Sudan Lee-O'Sullivan setup, large (KoalaBear)"⟩,
  ⟨"guruswami-sudan-hasse-koalabear",
    "Guruswami-Sudan Hasse multiplicity checking (KoalaBear)"⟩,
  ⟨"guruswami-sudan-compose-koalabear",
    "Guruswami-Sudan composition in Y (KoalaBear)"⟩,
  ⟨"guruswami-sudan-root-roth-koalabear",
    "Guruswami-Sudan Roth-Ruckenstein roots (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-small-koalabear",
    "Guruswami-Sudan full core, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-large-koalabear",
    "Guruswami-Sudan full core, large (KoalaBear)"⟩,
  ⟨"guruswami-sudan-packed-filter-koalabear",
    "Guruswami-Sudan packed distance filtering (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-small-koalabear",
    "Guruswami-Sudan filtered core, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-large-koalabear",
    "Guruswami-Sudan filtered core, large (KoalaBear)"⟩
]

private def runGsInterpolationSystemKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPointsWithCount gsSmallPointCount message
  let fastPoints := codewordPointsWithCount gsSmallPointCount fastMessage
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 3 1 1
  let fastMeasured := preset.selectNat 10 2 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-system" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Field" gsSmallInputShape preset warmup measured
    (fun _ ↦ interpolationMatrix points gsSmallParams)
    (checksumDenseMatrix checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-system-fast" "DenseMatrix"
    "Interpolation system construction"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastMeasured
    (fun _ ↦ interpolationMatrix fastPoints gsSmallParams)
    (checksumDenseMatrix checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-system-small-koalabear",
    title := "Guruswami-Sudan dense interpolation system construction, small (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsInterpolationSolveKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPointsWithCount gsSmallPointCount message
  let fastPoints := codewordPointsWithCount gsSmallPointCount fastMessage
  let matrix := interpolationMatrix points gsSmallParams
  let fastMatrix := interpolationMatrix fastPoints gsSmallParams
  let kernelContext := denseLinearKernelContext KoalaBear.Field
  let fastKernelContext := denseLinearKernelContext KoalaBear.Fast.Field
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 1 1 1
  let fastMeasured := preset.selectNat 2 1 1
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let row <- runTimed
    "guruswami-sudan-interp-solve" "DenseMatrix" "Homogeneous interpolation solve"
    "KoalaBear.Field" gsSmallInputShape preset warmup measured
    (fun _ ↦ kernelContext.homogeneousWitness matrix)
    (checksumOptionArray checksumKoalaBear) checksumIterations
  let fastRow <- runTimed
    "guruswami-sudan-interp-solve-fast" "DenseMatrix"
    "Homogeneous interpolation solve"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastMeasured
    (fun _ ↦ fastKernelContext.homogeneousWitness fastMatrix)
    (checksumOptionArray checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-solve-small-koalabear",
    title := "Guruswami-Sudan dense interpolation solving, small (KoalaBear)",
    records := #[row, fastRow]
  }, gen)

private def runGsInterpolationSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPointsWithCount gsSmallPointCount message
  let fastPoints := codewordPointsWithCount gsSmallPointCount fastMessage
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let koetterMeasured := preset.selectNat 10 2 1
  let leeDirectMeasured := preset.selectNat 60 8 2
  let leeSubproductMeasured := preset.selectNat 50 7 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastKoetterMeasured := preset.selectNat 70 10 2
  let fastLeeDirectMeasured := preset.selectNat 400 60 10
  let fastLeeSubproductMeasured := preset.selectNat 300 40 10
  let checksumIterations := groupChecksumIterations denseMeasured [
    koetterMeasured, leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastKoetterMeasured, fastLeeDirectMeasured, fastLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-interp-dense-small" "CBivariate"
    "Dense linear"
    "KoalaBear.Field" gsSmallInputShape preset warmup denseMeasured
    (fun _ ↦ denseInterpolate points gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsSmallParams)
    checksumIterations
  let koetterRow <- runTimed
    "guruswami-sudan-interp-koetter-small" "CBivariate"
    "Koetter"
    "KoalaBear.Field" gsSmallInputShape preset warmup koetterMeasured
    (fun _ ↦ koetterInterpolate points gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsSmallParams)
    checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsSmallInputShape preset warmup leeDirectMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsSmallParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsSmallInputShape preset warmup leeSubproductMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsSmallParams)
    checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-interp-dense-small-fast" "CBivariate"
    "Dense linear"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastDenseMeasured
    (fun _ ↦ denseInterpolate fastPoints gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsSmallParams)
    checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-interp-koetter-small-fast" "CBivariate"
    "Koetter"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastKoetterMeasured
    (fun _ ↦ koetterInterpolate fastPoints gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsSmallParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastLeeDirectMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsSmallParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsSmallParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsSmallParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-small-koalabear",
    title := "Guruswami-Sudan interpolation, small (KoalaBear)",
    records := #[
      denseRow, koetterRow, leeDirectRow, leeSubproductRow,
      fastDenseRow, fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsInterpolationLargeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let warmup := gsWarmupIterations preset
  let koetterMeasured := preset.selectNat 1 1 1
  let leeMeasured := preset.selectNat 6 1 1
  let fastKoetterMeasured := preset.selectNat 3 1 1
  let fastLeeMeasured := preset.selectNat 25 4 1
  let checksumIterations := groupChecksumIterations koetterMeasured [
    leeMeasured, leeMeasured, fastKoetterMeasured, fastLeeMeasured, fastLeeMeasured
  ]
  let koetterRow <- runTimed
    "guruswami-sudan-interp-koetter" "CBivariate"
    "Koetter"
    "KoalaBear.Field" gsInputShape preset warmup koetterMeasured
    (fun _ ↦ koetterInterpolate points gsKoalaParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsKoalaParams)
    checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsInputShape preset warmup leeMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsKoalaParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsKoalaParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsInputShape preset warmup leeMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsKoalaParams)
    (checksumInterpolationWitnessOption checksumKoalaBear points gsKoalaParams)
    checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-interp-koetter-fast" "CBivariate"
    "Koetter"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastKoetterMeasured
    (fun _ ↦ koetterInterpolate fastPoints gsKoalaParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsKoalaParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastLeeMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints gsKoalaParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsKoalaParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastLeeMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints gsKoalaParams)
    (checksumInterpolationWitnessOption checksumKoalaBearFast fastPoints gsKoalaParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-large-koalabear",
    title := "Guruswami-Sudan interpolation, large (KoalaBear)",
    records := #[
      koetterRow, leeDirectRow, leeSubproductRow,
      fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsLeeSetupLargeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let directV : CPolynomial.VanishingPolynomialContext KoalaBear.Field :=
    CPolynomial.VanishingPolynomialContext.direct
  let subproductV : CPolynomial.VanishingPolynomialContext KoalaBear.Field :=
    CPolynomial.VanishingPolynomialContext.subproduct koalaBearNttFastMulContext
  let hornerE : CPolynomial.BatchEvalContext KoalaBear.Field :=
    CPolynomial.BatchEvalContext.horner KoalaBear.Field
  let subproductE : CPolynomial.BatchEvalContext KoalaBear.Field :=
    koalaBearNttFastBatchEvalContext
  let fastDirectV : CPolynomial.VanishingPolynomialContext KoalaBear.Fast.Field :=
    CPolynomial.VanishingPolynomialContext.direct
  let fastSubproductV : CPolynomial.VanishingPolynomialContext KoalaBear.Fast.Field :=
    CPolynomial.VanishingPolynomialContext.subproduct fastKoalaBearNttFastMulContext
  let fastHornerE : CPolynomial.BatchEvalContext KoalaBear.Fast.Field :=
    CPolynomial.BatchEvalContext.horner KoalaBear.Fast.Field
  let fastSubproductE : CPolynomial.BatchEvalContext KoalaBear.Fast.Field :=
    fastKoalaBearNttFastBatchEvalContext
  let warmup := gsWarmupIterations preset
  let measured := preset.selectNat 5 1 1
  let fastMeasured := preset.selectNat 25 4 1
  let checksumIterations := groupChecksumIterations measured [
    measured, fastMeasured, fastMeasured
  ]
  let directRow <- runTimed
    "guruswami-sudan-lee-setup-direct" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (direct vanishing)"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ ↦ leeOSullivanBasisRows directV hornerE points gsKoalaParams)
    (checksumPolynomialMatrix checksumKoalaBear) checksumIterations
  let subproductRow <- runTimed
    "guruswami-sudan-lee-setup-subproduct" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (subproduct vanishing)"
    "KoalaBear.Field" gsInputShape preset warmup measured
    (fun _ ↦ leeOSullivanBasisRows subproductV subproductE points gsKoalaParams)
    (checksumPolynomialMatrix checksumKoalaBear) checksumIterations
  let fastDirectRow <- runTimed
    "guruswami-sudan-lee-setup-direct-fast" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (direct vanishing)"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ ↦ leeOSullivanBasisRows fastDirectV fastHornerE fastPoints gsKoalaParams)
    (checksumPolynomialMatrix checksumKoalaBearFast) checksumIterations
  let fastSubproductRow <- runTimed
    "guruswami-sudan-lee-setup-subproduct-fast" "PolynomialMatrix"
    "Lee-O'Sullivan basis setup (subproduct vanishing)"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastMeasured
    (fun _ ↦ leeOSullivanBasisRows fastSubproductV fastSubproductE fastPoints gsKoalaParams)
    (checksumPolynomialMatrix checksumKoalaBearFast) checksumIterations
  pure ({
    groupKey := "guruswami-sudan-lee-setup-large-koalabear",
    title := "Guruswami-Sudan Lee-O'Sullivan setup, large (KoalaBear)",
    records := #[directRow, subproductRow, fastDirectRow, fastSubproductRow]
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
  let fastMeasured := preset.selectNat 500 70 15
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
  let fastMeasured := preset.selectNat 500 70 15
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
  let fastMeasured := preset.selectNat 80 10 2
  let fastNttFastMeasured := preset.selectNat 80 10 2
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

private def runGsCoreSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPointsWithCount gsSmallPointCount message
  let fastPoints := codewordPointsWithCount gsSmallPointCount fastMessage
  let rootContext := koalaBearRothRootContext
  let fastRootContext := fastKoalaBearRothRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let koetterMeasured := preset.selectNat 10 2 1
  let leeDirectMeasured := preset.selectNat 60 8 2
  let leeSubproductMeasured := preset.selectNat 50 7 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastKoetterMeasured := preset.selectNat 70 10 2
  let fastLeeDirectMeasured := preset.selectNat 400 60 10
  let fastLeeSubproductMeasured := preset.selectNat 300 40 10
  let checksumIterations := groupChecksumIterations denseMeasured [
    koetterMeasured, leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastKoetterMeasured, fastLeeDirectMeasured, fastLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-core-dense-small" "CBivariate"
    "Dense linear + roots"
    "KoalaBear.Field" gsSmallInputShape preset warmup denseMeasured
    (fun _ ↦ gsCore points (denseInterpContext KoalaBear.Field) rootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let koetterRow <- runTimed
    "guruswami-sudan-core-koetter-small" "CBivariate"
    "Koetter + roots"
    "KoalaBear.Field" gsSmallInputShape preset warmup koetterMeasured
    (fun _ ↦ gsCore points koalaBearKoetterInterpContext rootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct + roots"
    "KoalaBear.Field" gsSmallInputShape preset warmup leeDirectMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext rootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct + roots"
    "KoalaBear.Field" gsSmallInputShape preset warmup leeSubproductMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext rootContext gsSmallParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-core-dense-small-fast" "CBivariate"
    "Dense linear + roots"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastDenseMeasured
    (fun _ ↦
      gsCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRootContext
        gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-core-koetter-small-fast" "CBivariate"
    "Koetter + roots"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastKoetterMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearKoetterInterpContext fastRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + roots"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastLeeDirectMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + roots"
    "KoalaBear.Fast.Field" gsSmallInputShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦ gsCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRootContext
      gsSmallParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-small-koalabear",
    title := "Guruswami-Sudan full core, small (KoalaBear)",
    records := #[
      denseRow, koetterRow, leeDirectRow, leeSubproductRow,
      fastDenseRow, fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsCoreLargeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let rootContext := koalaBearRothRootContext
  let fastRootContext := fastKoalaBearRothRootContext
  let warmup := gsWarmupIterations preset
  let koetterMeasured := preset.selectNat 1 1 1
  let leeMeasured := preset.selectNat 8 1 1
  let fastKoetterMeasured := preset.selectNat 3 1 1
  let fastLeeMeasured := preset.selectNat 40 5 1
  let checksumIterations := groupChecksumIterations koetterMeasured [
    leeMeasured, leeMeasured, fastKoetterMeasured, fastLeeMeasured, fastLeeMeasured
  ]
  let koetterRow <- runTimed
    "guruswami-sudan-core-koetter-roth" "CBivariate"
    "Koetter + roots"
    "KoalaBear.Field" gsInputShape preset warmup koetterMeasured
    (fun _ ↦ gsCore points koalaBearKoetterInterpContext rootContext gsKoalaParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-roth" "CBivariate"
    "Lee-O'Sullivan direct + roots"
    "KoalaBear.Field" gsInputShape preset warmup leeMeasured
    (fun _ ↦ gsCore points koalaBearLeeDirectInterpContext rootContext gsKoalaParams)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-roth" "CBivariate"
    "Lee-O'Sullivan subproduct + roots"
    "KoalaBear.Field" gsInputShape preset warmup leeMeasured
    (fun _ ↦ gsCore points koalaBearLeeSubproductInterpContext rootContext gsKoalaParams)
    checksumPolynomialArrayKoala checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-core-koetter-roth-fast" "CBivariate"
    "Koetter + roots"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastKoetterMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearKoetterInterpContext fastRootContext
        gsKoalaParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-core-lee-direct-roth-fast" "CBivariate"
    "Lee-O'Sullivan direct + roots"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeDirectInterpContext fastRootContext
        gsKoalaParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-core-lee-subproduct-roth-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + roots"
    "KoalaBear.Fast.Field" gsInputShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRootContext
        gsKoalaParams)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-core-large-koalabear",
    title := "Guruswami-Sudan full core, large (KoalaBear)",
    records := #[
      koetterRow, leeDirectRow, leeSubproductRow,
      fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsFilteredCoreSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsSmallMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPointsWithCount gsSmallPointCount message
  let fastPoints := codewordPointsWithCount gsSmallPointCount fastMessage
  let rootContext := koalaBearRothRootContext
  let fastRootContext := fastKoalaBearRothRootContext
  let warmup := gsWarmupIterations preset
  let denseMeasured := preset.selectNat 1 1 1
  let koetterMeasured := preset.selectNat 10 2 1
  let leeDirectMeasured := preset.selectNat 60 8 2
  let leeSubproductMeasured := preset.selectNat 50 7 1
  let fastDenseMeasured := preset.selectNat 2 1 1
  let fastKoetterMeasured := preset.selectNat 70 10 2
  let fastLeeDirectMeasured := preset.selectNat 400 60 10
  let fastLeeSubproductMeasured := preset.selectNat 300 40 10
  let checksumIterations := groupChecksumIterations denseMeasured [
    koetterMeasured, leeDirectMeasured, leeSubproductMeasured, fastDenseMeasured,
    fastKoetterMeasured, fastLeeDirectMeasured, fastLeeSubproductMeasured
  ]
  let denseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small" "CBivariate"
    "Dense linear + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup denseMeasured
    (fun _ ↦
      gsFilteredCore points (denseInterpContext KoalaBear.Field) rootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let koetterRow <- runTimed
    "guruswami-sudan-filtered-core-koetter-small" "CBivariate"
    "Koetter + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup koetterMeasured
    (fun _ ↦ gsFilteredCore points koalaBearKoetterInterpContext rootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small" "CBivariate"
    "Lee-O'Sullivan direct + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup leeDirectMeasured
    (fun _ ↦ gsFilteredCore points koalaBearLeeDirectInterpContext rootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small" "CBivariate"
    "Lee-O'Sullivan subproduct + filter"
    "KoalaBear.Field" gsSmallFilteredShape preset warmup leeSubproductMeasured
    (fun _ ↦ gsFilteredCore points koalaBearLeeSubproductInterpContext rootContext
      gsSmallParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastDenseRow <- runTimed
    "guruswami-sudan-filtered-core-dense-small-fast" "CBivariate"
    "Dense linear + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastDenseMeasured
    (fun _ ↦
      gsFilteredCore fastPoints (denseInterpContext KoalaBear.Fast.Field) fastRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-filtered-core-koetter-small-fast" "CBivariate"
    "Koetter + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastKoetterMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearKoetterInterpContext fastRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-small-fast" "CBivariate"
    "Lee-O'Sullivan direct + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastLeeDirectMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext fastRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + filter"
    "KoalaBear.Fast.Field" gsSmallFilteredShape preset warmup fastLeeSubproductMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRootContext
        gsSmallParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-small-koalabear",
    title := "Guruswami-Sudan filtered core, small (KoalaBear)",
    records := #[
      denseRow, koetterRow, leeDirectRow, leeSubproductRow,
      fastDenseRow, fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
  }, gen)

private def runGsFilteredCoreLargeKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := codewordPoints message
  let fastPoints := codewordPoints fastMessage
  let rootContext := koalaBearRothRootContext
  let fastRootContext := fastKoalaBearRothRootContext
  let warmup := gsWarmupIterations preset
  let koetterMeasured := preset.selectNat 1 1 1
  let leeMeasured := preset.selectNat 8 1 1
  let fastKoetterMeasured := preset.selectNat 3 1 1
  let fastLeeMeasured := preset.selectNat 40 5 1
  let checksumIterations := groupChecksumIterations koetterMeasured [
    leeMeasured, leeMeasured, fastKoetterMeasured, fastLeeMeasured, fastLeeMeasured
  ]
  let koetterRow <- runTimed
    "guruswami-sudan-filtered-core-koetter" "CBivariate"
    "Koetter + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup koetterMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearKoetterInterpContext rootContext gsKoalaParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct" "CBivariate"
    "Lee-O'Sullivan direct + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup leeMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeDirectInterpContext rootContext gsKoalaParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct" "CBivariate"
    "Lee-O'Sullivan subproduct + filter"
    "KoalaBear.Field" gsFilteredShape preset warmup leeMeasured
    (fun _ ↦
      gsFilteredCore points koalaBearLeeSubproductInterpContext rootContext
        gsKoalaParams 0)
    checksumPolynomialArrayKoala checksumIterations
  let fastKoetterRow <- runTimed
    "guruswami-sudan-filtered-core-koetter-fast" "CBivariate"
    "Koetter + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastKoetterMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearKoetterInterpContext fastRootContext
        gsKoalaParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-filtered-core-lee-direct-fast" "CBivariate"
    "Lee-O'Sullivan direct + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeDirectInterpContext fastRootContext
        gsKoalaParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-filtered-core-lee-subproduct-fast" "CBivariate"
    "Lee-O'Sullivan subproduct + filter"
    "KoalaBear.Fast.Field" gsFilteredShape preset warmup fastLeeMeasured
    (fun _ ↦
      gsFilteredCore fastPoints fastKoalaBearLeeSubproductInterpContext fastRootContext
        gsKoalaParams 0)
    checksumPolynomialArrayKoalaFast checksumIterations
  pure ({
    groupKey := "guruswami-sudan-filtered-core-large-koalabear",
    title := "Guruswami-Sudan filtered core, large (KoalaBear)",
    records := #[
      koetterRow, leeDirectRow, leeSubproductRow,
      fastKoetterRow, fastLeeDirectRow, fastLeeSubproductRow
    ]
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
  let measured := preset.selectNat 20 3 1
  let fastMeasured := preset.selectNat 200 30 5
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
    ⟨"guruswami-sudan-interp-system-small-koalabear", ""⟩) runGsInterpolationSystemKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 1
    ⟨"guruswami-sudan-interp-solve-small-koalabear", ""⟩) runGsInterpolationSolveKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 2
    ⟨"guruswami-sudan-interp-small-koalabear", ""⟩) runGsInterpolationSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 3
    ⟨"guruswami-sudan-interp-large-koalabear", ""⟩) runGsInterpolationLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 4
    ⟨"guruswami-sudan-lee-setup-large-koalabear", ""⟩) runGsLeeSetupLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 5
    ⟨"guruswami-sudan-hasse-koalabear", ""⟩) runGsHasseKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 6
    ⟨"guruswami-sudan-compose-koalabear", ""⟩) runGsComposeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 7
    ⟨"guruswami-sudan-root-roth-koalabear", ""⟩) runGsRootKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 8
    ⟨"guruswami-sudan-core-small-koalabear", ""⟩) runGsCoreSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 9
    ⟨"guruswami-sudan-core-large-koalabear", ""⟩) runGsCoreLargeKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 10
    ⟨"guruswami-sudan-packed-filter-koalabear", ""⟩) runGsPackedFilterKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 11
    ⟨"guruswami-sudan-filtered-core-small-koalabear", ""⟩) runGsFilteredCoreSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanGroupInfos.getD 12
    ⟨"guruswami-sudan-filtered-core-large-koalabear", ""⟩) runGsFilteredCoreLargeKoala
]

end CompPolyBench
