/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.GuruswamiSudan
import CompPoly.Bivariate.GuruswamiSudan.Implementations

/-!
# Guruswami-Sudan Received-Word Benchmarks

KoalaBear benchmarks for Guruswami-Sudan interpolation on perturbed received
words, where different interpolation backends may return different valid
witnesses.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

private def gsNonCodewordPointCount : Nat := 4

private def gsNonCodewordMessageDegree : Nat := 2

private def gsNonCodewordWeightedDegreeBound : Nat :=
  3

private def gsNonCodewordMultiplicity : Nat := 1

private def gsNonCodewordParams : GSInterpParams :=
  { messageDegree := gsNonCodewordMessageDegree
    multiplicity := gsNonCodewordMultiplicity
    weightedDegreeBound := gsNonCodewordWeightedDegreeBound }

private def gsStressPointCount : Nat := 128

private def gsStressMessageDegree : Nat := 33

private def gsStressWeightedDegreeBound : Nat := 160

private def gsStressMultiplicity : Nat := 2

private def gsStressParams : GSInterpParams :=
  { messageDegree := gsStressMessageDegree
    multiplicity := gsStressMultiplicity
    weightedDegreeBound := gsStressWeightedDegreeBound }

private def gsNonCodewordInputShape : String :=
  s!"n={gsNonCodewordPointCount},k={gsNonCodewordMessageDegree}," ++
    s!"m={gsNonCodewordMultiplicity},D={gsNonCodewordWeightedDegreeBound}," ++
    "errors=every2"

private def gsStressInputShape : String :=
  s!"n={gsStressPointCount},k={gsStressMessageDegree}," ++
    s!"m={gsStressMultiplicity},D={gsStressWeightedDegreeBound},errors=every7"

private def codewordPointsWithCount {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (pointCount : Nat) (p : CPolynomial F) : Array (Prod F F) :=
  (List.range pointCount).map
    (fun i ↦
      let x : F := (i + 1 : Nat)
      (x, CPolynomial.eval x p)) |>.toArray

private def perturbEveryNthY {F : Type*} [Add F] [OfNat F 1]
    (period : Nat) (points : Array (Prod F F)) : Array (Prod F F) :=
  if period == 0 then
    points
  else
    points.zipIdx.map fun pair ↦
      let point := pair.1
      let idx := pair.2
      if idx % period == 0 then
        (point.1, point.2 + 1)
      else
        point

private def checksumInterpolationValidityOption {F : Type*}
    [CommSemiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams)
    (Q? : Option (CBivariate F)) : Nat :=
  match Q? with
  | none => 0
  | some Q => if interpolationWitnessIsValidBool points params Q then 2 else 1

/-- Benchmark group metadata for received-word interpolation rows. -/
def guruswamiSudanReceivedWordGroupInfos : List BenchGroupInfo := [
  ⟨"guruswami-sudan-interp-noncodeword-small-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, smoke (KoalaBear)"⟩,
  ⟨"guruswami-sudan-interp-stress-koalabear",
    "Guruswami-Sudan interpolation on perturbed received word, stress (KoalaBear)"⟩
]

private def runGsInterpolationNonCodewordSmallKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsNonCodewordMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := perturbEveryNthY 2 (codewordPointsWithCount gsNonCodewordPointCount message)
  let fastPoints := perturbEveryNthY 2
    (codewordPointsWithCount gsNonCodewordPointCount fastMessage)
  let warmup := 0
  let leeDirectMeasured := preset.selectNat 20 3 1
  let leeSubproductMeasured := preset.selectNat 20 3 1
  let approximantDirectMeasured := preset.selectNat 1 1 1
  let approximantSubproductMeasured := preset.selectNat 1 1 1
  let fastLeeDirectMeasured := preset.selectNat 100 15 3
  let fastLeeSubproductMeasured := preset.selectNat 80 12 2
  let fastApproximantDirectMeasured := preset.selectNat 1 1 1
  let fastApproximantSubproductMeasured := preset.selectNat 1 1 1
  let checksumIterations := groupChecksumIterations leeDirectMeasured [
    leeSubproductMeasured, approximantDirectMeasured, approximantSubproductMeasured,
    fastLeeDirectMeasured, fastLeeSubproductMeasured, fastApproximantDirectMeasured,
    fastApproximantSubproductMeasured
  ]
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsNonCodewordInputShape preset warmup leeDirectMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsNonCodewordParams)
    (checksumInterpolationValidityOption points gsNonCodewordParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-noncodeword-small" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsNonCodewordInputShape preset warmup leeSubproductMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsNonCodewordParams)
    (checksumInterpolationValidityOption points gsNonCodewordParams)
    checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-noncodeword-small" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Field" gsNonCodewordInputShape preset warmup approximantDirectMeasured
    (fun _ ↦ koalaBearApproximantBasisDirectInterpContext.interpolate points
      gsNonCodewordParams)
    (checksumInterpolationValidityOption points gsNonCodewordParams)
    checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-noncodeword-small" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Field" gsNonCodewordInputShape preset warmup
    approximantSubproductMeasured
    (fun _ ↦ koalaBearApproximantBasisSubproductInterpContext.interpolate points
      gsNonCodewordParams)
    (checksumInterpolationValidityOption points gsNonCodewordParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsNonCodewordInputShape preset warmup
    fastLeeDirectMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints
      gsNonCodewordParams)
    (checksumInterpolationValidityOption fastPoints gsNonCodewordParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-noncodeword-small-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsNonCodewordInputShape preset warmup
    fastLeeSubproductMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsNonCodewordParams)
    (checksumInterpolationValidityOption fastPoints gsNonCodewordParams)
    checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-noncodeword-small-fast" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Fast.Field" gsNonCodewordInputShape preset warmup
    fastApproximantDirectMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisDirectInterpContext.interpolate fastPoints
      gsNonCodewordParams)
    (checksumInterpolationValidityOption fastPoints gsNonCodewordParams)
    checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-noncodeword-small-fast" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Fast.Field" gsNonCodewordInputShape preset warmup
    fastApproximantSubproductMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisSubproductInterpContext.interpolate
      fastPoints gsNonCodewordParams)
    (checksumInterpolationValidityOption fastPoints gsNonCodewordParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-noncodeword-small-koalabear",
    title := "Guruswami-Sudan interpolation on perturbed received word, smoke (KoalaBear)",
    records := #[
      leeDirectRow, leeSubproductRow, approximantDirectRow, approximantSubproductRow,
      fastLeeDirectRow, fastLeeSubproductRow, fastApproximantDirectRow,
      fastApproximantSubproductRow
    ]
  }, gen)

private def runGsInterpolationStressKoala (preset : BenchPreset) (gen : StdGen) :
    IO (Prod BenchGroup StdGen) := do
  let (coeffs, gen) := (koalaBearArray gsStressMessageDegree false).run gen
  let message := cpolyOfArray coeffs
  let fastMessage := cpolyOfArray (koalaBearFastArray coeffs)
  let points := perturbEveryNthY 7 (codewordPointsWithCount gsStressPointCount message)
  let fastPoints := perturbEveryNthY 7
    (codewordPointsWithCount gsStressPointCount fastMessage)
  let warmup := 0
  let leeMeasured := preset.selectNat 3 1 1
  let approximantMeasured := preset.selectNat 1 1 1
  let fastLeeMeasured := preset.selectNat 10 2 1
  let fastApproximantMeasured := preset.selectNat 1 1 1
  let checksumIterations := groupChecksumIterations leeMeasured [
    leeMeasured, approximantMeasured, approximantMeasured, fastLeeMeasured,
    fastLeeMeasured, fastApproximantMeasured, fastApproximantMeasured
  ]
  let leeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-stress" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Field" gsStressInputShape preset warmup leeMeasured
    (fun _ ↦ koalaBearLeeDirectInterpContext.interpolate points gsStressParams)
    (checksumInterpolationValidityOption points gsStressParams)
    checksumIterations
  let leeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-stress" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Field" gsStressInputShape preset warmup leeMeasured
    (fun _ ↦ koalaBearLeeSubproductInterpContext.interpolate points gsStressParams)
    (checksumInterpolationValidityOption points gsStressParams)
    checksumIterations
  let approximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-stress" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Field" gsStressInputShape preset warmup approximantMeasured
    (fun _ ↦ koalaBearApproximantBasisDirectInterpContext.interpolate points
      gsStressParams)
    (checksumInterpolationValidityOption points gsStressParams)
    checksumIterations
  let approximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-stress" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Field" gsStressInputShape preset warmup approximantMeasured
    (fun _ ↦ koalaBearApproximantBasisSubproductInterpContext.interpolate points
      gsStressParams)
    (checksumInterpolationValidityOption points gsStressParams)
    checksumIterations
  let fastLeeDirectRow <- runTimed
    "guruswami-sudan-interp-lee-direct-stress-fast" "CBivariate"
    "Lee-O'Sullivan direct"
    "KoalaBear.Fast.Field" gsStressInputShape preset warmup fastLeeMeasured
    (fun _ ↦ fastKoalaBearLeeDirectInterpContext.interpolate fastPoints
      gsStressParams)
    (checksumInterpolationValidityOption fastPoints gsStressParams)
    checksumIterations
  let fastLeeSubproductRow <- runTimed
    "guruswami-sudan-interp-lee-subproduct-stress-fast" "CBivariate"
    "Lee-O'Sullivan subproduct"
    "KoalaBear.Fast.Field" gsStressInputShape preset warmup fastLeeMeasured
    (fun _ ↦ fastKoalaBearLeeSubproductInterpContext.interpolate fastPoints
      gsStressParams)
    (checksumInterpolationValidityOption fastPoints gsStressParams)
    checksumIterations
  let fastApproximantDirectRow <- runTimed
    "guruswami-sudan-interp-approximant-direct-stress-fast" "CBivariate"
    "Approximant basis direct"
    "KoalaBear.Fast.Field" gsStressInputShape preset warmup fastApproximantMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisDirectInterpContext.interpolate fastPoints
      gsStressParams)
    (checksumInterpolationValidityOption fastPoints gsStressParams)
    checksumIterations
  let fastApproximantSubproductRow <- runTimed
    "guruswami-sudan-interp-approximant-subproduct-stress-fast" "CBivariate"
    "Approximant basis subproduct"
    "KoalaBear.Fast.Field" gsStressInputShape preset warmup fastApproximantMeasured
    (fun _ ↦ fastKoalaBearApproximantBasisSubproductInterpContext.interpolate
      fastPoints gsStressParams)
    (checksumInterpolationValidityOption fastPoints gsStressParams)
    checksumIterations
  pure ({
    groupKey := "guruswami-sudan-interp-stress-koalabear",
    title := "Guruswami-Sudan interpolation on perturbed received word, stress (KoalaBear)",
    records := #[
      leeDirectRow, leeSubproductRow, approximantDirectRow, approximantSubproductRow,
      fastLeeDirectRow, fastLeeSubproductRow, fastApproximantDirectRow,
      fastApproximantSubproductRow
    ]
  }, gen)

/-- Runnable received-word GS benchmark tasks. -/
def guruswamiSudanReceivedWordTasks : List BenchTask := [
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 0
    ⟨"guruswami-sudan-interp-noncodeword-small-koalabear", ""⟩)
    runGsInterpolationNonCodewordSmallKoala,
  BenchTask.fromGroupRunner (guruswamiSudanReceivedWordGroupInfos.getD 1
    ⟨"guruswami-sudan-interp-stress-koalabear", ""⟩)
    runGsInterpolationStressKoala
]

end CompPolyBench
