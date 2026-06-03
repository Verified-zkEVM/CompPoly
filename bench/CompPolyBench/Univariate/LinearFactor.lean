/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Univariate.Common
import CompPoly.Univariate.CoefficientInterpolation

/-!
# Univariate Linear-Factor Division Benchmarks

Compares the Lee-O'Sullivan coefficient-form synthetic quotient by `X - x`
with the generic monic-division quotient specialized to the same divisor.
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for univariate division by `X - x`. -/
def univariateLinearFactorGroupInfos : List BenchGroupInfo := [
  ⟨"univariate-divlinear-koalabear",
    "Univariate division by X - x (KoalaBear)"⟩
]

/-- Input shape for the univariate linear-factor quotient benchmark. -/
private def univariateLinearFactorShape : String :=
  "degree<128 dense dividend, divisor X - x"

/-- Run the univariate `divByLinearFactor` vs `divByMonic` comparison. -/
private def runKoalaBearUnivariateLinearFactor (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (coeffs, gen) := (koalaBearArray 128 false).run gen
  let (points, gen) := (koalaBearArray 16 false).run gen
  let poly : CPolynomial KoalaBear.Field := cpolyOfArray coeffs
  let fastPoly : CPolynomial KoalaBear.Fast.Field := cpolyOfArray (koalaBearFastArray coeffs)
  let fastPoints := koalaBearFastArray points
  let warmup := preset.selectNat 3 1 0
  let syntheticMeasured := preset.selectNat 1200 180 40
  let genericMeasured := preset.selectNat 20 3 1
  let fastSyntheticMeasured := preset.selectNat 1500 220 50
  let fastGenericMeasured := preset.selectNat 30 4 1
  let checksumIterations := groupChecksumIterations syntheticMeasured [
    genericMeasured, fastSyntheticMeasured, fastGenericMeasured
  ]
  let xAt (i : Nat) : KoalaBear.Field :=
    points.getD (i % points.size) 0
  let fastXAt (i : Nat) : KoalaBear.Fast.Field :=
    fastPoints.getD (i % fastPoints.size) 0
  let synthetic ← runTimed
    "univariate-deflate-linear-synthetic" "CPolynomial" "divByLinearFactor"
    "KoalaBear.Field" univariateLinearFactorShape preset warmup syntheticMeasured
    (fun i ↦ CPolynomial.divByLinearFactor poly (xAt i))
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let generic ← runTimed
    "univariate-deflate-linear-divbymonic" "CPolynomial" "divByMonic (X - x)"
    "KoalaBear.Field" univariateLinearFactorShape preset warmup genericMeasured
    (fun i ↦ CPolynomial.divByMonic poly (CPolynomial.linearFactor (xAt i)))
    (checksumCPolynomial checksumKoalaBear) (checksumIterations := checksumIterations)
  let fastSynthetic ← runTimed
    "univariate-deflate-linear-synthetic-fast" "CPolynomial" "divByLinearFactor"
    "KoalaBear.Fast.Field" univariateLinearFactorShape preset warmup fastSyntheticMeasured
    (fun i ↦ CPolynomial.divByLinearFactor fastPoly (fastXAt i))
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  let fastGeneric ← runTimed
    "univariate-deflate-linear-divbymonic-fast" "CPolynomial" "divByMonic (X - x)"
    "KoalaBear.Fast.Field" univariateLinearFactorShape preset warmup fastGenericMeasured
    (fun i ↦ CPolynomial.divByMonic fastPoly (CPolynomial.linearFactor (fastXAt i)))
    (checksumCPolynomial checksumKoalaBearFast) (checksumIterations := checksumIterations)
  pure ({
    groupKey := "univariate-divlinear-koalabear",
    title := "Univariate division by X - x (KoalaBear)",
    records := #[synthetic, generic, fastSynthetic, fastGeneric]
  }, gen)

/-- Runnable univariate linear-factor benchmark tasks. -/
def univariateLinearFactorTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"univariate-divlinear-koalabear",
      "Univariate division by X - x (KoalaBear)"⟩
    runKoalaBearUnivariateLinearFactor
]

end CompPolyBench
