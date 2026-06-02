/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPolyBench.Common
import CompPoly.Bivariate.Factor
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.Fields.BN254

/-!
# Bivariate Linear-Division Benchmarks

Compares two ways to divide a bivariate polynomial `Q` by the linear factor
`Y - f` in the `Y` variable:

* `divByLinearY`: the bespoke synthetic (Horner) division specialised to a monic
  linear divisor; and
* `CPolynomial.divByMonic`: general monic long division (now `CommRing`-general)
  applied to the divisor `Y - f`.

Measured across three fields of different word sizes (KoalaBear 31-bit,
Goldilocks 64-bit, BN254 254-bit) and three `Y`-degree sizes (`< 8`, `< 16`,
`< 32`), to show both that the Horner speedup is field-independent and that it
*grows* with the `Y`-degree (the generic divider does a full polynomial multiply
per step, whose cost balloons as the quotient's `X`-degree grows).

Both methods produce the same quotient, verified by an identical checksum within
each (field, size) group. The divisor's constant term is perturbed per iteration
so the division is genuinely recomputed (not hoisted) each measured call.
-/

open CompPoly

namespace CompPolyBench

/-- Benchmark group metadata for bivariate linear division (3 fields × 3 sizes). -/
def factorGroupInfos : List BenchGroupInfo := [
  ⟨"bivariate-divlinear-koalabear-y8", "Bivariate division by Y - f (KoalaBear, yDeg<8)"⟩,
  ⟨"bivariate-divlinear-koalabear-y16", "Bivariate division by Y - f (KoalaBear, yDeg<16)"⟩,
  ⟨"bivariate-divlinear-koalabear-y32", "Bivariate division by Y - f (KoalaBear, yDeg<32)"⟩,
  ⟨"bivariate-divlinear-goldilocks-y8", "Bivariate division by Y - f (Goldilocks, yDeg<8)"⟩,
  ⟨"bivariate-divlinear-goldilocks-y16", "Bivariate division by Y - f (Goldilocks, yDeg<16)"⟩,
  ⟨"bivariate-divlinear-goldilocks-y32", "Bivariate division by Y - f (Goldilocks, yDeg<32)"⟩,
  ⟨"bivariate-divlinear-bn254-y8", "Bivariate division by Y - f (BN254, yDeg<8)"⟩,
  ⟨"bivariate-divlinear-bn254-y16", "Bivariate division by Y - f (BN254, yDeg<16)"⟩,
  ⟨"bivariate-divlinear-bn254-y32", "Bivariate division by Y - f (BN254, yDeg<32)"⟩
]

/-- Input-shape label for a given coefficient count (`xDegree < 8`, so
`yDegree < terms / 8`). -/
private def factorInputShape (terms : Nat) : String :=
  s!"xDegree<8, yDegree<{terms / 8}, divisor Y - f with deg f < 8"

/-- Build a bivariate polynomial from generated coefficients (xDegree < 8). -/
private def buildCBivariate {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (terms : Array R) : CBivariate R :=
  Id.run do
    let mut p : CBivariate R := 0
    for i in [0:terms.size] do
      p := p + CBivariate.monomialXY (i % 8) (i / 8) (terms.getD i 0)
    pure p

/-- Build a univariate polynomial from generated coefficients. -/
private def buildCPolynomial {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (terms : Array R) : CPolynomial R :=
  Id.run do
    let mut p : CPolynomial R := 0
    for i in [0:terms.size] do
      p := p + CPolynomial.monomial i (terms.getD i 0)
    pure p

/-- The linear divisor `Y - f`, built at the underlying `CPolynomial (CPolynomial R)`. -/
private def linearDivisor {R : Type*}
    [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) : CBivariate R :=
  (CPolynomial.X : CPolynomial (CPolynomial R)) - CPolynomial.C f

/-- Run the `divByLinearY` vs `divByMonic` comparison over a prime `ZMod` field at
one `Y`-degree size (`terms` coefficients, `yDegree < terms / 8`). -/
private def runFactorZMod (modulus : Nat) [Fact (Nat.Prime modulus)]
    (key fieldName fieldTitle nameSuffix yLabel : String) (terms : Nat)
    (largeHorner mediumHorner smallHorner largeMonic mediumMonic smallMonic : Nat)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (qTerms, gen) := (zmodArray modulus terms false).run gen
  let (fTerms, gen) := (zmodArray modulus 8 false).run gen
  let (perturb, gen) := (zmodArray modulus 64 false).run gen
  let q := buildCBivariate qTerms
  let f := buildCPolynomial fTerms
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat largeHorner mediumHorner smallHorner
  let monicMeasured := preset.selectNat largeMonic mediumMonic smallMonic
  let checksumIterations := groupChecksumIterations measured [hornerMeasured, monicMeasured]
  let shape := factorInputShape terms
  let fAt (i : Nat) : CPolynomial (ZMod modulus) :=
    f + CPolynomial.C (perturb.getD (i % perturb.size) 0)
  let checksumBiv (p : CBivariate (ZMod modulus)) : Nat :=
    checksumCPolynomial (checksumCPolynomial checksumZMod) p
  let horner ← runTimed
    ("bivariate-deflate-horner-" ++ yLabel ++ nameSuffix) "CBivariate" "divByLinearY" fieldName
    shape preset warmup hornerMeasured
    (fun i ↦ (CBivariate.divByLinearY q (fAt i)).1)
    checksumBiv (checksumIterations := checksumIterations)
  let monic ← runTimed
    ("bivariate-deflate-divbymonic-" ++ yLabel ++ nameSuffix) "CBivariate" "divByMonic" fieldName
    shape preset warmup monicMeasured
    (fun i ↦ (CPolynomial.divByMonic q (linearDivisor (fAt i)) : CBivariate (ZMod modulus)))
    checksumBiv (checksumIterations := checksumIterations)
  pure ({
    groupKey := key,
    title := "Bivariate division by Y - f (" ++ fieldTitle ++ ", " ++ yLabel ++ ")",
    records := #[horner, monic] }, gen)

/-- Run the KoalaBear comparison at one `Y`-degree size. -/
private def runFactorKoalaBear (key yLabel : String) (terms : Nat)
    (largeHorner mediumHorner smallHorner largeMonic mediumMonic smallMonic : Nat)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (qTerms, gen) := (koalaBearArray terms false).run gen
  let (fTerms, gen) := (koalaBearArray 8 false).run gen
  let (perturb, gen) := (koalaBearArray 64 false).run gen
  let q := buildCBivariate qTerms
  let f := buildCPolynomial fTerms
  let warmup := warmupIterations preset
  let measured := measuredIterations preset
  let hornerMeasured := preset.selectNat largeHorner mediumHorner smallHorner
  let monicMeasured := preset.selectNat largeMonic mediumMonic smallMonic
  let checksumIterations := groupChecksumIterations measured [hornerMeasured, monicMeasured]
  let shape := factorInputShape terms
  let fAt (i : Nat) : CPolynomial KoalaBear.Field :=
    f + CPolynomial.C (perturb.getD (i % perturb.size) 0)
  let checksumBiv (p : CBivariate KoalaBear.Field) : Nat :=
    checksumCPolynomial (checksumCPolynomial checksumKoalaBear) p
  let horner ← runTimed
    ("bivariate-deflate-horner-" ++ yLabel) "CBivariate" "divByLinearY" "KoalaBear.Field"
    shape preset warmup hornerMeasured
    (fun i ↦ (CBivariate.divByLinearY q (fAt i)).1)
    checksumBiv (checksumIterations := checksumIterations)
  let monic ← runTimed
    ("bivariate-deflate-divbymonic-" ++ yLabel) "CBivariate" "divByMonic" "KoalaBear.Field"
    shape preset warmup monicMeasured
    (fun i ↦ (CPolynomial.divByMonic q (linearDivisor (fAt i)) : CBivariate KoalaBear.Field))
    checksumBiv (checksumIterations := checksumIterations)
  pure ({
    groupKey := key,
    title := "Bivariate division by Y - f (KoalaBear, " ++ yLabel ++ ")",
    records := #[horner, monic] }, gen)

/-- Runnable bivariate linear-division benchmark tasks (3 fields × 3 `Y`-sizes). -/
def factorTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-koalabear-y8", "Bivariate division by Y - f (KoalaBear, yDeg<8)"⟩
    (runFactorKoalaBear "bivariate-divlinear-koalabear-y8" "y8" 64 800 120 10 350 50 8),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-koalabear-y16", "Bivariate division by Y - f (KoalaBear, yDeg<16)"⟩
    (runFactorKoalaBear "bivariate-divlinear-koalabear-y16" "y16" 128 250 40 5 100 15 4),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-koalabear-y32", "Bivariate division by Y - f (KoalaBear, yDeg<32)"⟩
    (runFactorKoalaBear "bivariate-divlinear-koalabear-y32" "y32" 256 60 10 3 20 4 2),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-goldilocks-y8", "Bivariate division by Y - f (Goldilocks, yDeg<8)"⟩
    (runFactorZMod Goldilocks.fieldSize "bivariate-divlinear-goldilocks-y8" "Goldilocks.Field"
      "Goldilocks" "-goldilocks" "y8" 64 300 45 8 200 30 6),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-goldilocks-y16", "Bivariate division by Y - f (Goldilocks, yDeg<16)"⟩
    (runFactorZMod Goldilocks.fieldSize "bivariate-divlinear-goldilocks-y16" "Goldilocks.Field"
      "Goldilocks" "-goldilocks" "y16" 128 120 20 5 50 10 4),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-goldilocks-y32", "Bivariate division by Y - f (Goldilocks, yDeg<32)"⟩
    (runFactorZMod Goldilocks.fieldSize "bivariate-divlinear-goldilocks-y32" "Goldilocks.Field"
      "Goldilocks" "-goldilocks" "y32" 256 30 6 3 13 3 2),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-bn254-y8", "Bivariate division by Y - f (BN254, yDeg<8)"⟩
    (runFactorZMod BN254.scalarFieldSize "bivariate-divlinear-bn254-y8" "BN254.ScalarField"
      "BN254" "-bn254" "y8" 64 250 40 6 150 25 5),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-bn254-y16", "Bivariate division by Y - f (BN254, yDeg<16)"⟩
    (runFactorZMod BN254.scalarFieldSize "bivariate-divlinear-bn254-y16" "BN254.ScalarField"
      "BN254" "-bn254" "y16" 128 60 12 4 40 8 3),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-bn254-y32", "Bivariate division by Y - f (BN254, yDeg<32)"⟩
    (runFactorZMod BN254.scalarFieldSize "bivariate-divlinear-bn254-y32" "BN254.ScalarField"
      "BN254" "-bn254" "y32" 256 15 4 2 10 3 2)
]

end CompPolyBench
