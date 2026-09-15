/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
module

public import CompPolyBench.Common
public import CompPoly.Bivariate.Factor
public import CompPoly.Univariate.DivisionCorrectness
public import CompPoly.Fields.BN254

/-!
# Bivariate Linear-Division Benchmarks

Compares two ways to divide a bivariate polynomial `Q` by the linear factor
`Y - f` in the `Y` variable:

* `divByLinearY`: synthetic (Horner) division specialised to a monic linear
  divisor;
* `CPolynomial.divByMonic`: general monic long division applied to `Y - f`.

Measured over KoalaBear, Goldilocks, and BN254, at `Y`-degrees `< 8`, `< 16`,
and `< 32`. Both methods produce the same quotient, verified by an identical
checksum within each (field, size) group. The divisor's constant term is
perturbed per iteration so each measured call recomputes the division.
-/

public section

open CompPoly

namespace CompPolyBench

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
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (qTerms, gen) := (zmodArray modulus terms false).run gen
  let (fTerms, gen) := (zmodArray modulus 8 false).run gen
  let (perturb, gen) := (zmodArray modulus 64 false).run gen
  let q := buildCBivariate qTerms
  let f := buildCPolynomial fTerms
  let checksumIterations := digestPeriod perturb.size
  let shape := factorInputShape terms
  let fAt (i : Nat) : CPolynomial (ZMod modulus) :=
    f + CPolynomial.C (perturb.getD (i % perturb.size) 0)
  let checksumBiv (p : CBivariate (ZMod modulus)) : Nat :=
    checksumCPolynomial (checksumCPolynomial checksumZMod) p
  let horner ← runTimedSpec
    { name := ("bivariate-deflate-horner-" ++ yLabel ++ nameSuffix),
      representation := "CBivariate", method := "divByLinearY", field := fieldName,
      inputShape := shape, digestIterations := checksumIterations }
    preset (fun i ↦ (CBivariate.divByLinearY q (fAt i)).1) checksumBiv
  let monic ← runTimedSpec
    { name := ("bivariate-deflate-divbymonic-" ++ yLabel ++ nameSuffix),
      representation := "CBivariate", method := "divByMonic", field := fieldName,
      inputShape := shape, digestIterations := checksumIterations }
    preset
    (fun i ↦ (CPolynomial.divByMonic q (linearDivisor (fAt i)) : CBivariate (ZMod modulus)))
    checksumBiv
  pure ({
    groupKey := key,
    title := "Bivariate division by Y - f (" ++ fieldTitle ++ ", " ++ yLabel ++ ")",
    records := #[horner, monic] }, gen)

/-- Run the KoalaBear comparison at one `Y`-degree size. -/
private def runFactorKoalaBear (key yLabel : String) (terms : Nat)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (qTerms, gen) := (koalaBearArray terms false).run gen
  let (fTerms, gen) := (koalaBearArray 8 false).run gen
  let (perturb, gen) := (koalaBearArray 64 false).run gen
  let q := buildCBivariate qTerms
  let f := buildCPolynomial fTerms
  let checksumIterations := digestPeriod perturb.size
  let shape := factorInputShape terms
  let fAt (i : Nat) : CPolynomial KoalaBear.Field :=
    f + CPolynomial.C (perturb.getD (i % perturb.size) 0)
  let checksumBiv (p : CBivariate KoalaBear.Field) : Nat :=
    checksumCPolynomial (checksumCPolynomial checksumKoalaBear) p
  let horner ← runTimedSpec
    { name := ("bivariate-deflate-horner-" ++ yLabel), representation := "CBivariate",
      method := "divByLinearY", field := "KoalaBear.Field", inputShape := shape,
      digestIterations := checksumIterations }
    preset (fun i ↦ (CBivariate.divByLinearY q (fAt i)).1) checksumBiv
  let monic ← runTimedSpec
    { name := ("bivariate-deflate-divbymonic-" ++ yLabel), representation := "CBivariate",
      method := "divByMonic", field := "KoalaBear.Field", inputShape := shape,
      digestIterations := checksumIterations }
    preset
    (fun i ↦ (CPolynomial.divByMonic q (linearDivisor (fAt i)) : CBivariate KoalaBear.Field))
    checksumBiv
  pure ({
    groupKey := key,
    title := "Bivariate division by Y - f (KoalaBear, " ++ yLabel ++ ")",
    records := #[horner, monic] }, gen)

/-- Runnable bivariate linear-division benchmark tasks (3 fields × 3 `Y`-sizes). -/
def factorTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-koalabear-y8", "Bivariate division by Y - f (KoalaBear, yDeg<8)"⟩
    (runFactorKoalaBear "bivariate-divlinear-koalabear-y8" "y8" 64),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-koalabear-y16", "Bivariate division by Y - f (KoalaBear, yDeg<16)"⟩
    (runFactorKoalaBear "bivariate-divlinear-koalabear-y16" "y16" 128),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-koalabear-y32", "Bivariate division by Y - f (KoalaBear, yDeg<32)"⟩
    (runFactorKoalaBear "bivariate-divlinear-koalabear-y32" "y32" 256),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-goldilocks-y8", "Bivariate division by Y - f (Goldilocks, yDeg<8)"⟩
    (runFactorZMod Goldilocks.fieldSize "bivariate-divlinear-goldilocks-y8" "Goldilocks.Field"
      "Goldilocks" "-goldilocks" "y8" 64),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-goldilocks-y16", "Bivariate division by Y - f (Goldilocks, yDeg<16)"⟩
    (runFactorZMod Goldilocks.fieldSize "bivariate-divlinear-goldilocks-y16" "Goldilocks.Field"
      "Goldilocks" "-goldilocks" "y16" 128),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-goldilocks-y32", "Bivariate division by Y - f (Goldilocks, yDeg<32)"⟩
    (runFactorZMod Goldilocks.fieldSize "bivariate-divlinear-goldilocks-y32" "Goldilocks.Field"
      "Goldilocks" "-goldilocks" "y32" 256),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-bn254-y8", "Bivariate division by Y - f (BN254, yDeg<8)"⟩
    (runFactorZMod BN254.scalarFieldSize "bivariate-divlinear-bn254-y8" "BN254.ScalarField"
      "BN254" "-bn254" "y8" 64),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-bn254-y16", "Bivariate division by Y - f (BN254, yDeg<16)"⟩
    (runFactorZMod BN254.scalarFieldSize "bivariate-divlinear-bn254-y16" "BN254.ScalarField"
      "BN254" "-bn254" "y16" 128),
  BenchTask.fromGroupRunner
    ⟨"bivariate-divlinear-bn254-y32", "Bivariate division by Y - f (BN254, yDeg<32)"⟩
    (runFactorZMod BN254.scalarFieldSize "bivariate-divlinear-bn254-y32" "BN254.ScalarField"
      "BN254" "-bn254" "y32" 256)
]

end CompPolyBench
