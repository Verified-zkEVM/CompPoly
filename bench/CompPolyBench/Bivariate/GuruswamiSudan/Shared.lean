/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Bivariate.Deriv
import CompPoly.Bivariate.GuruswamiSudan
import CompPoly.Bivariate.GuruswamiSudan.Implementations
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.WitnessDivisibility
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear

/-!
# Guruswami-Sudan Benchmarks

KoalaBear cost-center benchmarks for the dense interpolation path,
Roth-Ruckenstein and Alekhnovich root finding, and
full backend-parametric `gsCore` and `gsFilteredCore`.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

def gsPointCount : Nat := 128
def gsMessageDegree : Nat := 32
def gsWeightedDegreeBound : Nat := 4 * (gsMessageDegree - 1)
def gsMultiplicity : Nat := 4
def gsCheckMultiplicity : Nat := 2

def gsKoalaParams : GSInterpParams :=
  { messageDegree := gsMessageDegree
    multiplicity := gsMultiplicity
    weightedDegreeBound := gsWeightedDegreeBound }

def gsMediumInterpPointCount : Nat := 192
def gsMediumInterpMessageDegree : Nat := 49
def gsMediumInterpMultiplicity : Nat := 2
/-- Weighted-degree bound scaled with the multiplicity (`D/m = 2.5 * (k - 1)`),
so the agreement margin `m * t > D` is kept for both the codeword and the
`every7`-perturbed received words at any multiplicity. -/
def gsMediumInterpWeightedDegreeBound : Nat :=
  5 * gsMediumInterpMultiplicity * (gsMediumInterpMessageDegree - 1) / 2
def gsMediumInterpParams : GSInterpParams :=
  { messageDegree := gsMediumInterpMessageDegree
    multiplicity := gsMediumInterpMultiplicity
    weightedDegreeBound := gsMediumInterpWeightedDegreeBound }

/-- Long-code shape for the asymptotic interpolation comparison: at
`n ≈ 5000` the defect-driven Mulders-Storjohann reduction (quadratic in `n`
on error-bearing words) crosses over against the quasi-linear approximant
PM-basis solver, so the large group compares only those two backends.
Koetter grows like `~n^3.4` here (extrapolated ~13 h per call) and the dense
solver is far beyond that, so neither is benchmarked at this size. -/
def gsLargeInterpPointCount : Nat := 5040
def gsLargeInterpMessageDegree : Nat := 1261
def gsLargeInterpMultiplicity : Nat := 2
def gsLargeInterpWeightedDegreeBound : Nat :=
  5 * gsLargeInterpMultiplicity * (gsLargeInterpMessageDegree - 1) / 2
def gsLargeInterpParams : GSInterpParams :=
  { messageDegree := gsLargeInterpMessageDegree
    multiplicity := gsLargeInterpMultiplicity
    weightedDegreeBound := gsLargeInterpWeightedDegreeBound }

def gsLargeInterpInputShape : String :=
  s!"n={gsLargeInterpPointCount},k={gsLargeInterpMessageDegree}," ++
    s!"m={gsLargeInterpMultiplicity},D={gsLargeInterpWeightedDegreeBound}"

def gsSmallPointCount : Nat := 64
def gsSmallMessageDegree : Nat := 16
def gsSmallWeightedDegreeBound : Nat :=
  5 * (gsSmallMessageDegree - 1)
def gsSmallMultiplicity : Nat := 2
def gsSmallParams : GSInterpParams :=
  { messageDegree := gsSmallMessageDegree
    multiplicity := gsSmallMultiplicity
    weightedDegreeBound := gsSmallWeightedDegreeBound }

def gsInputShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsMultiplicity},D={gsWeightedDegreeBound}"

def gsSmallInputShape : String :=
  s!"n={gsSmallPointCount},k={gsSmallMessageDegree}," ++
    s!"m={gsSmallMultiplicity},D={gsSmallWeightedDegreeBound}"

def gsSmallInterpInputShape : String :=
  gsSmallInputShape

def gsMediumInterpInputShape : String :=
  s!"n={gsMediumInterpPointCount},k={gsMediumInterpMessageDegree}," ++
    s!"m={gsMediumInterpMultiplicity},D={gsMediumInterpWeightedDegreeBound}"

def gsMultiplicityShape : String :=
  s!"n={gsPointCount},k={gsMessageDegree},m={gsCheckMultiplicity},Q=(Y-p)^2"

def gsRootShape : String :=
  s!"k={gsMessageDegree},Q=(Y-p)(Y-(p+7))"

def gsFilteredShape : String :=
  gsMediumInterpInputShape ++ ",r=0"

def gsSmallFilteredShape : String :=
  gsSmallInterpInputShape ++ ",r=0"

def codewordPointsWithCount {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (pointCount : Nat) (p : CPolynomial F) : Array (Prod F F) :=
  (List.range pointCount).map
    (fun i ↦
      let x : F := (i + 1 : Nat)
      (x, CPolynomial.eval x p)) |>.toArray

def codewordPoints {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Array (Prod F F) :=
  codewordPointsWithCount gsPointCount p

def gsSmallBenchmarkPoints {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Array (Prod F F) :=
  codewordPointsWithCount gsSmallPointCount p

def gsMediumBenchmarkPoints {F : Type*} [Semiring F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Array (Prod F F) :=
  codewordPointsWithCount gsMediumInterpPointCount p

def rootBenchmarkQ {F : Type*}
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYDivisor p

def multiplicityBenchmarkQ {F : Type*}
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  let Q := rootBenchmarkQ p
  Q * Q

def koalaFieldRoots : FieldRootContext KoalaBear.Field := koalaBearFieldRootContext
def koalaFieldRootsFast : FieldRootContext KoalaBear.Field :=
  koalaBearNttFastFieldRootContext
def koalaFastFieldRoots : FieldRootContext KoalaBear.Fast.Field :=
  fastKoalaBearFieldRootContext
def koalaFastFieldRootsFast : FieldRootContext KoalaBear.Fast.Field :=
  fastKoalaBearNttFastFieldRootContext

def nonlinearRootBenchmarkQ {F : Type*}
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYDivisor p * CBivariate.linearYDivisor (p + CPolynomial.C 7)

def checksumDenseMatrix {F : Type*} [Zero F]
    (checksum : F -> Nat) (M : DenseMatrix F) : Nat :=
  mixChecksum (mixChecksum M.rows M.cols) (checksumArray checksum M.data)

def checksumOptionArray {F : Type*} (checksum : F -> Nat)
    (v? : Option (Array F)) : Nat :=
  match v? with
  | none => 0
  | some v => mixChecksum 1 (checksumArray checksum v)

def checksumInterpolationValidityOption {F : Type*}
    [CommSemiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams)
    (Q? : Option (CBivariate F)) : Nat :=
  match Q? with
  | none => 0
  | some Q => if interpolationWitnessIsValidBool points params Q then 2 else 1

def checksumPolynomialMatrix {F : Type*} [Zero F]
    (checksum : F -> Nat) (M : PolynomialMatrix F) : Nat :=
  checksumArray (fun row ↦ checksumArray (checksumCPolynomial checksum) row) M

def checksumPolynomialArrayKoala (ps : Array (CPolynomial KoalaBear.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBear) ps

def checksumPolynomialArrayKoalaFast
    (ps : Array (CPolynomial KoalaBear.Fast.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBearFast) ps

def checksumBool (b : Bool) : Nat :=
  if b then 1 else 0

def checkMultiplicityShiftOnce {F : Type*}
    [CommSemiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (r : Nat) (x y : F) : Bool :=
  let shifted := CBivariate.shiftC x y Q
  List.all (List.range r) fun k ↦
    List.all (List.range (k + 1)) fun i ↦
      CBivariate.coeff shifted i (k - i) == 0

def gsWarmupIterations (preset : BenchPreset) : Nat :=
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
  ⟨"guruswami-sudan-interp-medium-koalabear",
    "Guruswami-Sudan interpolation, medium (KoalaBear)"⟩,
  ⟨"guruswami-sudan-lee-setup-medium-koalabear",
    "Guruswami-Sudan Lee-O'Sullivan setup, medium (KoalaBear)"⟩,
  ⟨"guruswami-sudan-hasse-koalabear",
    "Guruswami-Sudan Hasse multiplicity checking (KoalaBear)"⟩,
  ⟨"guruswami-sudan-compose-koalabear",
    "Guruswami-Sudan composition in Y (KoalaBear)"⟩,
  ⟨"guruswami-sudan-root-koalabear",
    "Guruswami-Sudan root finding (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-small-koalabear",
    "Guruswami-Sudan full core, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-medium-koalabear",
    "Guruswami-Sudan full core, medium (KoalaBear)"⟩,
  ⟨"guruswami-sudan-packed-filter-koalabear",
    "Guruswami-Sudan packed distance filtering (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-small-koalabear",
    "Guruswami-Sudan filtered core, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-medium-koalabear",
    "Guruswami-Sudan filtered core, medium (KoalaBear)"⟩
]

