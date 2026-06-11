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
# Guruswami-Sudan Benchmark Helpers

Shared KoalaBear input shapes, checksum helpers, and group metadata for the
dense-interpolation/root-search Guruswami-Sudan benchmark subset.
-/

open CompPoly
open CompPoly.GuruswamiSudan

namespace CompPolyBench

def gsPointCount : Nat := 128
def gsMessageDegree : Nat := 32
def gsWeightedDegreeBound : Nat := 4 * (gsMessageDegree - 1)
def gsMultiplicity : Nat := 4

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

def gsRootShape : String :=
  s!"k={gsMessageDegree},Q=(Y-p)(Y-(p+7))"

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

def nonlinearRootBenchmarkQ {F : Type*}
    [CommRing F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (p : CPolynomial F) : CBivariate F :=
  CBivariate.linearYDivisor p * CBivariate.linearYDivisor (p + CPolynomial.C 7)

def koalaFieldRoots : FieldRootContext KoalaBear.Field := koalaBearFieldRootContext
def koalaFieldRootsFast : FieldRootContext KoalaBear.Field :=
  koalaBearNttFastFieldRootContext
def koalaFastFieldRoots : FieldRootContext KoalaBear.Fast.Field :=
  fastKoalaBearFieldRootContext
def koalaFastFieldRootsFast : FieldRootContext KoalaBear.Fast.Field :=
  fastKoalaBearNttFastFieldRootContext

def checksumDenseMatrix {F : Type*} [Zero F]
    (checksum : F → Nat) (M : DenseMatrix F) : Nat :=
  mixChecksum (mixChecksum M.rows M.cols) (checksumArray checksum M.data)

def checksumOptionArray {F : Type*} (checksum : F → Nat)
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

def checksumPolynomialArrayKoala (ps : Array (CPolynomial KoalaBear.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBear) ps

def checksumPolynomialArrayKoalaFast
    (ps : Array (CPolynomial KoalaBear.Fast.Field)) : Nat :=
  checksumArray (checksumCPolynomial checksumKoalaBearFast) ps

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
  ⟨"guruswami-sudan-root-koalabear",
    "Guruswami-Sudan root finding (KoalaBear)"⟩,
  ⟨"guruswami-sudan-core-small-koalabear",
    "Guruswami-Sudan full core, small (KoalaBear)"⟩,
  ⟨"guruswami-sudan-packed-filter-koalabear",
    "Guruswami-Sudan packed distance filtering (KoalaBear)"⟩,
  ⟨"guruswami-sudan-filtered-core-small-koalabear",
    "Guruswami-Sudan filtered core, small (KoalaBear)"⟩
]

end CompPolyBench
