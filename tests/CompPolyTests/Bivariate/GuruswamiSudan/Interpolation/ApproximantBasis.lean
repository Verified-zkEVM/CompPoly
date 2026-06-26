/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis
import CompPoly.Bivariate.GuruswamiSudan.Core
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Approximant-Basis Guruswami-Sudan Interpolation Tests

Focused executable coverage for GS modular-data construction and diagonal
relation checks.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan
open CompPoly.GuruswamiSudan.ApproximantBasis
open CompPoly.PolynomialMatrix

namespace GuruswamiSudan.Interpolation.ApproximantBasis

abbrev F3 := ZMod 3
abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

instance : Fact (Nat.Prime 5) :=
  ⟨by decide⟩

private def X : CPolynomial F3 :=
  CPolynomial.X

private def paramsS1 : GSInterpParams :=
  { messageDegree := 2, multiplicity := 1, weightedDegreeBound := 2 }

private def paramsS2 : GSInterpParams :=
  { messageDegree := 2, multiplicity := 2, weightedDegreeBound := 4 }

private def paramsS3 : GSInterpParams :=
  { messageDegree := 2, multiplicity := 3, weightedDegreeBound := 6 }

private def lowParams : GSInterpParams :=
  { messageDegree := 1, multiplicity := 1, weightedDegreeBound := 0 }

private def nonCodewordParams : GSInterpParams :=
  { messageDegree := 2, multiplicity := 1, weightedDegreeBound := 3 }

private def nonCodewordStressParams : GSInterpParams :=
  { messageDegree := 2, multiplicity := 2, weightedDegreeBound := 3 }

private def points : Array (F3 × F3) :=
  #[(0, 0), (1, 1)]

private def nonCodewordPoints : Array (F5 × F5) :=
  #[(0, 0), (1, 1), (2, 0)]

private def lowPoints : Array (F3 × F3) :=
  #[(0, 0)]

private def duplicateXPoints : Array (F3 × F3) :=
  #[(0, 0), (0, 1)]

private def directV : CPolynomial.VanishingPolynomialContext F3 :=
  CPolynomial.VanishingPolynomialContext.direct

private def hornerE : CPolynomial.BatchEvalContext F3 :=
  CPolynomial.BatchEvalContext.horner F3

private def modCtx : CPolynomial.ModContext F3 :=
  CPolynomial.ModContext.remainderOnly

private def directV5 : CPolynomial.VanishingPolynomialContext F5 :=
  CPolynomial.VanishingPolynomialContext.direct

private def hornerE5 : CPolynomial.BatchEvalContext F5 :=
  CPolynomial.BatchEvalContext.horner F5

private def modCtx5 : CPolynomial.ModContext F5 :=
  CPolynomial.ModContext.remainderOnly

private def naiveMul : CPolynomial.MulContext F3 :=
  CPolynomial.MulContext.naive

private def naiveMul5 : CPolynomial.MulContext F5 :=
  CPolynomial.MulContext.naive

private def dataS1 : GSModularData F3 :=
  buildGSModularData directV hornerE naiveMul modCtx points paramsS1

private def dataS2 : GSModularData F3 :=
  buildGSModularData directV hornerE naiveMul modCtx points paramsS2

private def dataS3 : GSModularData F3 :=
  buildGSModularData directV hornerE naiveMul modCtx points paramsS3

private def nonCodewordData : GSModularData F5 :=
  buildGSModularData directV5 hornerE5 naiveMul5 modCtx5 nonCodewordPoints
    nonCodewordParams

private def nonCodewordStressData : GSModularData F5 :=
  buildGSModularData directV5 hornerE5 naiveMul5 modCtx5 nonCodewordPoints
    nonCodewordStressParams

private def pmCtx : PolynomialMatrix.Approximant.PMBasisContext F3 :=
  PolynomialMatrix.Approximant.kernelLeafPMBasisContext
    CPolynomial.MulContext.naive 32

private def solver : PolynomialMatrix.Approximant.ModularSolutionBasisContext F3 :=
  PolynomialMatrix.Approximant.modularSolutionBasisContextViaPMBasis
    CPolynomial.MulContext.naive modCtx pmCtx

private def pmCtx5 : PolynomialMatrix.Approximant.PMBasisContext F5 :=
  PolynomialMatrix.Approximant.kernelLeafPMBasisContext
    CPolynomial.MulContext.naive 32

private def solver5 : PolynomialMatrix.Approximant.ModularSolutionBasisContext F5 :=
  PolynomialMatrix.Approximant.modularSolutionBasisContextViaPMBasis
    CPolynomial.MulContext.naive modCtx5 pmCtx5

private def approxContext : GSInterpContext F3 :=
  approximantBasisInterpContext directV hornerE solver

private def approxContext5 : GSInterpContext F5 :=
  approximantBasisInterpContext directV5 hornerE5 solver5

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private theorem f3Elements_complete : ContainsAllFieldElements f3Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def fieldRoots : FieldRootContext F3 :=
  enumeratingFieldRootContext F3 f3Elements f3Elements_complete

private def rootContext : GSRootContext F3 :=
  rothRuckensteinRootContext F3 fieldRoots

private def rowYMinusX : PolynomialRow F3 :=
  #[-X, 1, 0]

private def rowYMinusXSquared : PolynomialRow F3 :=
  #[X ^ 2, -(CPolynomial.C (2 : F3) * X), 1, 0, 0]

#guard interpolationYCap paramsS1 == 2
#guard interpolationWidth paramsS1 == 3
#guard interpolationShifts paramsS1 == #[0, 1, 2]
#guard distinctXCoordinatesBool points
#guard !distinctXCoordinatesBool duplicateXPoints

#guard dataS1.moduli.size == 1
#guard dataS1.matrix.size == 3
#guard MatrixWidth dataS1.matrix == 1
#guard dataS1.shift == #[0, 1, 2]
#guard rowGet (dataS1.matrix.getD 0 #[]) 0 == 1
#guard rowGet (dataS1.matrix.getD 1 #[]) 0 == X
#guard rowGet (dataS1.matrix.getD 2 #[]) 0 == X
#guard rowSatisfiesModularBool CPolynomial.MulContext.naive modCtx
  rowYMinusX dataS1.matrix dataS1.moduli

#guard dataS2.moduli.size == 2
#guard dataS2.matrix.size == 5
#guard MatrixWidth dataS2.matrix == 2
#guard dataS2.moduli.getD 0 0 == dataS2.G ^ 2
#guard dataS2.moduli.getD 1 0 == dataS2.G
#guard rowGet (dataS2.matrix.getD 0 #[]) 1 == 0
#guard rowGet (dataS2.matrix.getD 1 #[]) 1 == 1
#guard rowSatisfiesModularBool CPolynomial.MulContext.naive modCtx
  rowYMinusXSquared dataS2.matrix dataS2.moduli

#guard dataS3.moduli.size == 3
#guard dataS3.matrix.size == 7
#guard MatrixWidth dataS3.matrix == 3
#guard dataS3.moduli.getD 0 0 == dataS3.G ^ 3
#guard dataS3.moduli.getD 1 0 == dataS3.G ^ 2
#guard dataS3.moduli.getD 2 0 == dataS3.G

#guard approximantBasisPositiveInterpolate directV hornerE solver
  duplicateXPoints paramsS1 == none

#guard (approximantBasisInterpolate directV hornerE solver points paramsS1).isSome
#guard match approximantBasisInterpolate directV hornerE solver points paramsS1 with
  | none => false
  | some Q => interpolationWitnessIsValidBool points paramsS1 Q

#guard (approximantBasisInterpolate directV hornerE solver lowPoints lowParams).isSome
#guard match approximantBasisInterpolate directV hornerE solver lowPoints lowParams with
  | none => false
  | some Q => interpolationWitnessIsValidBool lowPoints lowParams Q

#guard (approximantBasisInterpolate directV5 hornerE5 solver5
  nonCodewordPoints nonCodewordParams).isSome
#guard match approximantBasisInterpolate directV5 hornerE5 solver5
    nonCodewordPoints nonCodewordParams with
  | none => false
  | some Q => interpolationWitnessIsValidBool nonCodewordPoints nonCodewordParams Q

#guard (approximantBasisInterpolate directV5 hornerE5 solver5
  nonCodewordPoints nonCodewordStressParams).isSome
#guard match approximantBasisInterpolate directV5 hornerE5 solver5
    nonCodewordPoints nonCodewordStressParams with
  | none => false
  | some Q => interpolationWitnessIsValidBool nonCodewordPoints nonCodewordStressParams Q

#guard (approxContext5.interpolate nonCodewordPoints nonCodewordStressParams).isSome
#guard match approxContext5.interpolate nonCodewordPoints nonCodewordStressParams with
  | none => false
  | some Q => interpolationWitnessIsValidBool nonCodewordPoints nonCodewordStressParams Q

#guard (gsCore points approxContext rootContext paramsS1).size <= 3
#guard (gsCore lowPoints approxContext rootContext lowParams).size <= 3

end GuruswamiSudan.Interpolation.ApproximantBasis

end CompPolyTests
