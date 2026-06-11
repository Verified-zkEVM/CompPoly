/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant
import Mathlib.Algebra.Field.ZMod

/-!
# Polynomial-Matrix Approximant Tests

Focused executable checks for X-adic approximant problem sizing, recursive
PM-basis plumbing, partial-linearization orders, and exact-nullspace lifts.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.PolynomialMatrix
open CompPoly.PolynomialMatrix.Approximant

namespace LinearAlgebra.PolynomialMatrix.Approximant

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def X : CPolynomial F3 :=
  CPolynomial.X

private def problem : XAdicProblem F3 :=
  { orders := #[2]
    matrix := #[
      #[1],
      #[X]
    ] }

private def fullRankProblem : XAdicProblem F3 :=
  { orders := #[1]
    matrix := #[
      #[1]
    ] }

private def identityLeaf (problem : XAdicProblem F3) (_shift : Array Nat) :
    PolynomialMatrix F3 :=
  PolynomialMatrix.identity problem.matrix.size

private def lowCtx : PolynomialMatrix.MulLowContext F3 :=
  PolynomialMatrix.MulLowContext.fromMulContext CPolynomial.MulContext.naive

private def runtime : PMBasisRuntime F3 :=
  { mulContext := CPolynomial.MulContext.naive
    lowMulContext := lowCtx
    composeBasis := PolynomialMatrix.mulStrassenWith lowCtx 1
    residualProduct := PolynomialMatrix.mulTruncColumnStrassenWith lowCtx 1
    leafCutoff := 1
    leafBasis := identityLeaf }

private def kernelLeafRows : PolynomialMatrix F3 :=
  kernelLeafBasis problem #[0, 0]

private def firstPivotOnlyRows : PolynomialMatrix F3 :=
  #[
    #[1, 0]
  ]

private def compositionLeft : PolynomialMatrix F3 :=
  #[
    #[1 + X, X ^ 2],
    #[X, 1]
  ]

private def compositionRight : PolynomialMatrix F3 :=
  #[
    #[1, X],
    #[X + 1, X ^ 2]
  ]

private def rectangularLeft : PolynomialMatrix F3 :=
  #[
    #[1, X],
    #[X + 1, X ^ 2],
    #[0, 1]
  ]

private def rectangularRight : PolynomialMatrix F3 :=
  #[
    #[X, 1, X ^ 2],
    #[1, X + 1, 0]
  ]

private def moduli : Array (CPolynomial F3) :=
  #[X ^ 2, X]

private def equation : ModularEquation F3 :=
  { moduli := moduli
    matrix := #[
      #[1, X],
      #[X, 1]
    ] }

private def chunkPlan : PartialLinearizationPlan :=
  partialLinearizationPlan 2 2 moduli #[0, 5]

private def profileChunkPlan : PartialLinearizationPlan :=
  partialLinearizationPlanFromPivotDegrees 2 2 moduli #[0, 5] #[some 7, none]

private def highDegreeProfileChunkPlan : PartialLinearizationPlan :=
  partialLinearizationPlanFromPivotDegrees 2 2 moduli #[0, 20]
    #[some 25, some 45]

private def noChunkPlan : PartialLinearizationPlan :=
  unchunkedPartialLinearizationPlan 2 2 moduli

private def chunkedRow : PolynomialRow F3 :=
  #[1, X, 0, 1, 0, 0]

private def profileRows : PolynomialMatrix F3 :=
  #[
    #[X ^ 2, 0],
    #[0, X]
  ]

private def profileFromRows : PivotDegreeProfile :=
  pivotDegreeProfileFromRows 2 profileRows #[0, 5]

private def productionPMCtx : PMBasisContext F3 :=
  kernelLeafPMBasisContext CPolynomial.MulContext.naive 1

private def remainderModCtx : CPolynomial.ModContext F3 :=
  CPolynomial.ModContext.remainderOnly

private def discoveredProfile : PivotDegreeProfile :=
  discoverPivotDegreeProfileViaPMBasis CPolynomial.MulContext.naive
    remainderModCtx productionPMCtx equation #[0, 5]

private def knownDegreePlan : PartialLinearizationPlan :=
  partialLinearizationPlanFromPivotDegrees equation.solutionWidth equation.modularWidth
    equation.moduli #[0, 5] discoveredProfile.degrees

private def knownDegreeProblem : XAdicProblem F3 :=
  chunkedExactNullspaceProblemForShift remainderModCtx equation knownDegreePlan #[0, 5]

private def knownDegreeExpandedRows : PolynomialMatrix F3 :=
  productionPMCtx.basis knownDegreeProblem
    (chunkedExactNullspaceShift knownDegreePlan #[0, 5])

private def knownDegreeCompressedRows : PolynomialMatrix F3 :=
  compactNonzeroRows
    (compressChunkedPrincipalRows knownDegreePlan knownDegreeExpandedRows)

private def knownDegreeRows : PolynomialMatrix F3 :=
  knownDegreeSolutionBasisViaPMBasis remainderModCtx productionPMCtx equation #[0, 5]
    discoveredProfile

private def knownDegreeFilteredRows : PolynomialMatrix F3 :=
  filterModularSolutionRows CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly equation knownDegreeRows

private def productionRows : PolynomialMatrix F3 :=
  filteredSolutionBasisViaPMBasis CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly productionPMCtx equation #[0, 5] none

private def debugUnchunkedRows : PolynomialMatrix F3 :=
  debugUnchunkedFilteredSolutionBasisViaPMBasis CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly productionPMCtx equation #[0, 5]

private def leastChoiceRows : PolynomialMatrix F3 :=
  #[
    #[X ^ 2, 0],
    #[1, 0],
    #[0, X]
  ]

#guard maxOrder problem == 2
#guard totalOrder problem == 2
#guard lowerOrders problem 1 == #[1]
#guard residualOrders problem 1 == #[1]
#guard leafDegreeCap problem == 2
#guard (coefficientMatrix problem).rows == 2
#guard (coefficientMatrix problem).cols == 4
#guard kernelLeafRows.any fun row ↦ row == #[-X, 1]
#guard (kernelLeafBasis fullRankProblem #[0]).any fun row ↦ row == #[X]
#guard rowsContainLeadingPosition firstPivotOnlyRows #[0, 0] 0
#guard !rowsContainLeadingPosition firstPivotOnlyRows #[0, 0] 1
#guard missingCompletionRows problem #[0, 0] firstPivotOnlyRows == #[#[0, X ^ 2]]
#guard rowGet (rowMulMatrixTruncColumnWith lowCtx #[2] #[1, X] problem.matrix) 0 == 1
#guard mulBoundedWith lowCtx compositionLeft compositionRight ==
  mulWith CPolynomial.MulContext.naive compositionLeft compositionRight
#guard mulStrassenWith lowCtx 1 compositionLeft compositionRight ==
  mulWith CPolynomial.MulContext.naive compositionLeft compositionRight
#guard mulStrassenWith lowCtx 1 rectangularLeft rectangularRight ==
  mulWith CPolynomial.MulContext.naive rectangularLeft rectangularRight
#guard mulTruncColumnStrassenWith lowCtx 1 #[2, 1, 3]
    rectangularLeft rectangularRight ==
  mulTruncColumnWith lowCtx #[2, 1, 3] rectangularLeft rectangularRight

#guard (pmBasis runtime problem #[0, 0]).size == 2
#guard MatrixWidth (pmBasis runtime problem #[0, 0]) == 2

#guard modulusDegreeMass moduli == 3
#guard chunkDelta 2 moduli == 2
#guard linearizedOrders 2 moduli == #[5, 4]
#guard chunkPlan.chunks.size == 4
#guard chunkedExactNullspaceShift chunkPlan #[0, 5] == #[3, 5, 7, 8, 2, 2]
#guard profileChunkPlan.chunks.size == 5
#guard highDegreeProfileChunkPlan.chunks.size > profileChunkPlan.chunks.size
#guard noChunkPlan.chunks == #[{ coord := 0, offset := 0 }, { coord := 1, offset := 0 }]
#guard profileFromRows.degrees == #[some 2, some 6]
#guard (chunkedExactNullspaceLift remainderModCtx equation chunkPlan).size == 6
#guard MatrixWidth (chunkedExactNullspaceLift remainderModCtx equation chunkPlan) == 2
#guard rowGet ((chunkedExactNullspaceLift remainderModCtx equation chunkPlan).getD 1 #[]) 0 == 0
#guard rowGet ((chunkedExactNullspaceLift remainderModCtx equation chunkPlan).getD 3 #[]) 0 == X
#guard compressChunkedPrincipalRow chunkPlan chunkedRow == #[1 + X ^ 3, 1]

#guard equation.solutionWidth == 2
#guard equation.modularWidth == 2
#guard (exactNullspaceLift equation).size == 4
#guard MatrixWidth (exactNullspaceLift equation) == 2
#guard rowGet ((exactNullspaceLift equation).getD 2 #[]) 0 == -(X ^ 2)
#guard rowGet ((exactNullspaceLift equation).getD 3 #[]) 1 == -X
#guard (filterModularSolutionRows CPolynomial.MulContext.naive
  CPolynomial.ModContext.remainderOnly equation #[PolynomialMatrix.zeroRow 2]).isEmpty

#guard knownDegreeCompressedRows == knownDegreeRows
#guard !knownDegreeRows.isEmpty
#guard knownDegreeRows.all fun row ↦
  rowSatisfiesModularBool CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly row equation.matrix equation.moduli
#guard !knownDegreeFilteredRows.isEmpty
#guard knownDegreeFilteredRows.all fun row ↦
  rowSatisfiesModularBool CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly row equation.matrix equation.moduli
#guard !productionRows.isEmpty
#guard MatrixWidth productionRows == equation.solutionWidth
#guard productionRows.all fun row ↦
  rowSatisfiesModularBool CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly row equation.matrix equation.moduli
#guard debugUnchunkedRows.all fun row ↦
  rowSatisfiesModularBool CPolynomial.MulContext.naive
    CPolynomial.ModContext.remainderOnly row equation.matrix equation.moduli
#guard match leastShiftedDegreeChoice? leastChoiceRows #[0, 3] with
  | some choice => choice.index == 1 && choice.degree == 0 && choice.row == #[1, 0]
  | none => false

end LinearAlgebra.PolynomialMatrix.Approximant

end CompPolyTests
