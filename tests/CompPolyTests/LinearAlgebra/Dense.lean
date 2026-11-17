/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public meta import CompPoly.LinearAlgebra.Dense
public meta import Mathlib.Algebra.Field.ZMod

/-!
# Dense Linear-Algebra Tests

Focused regression coverage for the dense homogeneous-kernel witness used by
Guruswami-Sudan interpolation, and for the full dense kernel basis against the
row-array kernel.
-/

public meta section

namespace CompPolyTests

open CompPoly

namespace LinearAlgebra.Dense

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def dependentSystem : DenseMatrix F3 :=
  DenseMatrix.ofFn 1 2 fun _ col ↦
    if col = 0 then 1 else 2

#guard (DenseMatrix.homogeneousWitness dependentSystem).isSome

/-- Rank one: the second row is twice the first. -/
private def rankOne : DenseMatrix F3 :=
  DenseMatrix.ofFn 2 3 fun row col ↦
    ((#[#[1, 2, 0], #[2, 1, 0]] : Array (Array F3)).getD row #[]).getD col 0

/-- Full rank and square, so the kernel is trivial. -/
private def fullRank : DenseMatrix F3 :=
  DenseMatrix.ofFn 2 2 fun row col ↦ if row ≤ col then 1 else 0

private def zeroMatrix : DenseMatrix F3 := DenseMatrix.ofFn 2 3 fun _ _ ↦ 0

private def noColumns : DenseMatrix F3 := DenseMatrix.ofFn 2 0 fun _ _ ↦ 0

/-- The first pivot sits in the second row, so the reduction swaps rows. -/
private def needsSwap : DenseMatrix F3 :=
  DenseMatrix.ofFn 2 3 fun row col ↦
    ((#[#[0, 1, 1], #[1, 0, 2]] : Array (Array F3)).getD row #[]).getD col 0

/-- More rows than columns, with a dependent third row. -/
private def tall : DenseMatrix F3 :=
  DenseMatrix.ofFn 3 2 fun row col ↦
    ((#[#[1, 0], #[0, 1], #[1, 1]] : Array (Array F3)).getD row #[]).getD col 0

/-- The dense basis agrees with the row-array basis of the matrix rows, has one
vector per non-pivot column, and each vector solves the system. -/
private def kernelBasisChecks (M : DenseMatrix F3) : Bool :=
  let basis := DenseMatrix.homogeneousKernelBasis M
  basis == DenseMatrix.homogeneousKernelBasisRows M.toRows M.cols &&
    basis.size + (DenseMatrix.rref M).pivots.size == M.cols &&
    basis.all fun v ↦ (M.mulVec v).all (· == 0)

#guard rankOne.toRows == #[#[1, 2, 0], #[2, 1, 0]]
#guard kernelBasisChecks rankOne
#guard (DenseMatrix.homogeneousKernelBasis rankOne).size == 2
#guard kernelBasisChecks fullRank
#guard (DenseMatrix.homogeneousKernelBasis fullRank).size == 0
#guard kernelBasisChecks zeroMatrix
#guard (DenseMatrix.homogeneousKernelBasis zeroMatrix).size == 3
#guard kernelBasisChecks noColumns
#guard (DenseMatrix.homogeneousKernelBasis noColumns).size == 0
#guard kernelBasisChecks needsSwap
#guard (DenseMatrix.homogeneousKernelBasis needsSwap).size == 1
#guard kernelBasisChecks tall
#guard (DenseMatrix.homogeneousKernelBasis tall).size == 0

end LinearAlgebra.Dense

end CompPolyTests
