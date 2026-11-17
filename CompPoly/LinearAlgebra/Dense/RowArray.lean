/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.LinearAlgebra.Dense.Kernel

/-!
# Row-Array Homogeneous Kernels

Gauss-Jordan reduction and homogeneous-kernel extraction for a matrix stored as
an array of rows, `Array (Array F)`, with the column count passed separately.
Rows may be ragged; missing entries read as zero.

The algorithm performs the same pivot search, swap, normalization, and
elimination as `DenseMatrix.rref`, and the kernel basis is read off the free
columns exactly as in `DenseMatrix.homogeneousKernelBasis`.
Correctness is in `CompPoly.LinearAlgebra.Dense.RowArrayCorrectness`.
-/

@[expose] public section

namespace CompPoly

namespace DenseMatrix

variable {F : Type*}

/-- The rows of a dense matrix as a row array, each of width `M.cols`. -/
def toRows [Zero F] (M : DenseMatrix F) : Array (Array F) :=
  Array.ofFn fun i : Fin M.rows ↦ Array.ofFn fun j : Fin M.cols ↦ M.get i j

variable [Field F] [BEq F]

/-- Swap two scalar rows in a row-array matrix. -/
def swapScalarRows (rows : Array (Array F)) (rowA rowB : Nat) :
    Array (Array F) :=
  let a := rows.getD rowA #[]
  let b := rows.getD rowB #[]
  (rows.setIfInBounds rowA b).setIfInBounds rowB a

/-- Find a nonzero pivot row at or below `startRow` in column `col`. -/
def findScalarPivotRow (rows : Array (Array F)) (startRow col : Nat) :
    Option Nat :=
  (List.range' startRow (rows.size - startRow)).find? fun row ↦
    (rows.getD row #[]).getD col 0 != 0

/-- Scale a scalar row so that column `pivotCol` becomes one. -/
def normalizeScalarRow (row : Array F) (pivotCol : Nat) : Array F :=
  let pivot := row.getD pivotCol 0
  if pivot == 0 then
    row
  else
    row.map fun x ↦ x / pivot

/-- Add `factor * source` to `target`, using zero defaults for ragged rows. -/
def addScaledScalarRow (target source : Array F) (factor : F) : Array F :=
  (List.range (max target.size source.size)).map
    (fun col ↦ target.getD col 0 + factor * source.getD col 0) |>.toArray

/-- Normalize one pivot row and clear the pivot column in all other rows. -/
def normalizeAndEliminateScalarRows (rows : Array (Array F))
    (pivotRow pivotCol : Nat) : Array (Array F) :=
  let pivot := (rows.getD pivotRow #[]).getD pivotCol 0
  if pivot == 0 then
    rows
  else
    let pivotVector := normalizeScalarRow (rows.getD pivotRow #[]) pivotCol
    let rows := rows.setIfInBounds pivotRow pivotVector
    (List.range rows.size).foldl
      (fun rows row ↦
        if row == pivotRow then
          rows
        else
          let factor := -((rows.getD row #[]).getD pivotCol 0)
          if factor == 0 then
            rows
          else
            rows.setIfInBounds row
              (addScaledScalarRow (rows.getD row #[]) pivotVector factor))
      rows

/-- RREF result for a scalar row-array matrix. -/
structure ScalarRrefResult where
  rows : Array (Array F)
  pivots : Array Nat

/-- Fuel-bounded row-array RREF for tiny scalar coefficient matrices. -/
def scalarRrefRowsLoop (cols : Nat) :
    Nat → Nat → Nat → Array (Array F) → Array Nat → ScalarRrefResult (F := F)
  | 0, _col, _row, rows, pivots => { rows := rows, pivots := pivots }
  | fuel + 1, col, row, rows, pivots =>
      if col >= cols || row >= rows.size then
        { rows := rows, pivots := pivots }
      else
        match findScalarPivotRow rows row col with
        | none => scalarRrefRowsLoop cols fuel (col + 1) row rows pivots
        | some pivotRow =>
            let swapped := swapScalarRows rows pivotRow row
            let reduced := normalizeAndEliminateScalarRows swapped row col
            scalarRrefRowsLoop cols fuel (col + 1) (row + 1) reduced
              (pivots.push col)

/-- Row-array RREF for tiny scalar coefficient matrices. -/
def scalarRrefRows (rows : Array (Array F)) (cols : Nat) :
    ScalarRrefResult (F := F) :=
  scalarRrefRowsLoop cols (cols + 1) 0 0 rows #[]

/-- Kernel basis vector for one free column of a row-array RREF matrix. -/
def basisVectorForFreeColumnRows (rows : Array (Array F))
    (pivots : Array Nat) (cols free : Nat) : Array F :=
  Array.ofFn fun i : Fin cols ↦
    if i.val == free then
      1
    else
      match pivotRowOfColumn? pivots i.val with
      | none => 0
      | some row => -((rows.getD row #[]).getD free 0)

/-- Homogeneous scalar-kernel basis for a row-array matrix. -/
def homogeneousKernelBasisRows (rows : Array (Array F)) (cols : Nat) :
    Array (Array F) :=
  let R := scalarRrefRows rows cols
  (freeColumns cols R.pivots).map
    (basisVectorForFreeColumnRows R.rows R.pivots cols)

end DenseMatrix

end CompPoly
