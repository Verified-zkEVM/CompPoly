/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.Kernel

/-!
# In-Place Dense Homogeneous Kernels

A memory-efficient executable variant of the dense Gauss-Jordan homogeneous-kernel
backend.

The functions in `RowOps.lean` and `Kernel.lean` thread a whole `DenseMatrix`
structure through every row operation. Because `scaleRow`/`addScaledRow`/`swapRows`
read the matrix through `M.get` while the structure `M` is still live, the backing
`Array` is multiply-referenced at the first `setD`, so `Array.setIfInBounds` copies
the entire array on every row-operation call. Gauss-Jordan elimination performs
`Θ(rows)` row operations per pivot and `Θ(min rows cols)` pivots, so the copies turn
an `O(n³)` algorithm into `O(n⁴)` work plus `Θ(n⁴)` words of short-lived allocation.

This module performs the same arithmetic, in the same order, threading a bare
`Array F` (with the dimensions carried as separate `Nat` arguments) through the
reduction. The array is uniquely referenced as it flows from one operation to the
next, so `setIfInBounds` mutates in place after at most one fork from a shared input.
The reduced matrix and pivot data are bit-for-bit identical to `rref`, so the
extracted witnesses agree with `homogeneousWitness`.

The free-column witness extraction (`freeColumns`, `basisVectorForFreeColumn`) is
cheap and shared verbatim with `Kernel.lean`.
-/

namespace CompPoly

namespace DenseMatrix

variable {F : Type*}

/-- Swap rows `rowA` and `rowB` of a width-`cols` row-major array, in place. -/
def swapRowsData [Zero F] (cols rowA rowB : Nat) (data : Array F) : Array F :=
  if rowA = rowB then
    data
  else
    Id.run do
      let mut data := data
      for col in [0:cols] do
        let ia := rowA * cols + col
        let ib := rowB * cols + col
        let a := data.getD ia 0
        let b := data.getD ib 0
        data := setD data ia b
        data := setD data ib a
      pure data

/-- Scale row `row` of a width-`cols` row-major array by `factor`, in place. -/
def scaleRowData [Field F] (cols row : Nat) (factor : F) (data : Array F) :
    Array F :=
  Id.run do
    let mut data := data
    for col in [0:cols] do
      let idx := row * cols + col
      data := setD data idx (factor * data.getD idx 0)
    pure data

/-- Add `factor` times row `source` to row `target` (with `target ≠ source`), in
place. -/
def addScaledRowData [Field F] (cols target source : Nat) (factor : F)
    (data : Array F) : Array F :=
  Id.run do
    let mut data := data
    for col in [0:cols] do
      let ti := target * cols + col
      let si := source * cols + col
      data := setD data ti (data.getD ti 0 + factor * data.getD si 0)
    pure data

/-- Find a pivot row at or below `startRow` in column `col`. -/
def findPivotRowData [Zero F] [BEq F] (rows cols startRow col : Nat)
    (data : Array F) : Option Nat :=
  Id.run do
    let mut out : Option Nat := none
    for row in [startRow:rows] do
      if out.isNone && !(data.getD (row * cols + col) 0 == 0) then
        out := some row
    pure out

/-- Normalize the pivot row and clear the pivot column in every other row, in
place. -/
def normalizeAndEliminateData [Field F] [BEq F] (rows cols pivotRow pivotCol : Nat)
    (data : Array F) : Array F :=
  let pivot := data.getD (pivotRow * cols + pivotCol) 0
  if pivot == 0 then
    data
  else
    Id.run do
      let mut data := scaleRowData cols pivotRow pivot⁻¹ data
      for row in [0:rows] do
        if row != pivotRow then
          let factor := -(data.getD (row * cols + pivotCol) 0)
          data := addScaledRowData cols row pivotRow factor data
      pure data

/-- Fuel-bounded Gauss-Jordan reduction over a bare row-major array. -/
def rrefLoopData [Field F] [BEq F] :
    Nat → Nat → Nat → Nat → Nat → Array F → Array Nat → Array F × Array Nat
  | 0, _rows, _cols, _col, _row, data, pivots => (data, pivots)
  | fuel + 1, rows, cols, col, row, data, pivots =>
      if col < cols && row < rows then
        match findPivotRowData rows cols row col data with
        | none => rrefLoopData fuel rows cols (col + 1) row data pivots
        | some pivotRow =>
            let data := swapRowsData cols pivotRow row data
            let data := normalizeAndEliminateData rows cols row col data
            rrefLoopData fuel rows cols (col + 1) (row + 1) data (pivots.push col)
      else
        (data, pivots)

/-- Reduced row-echelon form with pivot-column metadata, computed in place.

This destructures `M` so the backing array is owned by the reduction loop rather
than aliased through the structure, which is what lets `setIfInBounds` mutate in
place. The result equals `rref M`. -/
def rrefInPlace [Field F] [BEq F] (M : DenseMatrix F) : RrefResult F :=
  match M with
  | { rows := rows, cols := cols, data := data } =>
      let (data, pivots) := rrefLoopData (cols + 1) rows cols 0 0 data #[]
      { matrix := { rows := rows, cols := cols, data := data }, pivots := pivots }

/-- Homogeneous kernel basis extracted from the in-place RREF free columns. -/
def homogeneousKernelBasisInPlace [Field F] [BEq F] (M : DenseMatrix F) :
    Array (Array F) :=
  let R := rrefInPlace M
  (freeColumns R.matrix.cols R.pivots).map
    (basisVectorForFreeColumn R.matrix R.pivots)

/-- One nonzero homogeneous-kernel witness via in-place reduction, if a free
column exists. Output-identical to `homogeneousWitness`. -/
def homogeneousWitnessInPlace [Field F] [BEq F] (M : DenseMatrix F) :
    Option (Array F) :=
  let basis := homogeneousKernelBasisInPlace M
  if basis.size = 0 then none else some (basis.getD 0 #[])

end DenseMatrix

end CompPoly
