/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.Basic

/-!
# Dense Row Operations

Executable row operations and Gauss-Jordan reduction for row-major matrices.
-/

namespace CompPoly

namespace DenseMatrix

variable {F : Type*}

/-- Result of row reduction, retaining pivot columns in row order. -/
structure RrefResult (F : Type*) [Zero F] where
  matrix : DenseMatrix F
  pivots : Array Nat

/-- Swap two rows. -/
def swapRows [Zero F] (M : DenseMatrix F) (rowA rowB : Nat) : DenseMatrix F :=
  if rowA = rowB then
    M
  else
    { M with data := Id.run do
        let mut data := M.data
        for col in [0:M.cols] do
          let a := M.get rowA col
          let b := M.get rowB col
          data := setD data (M.index rowA col) b
          data := setD data (M.index rowB col) a
        pure data }

/-- Scale one row by a field element. -/
def scaleRow [Field F] (M : DenseMatrix F) (row : Nat) (factor : F) :
    DenseMatrix F :=
  { M with data := Id.run do
      let mut data := M.data
      for col in [0:M.cols] do
        data := setD data (M.index row col) (factor * M.get row col)
      pure data }

/-- Add `factor` times `source` row to `target` row. -/
def addScaledRow [Field F] (M : DenseMatrix F) (target source : Nat)
    (factor : F) : DenseMatrix F :=
  { M with data := Id.run do
      let mut data := M.data
      for col in [0:M.cols] do
        data := setD data (M.index target col)
          (M.get target col + factor * M.get source col)
      pure data }

/-- Find a pivot row at or below `startRow` in column `col`. -/
def findPivotRow [Zero F] [BEq F] (M : DenseMatrix F)
    (startRow col : Nat) : Option Nat :=
  Id.run do
    let mut out : Option Nat := none
    for row in [startRow:M.rows] do
      if out.isNone && !(M.get row col == 0) then
        out := some row
    pure out

/-- Normalize the pivot row and clear the pivot column in every other row. -/
def normalizeAndEliminate [Field F] [BEq F] (M : DenseMatrix F)
    (pivotRow pivotCol : Nat) : DenseMatrix F :=
  let pivot := M.get pivotRow pivotCol
  if pivot == 0 then
    M
  else
    let normalized := scaleRow M pivotRow pivot⁻¹
    Id.run do
      let mut out := normalized
      for row in [0:normalized.rows] do
        if row != pivotRow then
          out := addScaledRow out row pivotRow (-(out.get row pivotCol))
      pure out

/-- Fuel-bounded Gauss-Jordan reduction. -/
def rrefLoop [Field F] [BEq F] :
    Nat -> Nat -> Nat -> DenseMatrix F -> Array Nat -> RrefResult F
  | 0, _col, _row, M, pivots => { matrix := M, pivots := pivots }
  | fuel + 1, col, row, M, pivots =>
      if col < M.cols && row < M.rows then
        match findPivotRow M row col with
        | none => rrefLoop fuel (col + 1) row M pivots
        | some pivotRow =>
            let swapped := swapRows M pivotRow row
            let reduced := normalizeAndEliminate swapped row col
            rrefLoop fuel (col + 1) (row + 1) reduced (pivots.push col)
      else
        { matrix := M, pivots := pivots }

/-- Reduced row-echelon form with pivot-column metadata. -/
def rref [Field F] [BEq F] (M : DenseMatrix F) : RrefResult F :=
  rrefLoop (M.cols + 1) 0 0 M #[]

end DenseMatrix

end CompPoly
