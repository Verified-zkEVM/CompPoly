/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import Mathlib.Algebra.Field.Defs

/-!
# Dense Row-Major Matrices

Basic dense row-major matrix storage, indexing, and homogeneous-system
predicates.
-/

namespace CompPoly

namespace DenseMatrix

/-- Set an array entry when the index is in bounds; otherwise leave the array unchanged. -/
def setD (xs : Array alpha) (i : Nat) (a : alpha) : Array alpha :=
  xs.setIfInBounds i a

end DenseMatrix

/-- A dense row-major matrix with dimensions stored explicitly. -/
structure DenseMatrix (F : Type*) [Zero F] where
  rows : Nat
  cols : Nat
  data : Array F

namespace DenseMatrix

variable {F : Type*}

/-- A dense matrix stores exactly one row-major entry for every matrix coordinate. -/
def WellFormed [Zero F] (M : DenseMatrix F) : Prop :=
  M.data.size = M.rows * M.cols

/-- Row-major index for the matrix entry `(row, col)`. -/
def index [Zero F] (M : DenseMatrix F) (row col : Nat) : Nat :=
  row * M.cols + col

/-- Read a matrix entry, returning zero outside the stored data. -/
def get [Zero F] (M : DenseMatrix F) (row col : Nat) : F :=
  M.data.getD (M.index row col) 0

/-- Replace a matrix entry when the row-major slot is stored. -/
def set [Zero F] (M : DenseMatrix F) (row col : Nat) (value : F) : DenseMatrix F :=
  { M with data := setD M.data (M.index row col) value }

/-- Construct a dense matrix from an entry function. -/
def ofFn [Zero F] (rows cols : Nat) (f : Nat -> Nat -> F) : DenseMatrix F :=
  { rows := rows
    cols := cols
    data := Array.ofFn fun i : Fin (rows * cols) ↦
      f (i.val / cols) (i.val % cols) }

/-- Dot product of one matrix row with a vector. -/
def dotRow [Semiring F] (M : DenseMatrix F) (row : Nat) (v : Array F) : F :=
  (List.range M.cols).foldl
    (fun acc col ↦ acc + M.get row col * v.getD col 0)
    0

/-- Matrix-vector product. -/
def mulVec [Semiring F] (M : DenseMatrix F) (v : Array F) : Array F :=
  ((List.range M.rows).map fun row ↦ dotRow M row v).toArray

/-- A vector has the same width as the matrix column count. -/
def VectorWidth [Zero F] (M : DenseMatrix F) (v : Array F) : Prop :=
  v.size = M.cols

/-- A vector has at least one nonzero entry. -/
def NonzeroVector [Zero F] (v : Array F) : Prop :=
  exists i, i < v.size /\ v.getD i 0 ≠ 0

/-- A vector solves the homogeneous system represented by `M`. -/
def IsHomogeneousSolution [Semiring F] (M : DenseMatrix F) (v : Array F) : Prop :=
  forall row, row < M.rows -> dotRow M row v = 0

end DenseMatrix

end CompPoly
