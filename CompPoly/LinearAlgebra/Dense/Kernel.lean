/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.RowOps

/-!
# Dense Homogeneous Kernels

Executable homogeneous-kernel basis and witness extraction from row-reduced
dense matrices.
-/

namespace CompPoly

namespace DenseMatrix

variable {F : Type*}

/-- Boolean membership test for natural-number arrays. -/
def containsNat (xs : Array Nat) (x : Nat) : Bool :=
  xs.any fun y => y == x

/-- Free columns of a row-reduced matrix. -/
def freeColumns (cols : Nat) (pivots : Array Nat) : Array Nat :=
  ((List.range cols).filter fun col => !(containsNat pivots col)).toArray

/-- Pivot row for a pivot column, if the column is a pivot. -/
def pivotRowOfColumn? (pivots : Array Nat) (col : Nat) : Option Nat :=
  (List.range pivots.size).find? fun row => pivots.getD row 0 == col

/-- Kernel basis vector corresponding to one free column of an RREF matrix. -/
def basisVectorForFreeColumn [Field F] [BEq F] (A : DenseMatrix F)
    (pivots : Array Nat) (free : Nat) : Array F :=
  Array.ofFn fun i : Fin A.cols =>
    if i.val == free then
      1
    else
      match pivotRowOfColumn? pivots i.val with
      | none => 0
      | some row => -(A.get row free)

/-- Homogeneous kernel basis extracted from the RREF free columns. -/
def homogeneousKernelBasis [Field F] [BEq F] (M : DenseMatrix F) :
    Array (Array F) :=
  let R := rref M
  (freeColumns M.cols R.pivots).map
    (basisVectorForFreeColumn R.matrix R.pivots)

/-- One nonzero homogeneous-kernel witness, if a free column exists. -/
def homogeneousWitness [Field F] [BEq F] (M : DenseMatrix F) : Option (Array F) :=
  let basis := homogeneousKernelBasis M
  if basis.size = 0 then none else some (basis.getD 0 #[])

end DenseMatrix

end CompPoly

