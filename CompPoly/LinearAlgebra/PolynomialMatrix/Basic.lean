/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Basic

/-!
# Polynomial Rows and Matrices

Minimal row-oriented polynomial-matrix infrastructure for shifted row reduction.
-/

namespace CompPoly

/-- A polynomial row over `F[X]`. -/
abbrev PolynomialRow (F : Type*) [Zero F] := Array (CPolynomial F)

/-- A polynomial matrix over `F[X]`, stored as an array of rows. -/
abbrev PolynomialMatrix (F : Type*) [Zero F] := Array (PolynomialRow F)

/-- Runtime rectangular shape of a polynomial matrix. -/
structure PolynomialMatrixShape where
  rows : Nat
  width : Nat
deriving Repr, BEq, DecidableEq

namespace PolynomialMatrix

variable {F : Type*}

/-- Width of a row. -/
def RowWidth [Zero F] (row : PolynomialRow F) : Nat :=
  row.size

/-- Matrix width, using the first row and width `0` for an empty matrix. -/
def MatrixWidth [Zero F] (M : PolynomialMatrix F) : Nat :=
  match M[0]? with
  | none => 0
  | some row => row.size

/-- Runtime matrix shape. -/
def MatrixShape [Zero F] (M : PolynomialMatrix F) : PolynomialMatrixShape :=
  { rows := M.size, width := MatrixWidth M }

/-- Matrix rows as a list, for membership statements. -/
def MatrixRows [Zero F] (M : PolynomialMatrix F) : List (PolynomialRow F) :=
  M.toList

/-- A matrix is rectangular when every row has the matrix width. -/
def WellFormed [Zero F] (M : PolynomialMatrix F) : Prop :=
  ∀ row, row ∈ MatrixRows M → row.size = MatrixWidth M

/-- Read a row coefficient with zero default. -/
def rowGet [Zero F] (row : PolynomialRow F) (j : Nat) : CPolynomial F :=
  row.getD j 0

/-- The zero row of a fixed width. -/
def zeroRow [Zero F] (width : Nat) : PolynomialRow F :=
  Array.replicate width 0

/-- Pointwise row addition over the maximum input width. -/
def rowAdd [Semiring F] [BEq F] [LawfulBEq F]
    (a b : PolynomialRow F) : PolynomialRow F :=
  (List.range (max a.size b.size)).map
    (fun j ↦ rowGet a j + rowGet b j) |>.toArray

/-- Pointwise row negation. -/
def rowNeg [Ring F] [BEq F] [LawfulBEq F] (row : PolynomialRow F) :
    PolynomialRow F :=
  row.map fun p ↦ -p

/-- Pointwise row subtraction over the maximum input width. -/
def rowSub [Ring F] [BEq F] [LawfulBEq F]
    (a b : PolynomialRow F) : PolynomialRow F :=
  rowAdd a (rowNeg b)

/-- Multiply a row by a univariate polynomial. -/
def rowScalePolynomial [Semiring F] [BEq F] [LawfulBEq F]
    (c : CPolynomial F) (row : PolynomialRow F) : PolynomialRow F :=
  row.map fun p ↦ c * p

/-- Multiply a row by `c * X^d`. -/
def rowScaleMonomial [Semiring F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (c : F) (d : Nat) (row : PolynomialRow F) : PolynomialRow F :=
  rowScalePolynomial (CPolynomial.monomial d c) row

/-- Replace a row if the index is in bounds. -/
def replaceRow [Zero F] (M : PolynomialMatrix F) (idx : Nat) (row : PolynomialRow F) :
    PolynomialMatrix F :=
  M.setIfInBounds idx row

end PolynomialMatrix

end CompPoly
