/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Degree

/-!
# Shifted Degrees for Polynomial Rows
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*}

/-- Shifted leading term metadata for a nonzero row. -/
structure ShiftedLeadingTerm (F : Type*) where
  position : Nat
  degree : Nat
  shiftedDegree : Nat
  coeff : F
deriving Repr

private def maxOption : Option Nat → Nat → Option Nat
  | none, n => some n
  | some m, n => some (max m n)

/-- Shifted degree of one row entry. Zero entries have no degree. -/
def shiftedEntryDegree? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) (j : Nat) : Option Nat :=
  let p := rowGet row j
  if p == 0 then none else some (p.natDegree + shift.getD j 0)

/-- Shifted degree of a row, with `none` exactly for zero rows. -/
def rowShiftedDegree? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) : Option Nat :=
  (List.range row.size).foldl
    (fun acc j ↦
      match shiftedEntryDegree? row shift j with
      | none => acc
      | some d => maxOption acc d)
    none

/-- Shifted leading position of a nonzero row. Ties use the largest column index. -/
def rowShiftedLeadingPosition? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) : Option Nat :=
  match rowShiftedDegree? row shift with
  | none => none
  | some d =>
      (List.range row.size).reverse.find? fun j ↦
        match shiftedEntryDegree? row shift j with
        | some dj => dj == d
        | none => false

/-- Shifted leading term metadata for a nonzero row. -/
def rowShiftedLeadingTerm? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) :
    Option (ShiftedLeadingTerm F) :=
  match rowShiftedDegree? row shift, rowShiftedLeadingPosition? row shift with
  | some shiftedDegree, some j =>
      let p := rowGet row j
      if p == 0 then
        none
      else
        some
          { position := j
            degree := p.natDegree
            shiftedDegree := shiftedDegree
            coeff := p.coeff p.natDegree }
  | _, _ => none

/-- Nonzero rows are exactly the rows with a shifted degree. -/
theorem rowShiftedDegree?_eq_none_iff [Zero F] [BEq F] [LawfulBEq F]
    {row : PolynomialRow F} {shift : Array Nat} :
    rowShiftedDegree? row shift = none ↔ RowIsZero row := by
  sorry

/-- A shifted weak-Popov matrix has distinct leading positions among nonzero rows. -/
def ShiftedWeakPopov [Zero F] [BEq F]
    (M : PolynomialMatrix F) (shift : Array Nat) : Prop :=
  ∀ i j,
    i < M.size →
    j < M.size →
    i ≠ j →
    rowShiftedLeadingPosition? (M.getD i #[]) shift ≠ none →
    rowShiftedLeadingPosition? (M.getD j #[]) shift ≠ none →
      rowShiftedLeadingPosition? (M.getD i #[]) shift ≠
        rowShiftedLeadingPosition? (M.getD j #[]) shift

end PolynomialMatrix

end CompPoly
