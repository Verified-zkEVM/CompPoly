/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.ShiftedReduction

/-!
# Mulders-Storjohann Shifted Row Reduction

Direct executable shifted row reduction over polynomial rows.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- One inner-loop update for shifted-leading-position conflict search. -/
def shiftedLeadingConflictInRowStep?
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    (found : Option (Nat × Nat)) (j : Nat) : Option (Nat × Nat) :=
  match found with
  | some _ => found
  | none =>
      match rowShiftedLeadingPosition? (M.getD i #[]) shift,
          rowShiftedLeadingPosition? (M.getD j #[]) shift with
      | some pi, some pj =>
          if pi == pj then some (i, j) else none
      | _, _ => none

/-- Scan one row index `i` for a shifted-leading-position conflict. -/
def shiftedLeadingConflictInRow?
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    (found : Option (Nat × Nat)) : Option (Nat × Nat) :=
  (List.range' (i + 1) (M.size - (i + 1))).foldl
    (shiftedLeadingConflictInRowStep? M shift i)
    found

/-- One outer-loop update for shifted-leading-position conflict search. -/
def shiftedLeadingConflictFromStep?
    (M : PolynomialMatrix F) (shift : Array Nat)
    (found : Option (Nat × Nat)) (i : Nat) : Option (Nat × Nat) :=
  shiftedLeadingConflictInRow? M shift i found

/-- Scan all row pairs for the first shifted-leading-position conflict. -/
def shiftedLeadingConflictFrom?
    (M : PolynomialMatrix F) (shift : Array Nat)
    (found : Option (Nat × Nat)) : Option (Nat × Nat) :=
  (List.range' 0 M.size).foldl
    (shiftedLeadingConflictFromStep? M shift)
    found

/-- First pair of nonzero rows with the same shifted leading position. -/
def shiftedLeadingConflict? (M : PolynomialMatrix F) (shift : Array Nat) :
    Option (Nat × Nat) :=
  shiftedLeadingConflictFrom? M shift none

/-- Cancel the shifted leading term of `target` using `reducer`, when possible. -/
def cancelShiftedLeadingTerm
    (target reducer : PolynomialRow F) (shift : Array Nat) : PolynomialRow F :=
  match rowShiftedLeadingTerm? target shift, rowShiftedLeadingTerm? reducer shift with
  | some t, some r =>
      if t.position == r.position then
        if r.coeff == 0 then
          target
        else
          rowSub target
            (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer)
      else
        target
  | _, _ => target

/-- One Mulders-Storjohann cancellation step for a chosen conflicting pair. -/
def muldersStorjohannStep
    (M : PolynomialMatrix F) (shift : Array Nat) (i j : Nat) : PolynomialMatrix F :=
  let rowI := M.getD i #[]
  let rowJ := M.getD j #[]
  match rowShiftedDegree? rowI shift, rowShiftedDegree? rowJ shift with
  | some degI, some degJ =>
      if degI ≤ degJ then
        replaceRow M j (cancelShiftedLeadingTerm rowJ rowI shift)
      else
        replaceRow M i (cancelShiftedLeadingTerm rowI rowJ shift)
  | _, _ => M

/-- Fuel-bounded Mulders-Storjohann reduction loop. -/
def muldersStorjohannReduceWithFuel :
    Nat → PolynomialMatrix F → Array Nat → PolynomialMatrix F
  | 0, M, _shift => M
  | fuel + 1, M, shift =>
      match shiftedLeadingConflict? M shift with
      | none => M
      | some (i, j) =>
          muldersStorjohannReduceWithFuel fuel
            (muldersStorjohannStep M shift i j) shift

/-- Insert a natural number into an optional running maximum. -/
def maxOption : Option Nat → Nat → Option Nat
  | none, n => some n
  | some m, n => some (max m n)

/-- Maximum shifted row degree currently visible in a matrix. -/
def matrixShiftedDegree? (M : PolynomialMatrix F) (shift : Array Nat) : Option Nat :=
  (List.range M.size).foldl
    (fun acc i ↦
      match rowShiftedDegree? (M.getD i #[]) shift with
      | none => acc
      | some d => maxOption acc d)
    none

/-- Executable fuel used by the direct reducer. -/
def muldersStorjohannFuel (M : PolynomialMatrix F) (shift : Array Nat) : Nat :=
  let d := (matrixShiftedDegree? M shift).getD 0
  (M.size + 1) * (MatrixWidth M + 1) * (d + 1)

/-- Direct executable Mulders-Storjohann shifted row reducer. -/
def muldersStorjohannReduce (M : PolynomialMatrix F) (shift : Array Nat) :
    PolynomialMatrix F :=
  muldersStorjohannReduceWithFuel (muldersStorjohannFuel M shift) M shift

end PolynomialMatrix

end CompPoly
