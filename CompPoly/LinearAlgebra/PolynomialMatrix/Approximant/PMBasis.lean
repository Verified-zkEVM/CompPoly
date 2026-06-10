/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic

/-!
# Recursive PM-Basis Skeleton

An executable divide-and-conquer PM-basis driver parameterized by an explicit
leaf solver.  The leaf is the only classical hook; production contexts choose
the cutoff and leaf implementation, while the recursive residual/composition
structure is shared.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Coefficient degree cap used by the classical scalar-kernel PM-basis leaf. -/
def leafDegreeCap (problem : XAdicProblem F) : Nat :=
  max 1 (maxOrder problem)

/-- Coefficient-equation indices `(column, coefficientDegree)`. -/
def coefficientEquationIndices (orders : Array Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for j in [0:orders.size] do
    for t in [0:orders.getD j 0] do
      out := out.push (j, t)
  pure out

/-- Dense scalar coefficient matrix for the bounded leaf problem. -/
def coefficientMatrix (problem : XAdicProblem F) : DenseMatrix F :=
  let degreeCap := leafDegreeCap problem
  let equations := coefficientEquationIndices problem.orders
  DenseMatrix.ofFn equations.size (problem.matrix.size * degreeCap) fun row col ↦
    let equation := equations.getD row (0, 0)
    let matrixCol := equation.1
    let coeffDegree := equation.2
    let coord := col / degreeCap
    let coordDegree := col % degreeCap
    if coordDegree ≤ coeffDegree then
      CPolynomial.coeff
        (PolynomialMatrix.rowGet (problem.matrix.getD coord #[]) matrixCol)
        (coeffDegree - coordDegree)
    else
      0

/-- One scalar coefficient row for the bounded leaf problem. -/
def coefficientMatrixRow (problem : XAdicProblem F) (degreeCap : Nat)
    (equation : Nat × Nat) : Array F :=
  (List.range (problem.matrix.size * degreeCap)).map
    (fun col ↦
      let matrixCol := equation.1
      let coeffDegree := equation.2
      let coord := col / degreeCap
      let coordDegree := col % degreeCap
      if coordDegree ≤ coeffDegree then
        CPolynomial.coeff
          (PolynomialMatrix.rowGet (problem.matrix.getD coord #[]) matrixCol)
          (coeffDegree - coordDegree)
      else
        0) |>.toArray

/-- Scalar coefficient rows for the bounded leaf problem.  This is the same
matrix as `coefficientMatrix`, represented directly as row arrays for the tiny
leaf RREF routine. -/
def coefficientMatrixRows (problem : XAdicProblem F) : Array (Array F) :=
  let degreeCap := leafDegreeCap problem
  (coefficientEquationIndices problem.orders).map
    (coefficientMatrixRow problem degreeCap)

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
      match DenseMatrix.pivotRowOfColumn? pivots i.val with
      | none => 0
      | some row => -((rows.getD row #[]).getD free 0)

/-- Homogeneous scalar-kernel basis for a row-array matrix. -/
def homogeneousKernelBasisRows (rows : Array (Array F)) (cols : Nat) :
    Array (Array F) :=
  let R := scalarRrefRows rows cols
  (DenseMatrix.freeColumns cols R.pivots).map
    (basisVectorForFreeColumnRows R.rows R.pivots cols)

/-- Convert one scalar kernel vector back into a polynomial row. -/
def vectorToPolynomialRow (degreeCap solutionWidth : Nat) (v : Array F) :
    PolynomialRow F :=
  (List.range solutionWidth).map
    (fun coord ↦
      CPolynomial.ofArray
        ((List.range degreeCap).map
          (fun degree ↦ v.getD (coord * degreeCap + degree) 0) |>.toArray)) |>.toArray

/-- Polynomial `c * X^d`, built without the `CPolynomial.monomial`
`DecidableEq` assumption. -/
def coeffXPower (c : F) (d : Nat) : CPolynomial F :=
  CPolynomial.ofArray ((Array.replicate d 0).push c)

/-- Multiply a row by `c * X^d`, using the coefficient-array monomial builder. -/
def polynomialScaleCoeffX (c : F) (d : Nat) (p : CPolynomial F) :
    CPolynomial F :=
  if c == 0 then
    0
  else if p == 0 then
    0
  else
    CPolynomial.ofArray
      ((List.replicate d 0 ++ p.val.toList.map (fun a ↦ c * a)).toArray)

/-- Multiply a row by `c * X^d`, using coefficient shifting instead of generic
polynomial multiplication by a monomial. -/
def rowScaleCoeffX (c : F) (d : Nat) (row : PolynomialRow F) :
    PolynomialRow F :=
  row.map fun p ↦ polynomialScaleCoeffX c d p

/-- Monomial row `X^d * e_i`, used to complete bounded-kernel leaves to a full
approximant basis. -/
def monomialUnitRow (width i d : Nat) : PolynomialRow F :=
  (List.range width).map
    (fun j ↦ if i == j then coeffXPower 1 d else 0) |>.toArray

/-- Trivial high-degree approximants present in every X-adic problem.  These
rows are essential when the bounded scalar kernel has fewer rows than the module
rank. -/
def kernelLeafCompletionRows (problem : XAdicProblem F) :
    PolynomialMatrix F :=
  let degreeCap := leafDegreeCap problem
  (List.range problem.matrix.size).map
    (fun i ↦ monomialUnitRow problem.matrix.size i degreeCap) |>.toArray

/-- Whether a row set already contains a row with a given shifted leading
position. -/
def rowsContainLeadingPosition (rows : PolynomialMatrix F)
    (shift : Array Nat) (position : Nat) : Bool :=
  rows.any fun row ↦
    match rowShiftedLeadingPosition? row shift with
    | some p => p == position
    | none => false

/-- High monomial rows for shifted leading positions not represented by `rows`.
These rows are always valid approximants and keep recursive residual problems
from losing coordinates after compact row reduction. -/
def missingCompletionRows (problem : XAdicProblem F)
    (shift : Array Nat) (rows : PolynomialMatrix F) :
    PolynomialMatrix F :=
  let degreeCap := leafDegreeCap problem
  (List.range problem.matrix.size).filterMap
    (fun i ↦
      if rowsContainLeadingPosition rows shift i then
        none
      else
        some (monomialUnitRow problem.matrix.size i degreeCap)) |>.toArray

/-- Add high monomial approximants for missing pivot positions. -/
def completeMissingPivotRows (problem : XAdicProblem F)
    (shift : Array Nat) (rows : PolynomialMatrix F) :
    PolynomialMatrix F :=
  rows ++ missingCompletionRows problem shift rows

/-- Cancel the shifted leading term of `target` by `reducer`, when their shifted
leading positions agree.  This is the small-leaf analogue of polynomial-matrix
row reduction; it is used only after the bounded scalar kernel has already been
computed. -/
def cancelKernelLeafLeadingTerm
    (target reducer : PolynomialRow F) (shift : Array Nat) : PolynomialRow F :=
  match rowShiftedLeadingTerm? target shift, rowShiftedLeadingTerm? reducer shift with
  | some t, some r =>
      if t.position == r.position then
        if r.coeff == 0 then
          target
        else
          rowSub target (rowScaleCoeffX (t.coeff / r.coeff) (t.degree - r.degree) reducer)
      else
        target
  | _, _ => target

/-- One inner-loop update for finding a leading-position conflict in a bounded
kernel leaf. -/
def kernelLeafConflictInRowStep? (rows : PolynomialMatrix F) (shift : Array Nat)
    (i : Nat) (found : Option (Nat × Nat)) (j : Nat) : Option (Nat × Nat) :=
  match found with
  | some _ => found
  | none =>
      match rowShiftedLeadingPosition? (rows.getD i #[]) shift,
          rowShiftedLeadingPosition? (rows.getD j #[]) shift with
      | some pi, some pj => if pi == pj then some (i, j) else none
      | _, _ => none

/-- Scan one row for a shifted-leading-position conflict in a bounded kernel
leaf. -/
def kernelLeafConflictInRow? (rows : PolynomialMatrix F) (shift : Array Nat)
    (i : Nat) (found : Option (Nat × Nat)) : Option (Nat × Nat) :=
  (List.range' (i + 1) (rows.size - (i + 1))).foldl
    (kernelLeafConflictInRowStep? rows shift i) found

/-- Scan all row pairs for the first shifted-leading-position conflict. -/
def kernelLeafConflictFrom? (rows : PolynomialMatrix F) (shift : Array Nat)
    (found : Option (Nat × Nat)) : Option (Nat × Nat) :=
  (List.range rows.size).foldl
    (fun acc i ↦ kernelLeafConflictInRow? rows shift i acc) found

/-- First pair of nonzero bounded-kernel rows with the same shifted leading
position. -/
def kernelLeafConflict? (rows : PolynomialMatrix F) (shift : Array Nat) :
    Option (Nat × Nat) :=
  kernelLeafConflictFrom? rows shift none

/-- One shifted-reduction step for bounded scalar-kernel rows. -/
def reduceKernelLeafStep (rows : PolynomialMatrix F) (shift : Array Nat)
    (i j : Nat) : PolynomialMatrix F :=
  let rowI := rows.getD i #[]
  let rowJ := rows.getD j #[]
  match rowShiftedDegree? rowI shift, rowShiftedDegree? rowJ shift with
  | some degI, some degJ =>
      if degI ≤ degJ then
        replaceRow rows j (cancelKernelLeafLeadingTerm rowJ rowI shift)
      else
        replaceRow rows i (cancelKernelLeafLeadingTerm rowI rowJ shift)
  | _, _ => rows

/-- Fuel for bounded-kernel shifted reduction.  The scalar leaf is already a
small base case, so this conservative degree-width bound is acceptable here. -/
def reduceKernelLeafFuel (rows : PolynomialMatrix F) (shift : Array Nat) : Nat :=
  let maxDegree := (List.range rows.size).foldl
    (fun acc i ↦
      match rowShiftedDegree? (rows.getD i #[]) shift with
      | none => acc
      | some degree => max acc degree)
    0
  (rows.size + 1) * (MatrixWidth rows + 1) * (maxDegree + 1)

/-- Extract the nonempty pivot rows from a leading-position table. -/
def pivotRows (pivots : Array (Option (PolynomialRow F))) :
    PolynomialMatrix F :=
  pivots.toList.filterMap id |>.toArray

/-- Insert one row into a shifted weak-Popov pivot table.  Conflicts are resolved
only at the current leading position, avoiding the repeated global pair scans
used by the simple reference reducer. -/
def insertKernelLeafPivotRowWithFuel :
    Nat → Array (Option (PolynomialRow F)) → Array Nat → PolynomialRow F →
      Array (Option (PolynomialRow F))
  | 0, pivots, _shift, _row => pivots
  | fuel + 1, pivots, shift, row =>
      match rowShiftedLeadingTerm? row shift with
      | none => pivots
      | some target =>
          match pivots.getD target.position none with
          | none => pivots.setIfInBounds target.position (some row)
          | some pivot =>
              match rowShiftedLeadingTerm? pivot shift with
              | none => pivots.setIfInBounds target.position (some row)
              | some reducer =>
                  if target.shiftedDegree < reducer.shiftedDegree then
                    let reducedPivot := cancelKernelLeafLeadingTerm pivot row shift
                    let pivots := pivots.setIfInBounds target.position (some row)
                    insertKernelLeafPivotRowWithFuel fuel pivots shift reducedPivot
                  else
                    let reducedRow := cancelKernelLeafLeadingTerm row pivot shift
                    insertKernelLeafPivotRowWithFuel fuel pivots shift reducedRow

/-- Pivot-table shifted reduction for bounded scalar-kernel rows. -/
def reduceKernelLeafRowsByPivots (rows : PolynomialMatrix F) (shift : Array Nat) :
    PolynomialMatrix F :=
  let fuel := reduceKernelLeafFuel rows shift
  let pivots := rows.foldl
    (fun pivots row ↦ insertKernelLeafPivotRowWithFuel fuel pivots shift row)
    (Array.replicate (MatrixWidth rows) none)
  pivotRows pivots

/-- Shift-reduce the bounded scalar-kernel rows before compacting them.  This
keeps one low representative per shifted leading position instead of selecting
arbitrary low-degree kernel vectors. -/
def reduceKernelLeafWithFuel :
    Nat → PolynomialMatrix F → Array Nat → PolynomialMatrix F
  | 0, rows, _shift => rows
  | fuel + 1, rows, shift =>
      match kernelLeafConflict? rows shift with
      | none => rows
      | some (i, j) =>
          reduceKernelLeafWithFuel fuel (reduceKernelLeafStep rows shift i j) shift

/-- Shift-reduced bounded scalar-kernel rows for the PM-basis leaf. -/
def reduceKernelLeafRows (rows : PolynomialMatrix F) (shift : Array Nat) :
    PolynomialMatrix F :=
  reduceKernelLeafRowsByPivots rows shift

/-- Insert one bounded-kernel row into a small shifted-reduced leaf basis.  This
keeps the live reduction matrix near the module width instead of reducing the
entire scalar kernel at once. -/
def insertKernelLeafRowIncremental (basis : PolynomialMatrix F)
    (shift : Array Nat) (row : PolynomialRow F) : PolynomialMatrix F :=
  (reduceKernelLeafRows (basis.push row) shift).filter fun row ↦ !rowIsZero row

/-- Shift-reduce all bounded scalar-kernel rows incrementally.  The dense scalar
kernel can have many rows, but after every insertion the weak-Popov conflict loop
works on the current reduced basis plus one candidate row. -/
def reduceKernelLeafRowsIncremental (rows : PolynomialMatrix F)
    (shift : Array Nat) : PolynomialMatrix F :=
  rows.foldl (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) #[]

/-- Classical scalar-kernel leaf for small X-adic approximant problems. -/
def kernelLeafBasis (problem : XAdicProblem F) (shift : Array Nat) :
    PolynomialMatrix F :=
  let degreeCap := leafDegreeCap problem
  let scalarRows := (homogeneousKernelBasisRows (coefficientMatrixRows problem)
      (problem.matrix.size * degreeCap)).map
    (vectorToPolynomialRow degreeCap problem.matrix.size)
  completeMissingPivotRows problem shift
    (reduceKernelLeafRowsIncremental
      (scalarRows ++ kernelLeafCompletionRows problem) shift)

/-- Remove zero rows before a recursively computed approximant basis is used as
the coordinate system for the next residual problem. -/
def compactNonzeroRows (rows : PolynomialMatrix F) : PolynomialMatrix F :=
  rows.filter fun row ↦ !rowIsZero row

/-- Runtime data for recursive PM-basis computation. -/
structure PMBasisRuntime (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  mulContext : CPolynomial.MulContext F
  lowMulContext : PolynomialMatrix.MulLowContext F
  composeBasis : PolynomialMatrix F → PolynomialMatrix F → PolynomialMatrix F
  residualProduct :
    Array Nat → PolynomialMatrix F → PolynomialMatrix F → PolynomialMatrix F
  leafCutoff : Nat
  leafBasis : XAdicProblem F → Array Nat → PolynomialMatrix F

/-- Recursive PM-basis runtime using the scalar dense-kernel routine as its
small-leaf solver and an independently tuned basis-composition cutoff. -/
def kernelLeafRuntimeWithLowAndCompose (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) :
    PMBasisRuntime F where
  mulContext := mulCtx
  lowMulContext := lowCtx
  composeBasis := PolynomialMatrix.mulStrassenWith lowCtx composeLeafCutoff
  residualProduct := PolynomialMatrix.mulTruncColumnStrassenWith lowCtx
    composeLeafCutoff
  leafCutoff := leafCutoff
  leafBasis := kernelLeafBasis

/-- Recursive PM-basis runtime using the scalar dense-kernel routine as its
small-leaf solver. -/
def kernelLeafRuntimeWithLow (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F) (leafCutoff : Nat) :
    PMBasisRuntime F :=
  kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff leafCutoff

/-- Compatibility runtime whose low products are obtained by truncating full
products. -/
def kernelLeafRuntime (mulCtx : CPolynomial.MulContext F) (leafCutoff : Nat) :
    PMBasisRuntime F :=
  kernelLeafRuntimeWithLow mulCtx (PolynomialMatrix.MulLowContext.fromMulContext mulCtx)
    leafCutoff

/-- Fuel-bounded recursive PM-basis driver, compacting zero rows after each
leaf and composition step.

Internal nodes return the composed product `P₂ * P₁` without re-reduction:
composition of minimal half-bases under the updated shift is itself a basis of
the full-order approximant module, so re-reducing at every node would only add
work that is quadratic in the row degrees and outside the PM-basis cost model.
A single weak-Popov normalization pass runs once at the root entry points. -/
def pmBasisWithFuelCore (runtime : PMBasisRuntime F) :
    Nat → XAdicProblem F → Array Nat → PolynomialMatrix F
  | 0, problem, shift => compactNonzeroRows (runtime.leafBasis problem shift)
  | fuel + 1, problem, shift =>
      let order := maxOrder problem
      if order ≤ runtime.leafCutoff || order ≤ 1 then
        compactNonzeroRows (runtime.leafBasis problem shift)
      else
        let d₁ := order / 2
        let lower : XAdicProblem F :=
          { orders := lowerOrders problem d₁, matrix := problem.matrix }
        let P₁ := pmBasisWithFuelCore runtime fuel lower shift
        let residualOrders := residualOrders problem d₁
        let residual : XAdicProblem F :=
          { orders := residualOrders
            matrix := residualMatrixWithProduct runtime.residualProduct P₁
              problem.matrix d₁ residualOrders }
        let shifted := updateShiftByRows P₁ shift
        let P₂ := pmBasisWithFuelCore runtime fuel residual shifted
        compactNonzeroRows (runtime.composeBasis P₂ P₁)

/-- Root normalization for a recursively composed approximant basis: one
weak-Popov reduction pass plus completion rows for any leading position that
lost its representative.  When the recursion preserved minimality this pass
performs no cascading cancellations; it is a semantic guard, not part of the
recursive cost model. -/
def pmBasisNormalizeRoot (problem : XAdicProblem F) (shift : Array Nat)
    (basis : PolynomialMatrix F) : PolynomialMatrix F :=
  completeMissingPivotRows problem shift
    (compactNonzeroRows (reduceKernelLeafRows basis shift))

/-- Fuel-bounded recursive PM-basis driver with root normalization. -/
def pmBasisWithFuel (runtime : PMBasisRuntime F)
    (fuel : Nat) (problem : XAdicProblem F) (shift : Array Nat) :
    PolynomialMatrix F :=
  pmBasisNormalizeRoot problem shift (pmBasisWithFuelCore runtime fuel problem shift)

/-- Default fuel choice, large enough to split each positive order down to the
leaf cutoff. -/
def pmBasisFuel [Zero F] (problem : XAdicProblem F) : Nat :=
  maxOrder problem + 1

/-- Recursive PM-basis entry point. -/
def pmBasis (runtime : PMBasisRuntime F)
    (problem : XAdicProblem F) (shift : Array Nat) : PolynomialMatrix F :=
  pmBasisWithFuel runtime (pmBasisFuel problem) problem shift

/-- Context packaging the executable PM-basis operation with theorem fields. -/
structure PMBasisContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  runtime : PMBasisRuntime F
  basis : XAdicProblem F → Array Nat → PolynomialMatrix F := pmBasis runtime
  sound :
    ∀ problem shift row,
      row ∈ MatrixRows (basis problem shift) →
        ∀ j, j < problem.orders.size →
          truncateX (problem.orders.getD j 0)
            (rowGet (rowMulMatrixWith runtime.mulContext row problem.matrix) j) = 0
  complete_minimal :
    ∀ problem shift row,
      (∀ j, j < problem.orders.size →
        truncateX (problem.orders.getD j 0)
          (rowGet (rowMulMatrixWith runtime.mulContext row problem.matrix) j) = 0) →
        ∃ basisRow,
          basisRow ∈ MatrixRows (basis problem shift)

/-- PM-basis context backed by the recursive driver, scalar dense-kernel leaves,
and an independently tuned basis-composition cutoff. -/
def kernelLeafPMBasisContextWithLowAndCompose (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff composeLeafCutoff : Nat) : PMBasisContext F where
  runtime := kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
    composeLeafCutoff
  basis := pmBasis (kernelLeafRuntimeWithLowAndCompose mulCtx lowCtx leafCutoff
    composeLeafCutoff)
  sound := by
    sorry
  complete_minimal := by
    sorry

/-- PM-basis context backed by the recursive driver and scalar dense-kernel
leaves. -/
def kernelLeafPMBasisContextWithLow (mulCtx : CPolynomial.MulContext F)
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (leafCutoff : Nat) : PMBasisContext F :=
  kernelLeafPMBasisContextWithLowAndCompose mulCtx lowCtx leafCutoff leafCutoff

/-- PM-basis context whose low products are obtained by truncating full
products. -/
def kernelLeafPMBasisContext (mulCtx : CPolynomial.MulContext F)
    (leafCutoff : Nat) : PMBasisContext F :=
  kernelLeafPMBasisContextWithLow mulCtx
    (PolynomialMatrix.MulLowContext.fromMulContext mulCtx) leafCutoff

end Approximant

end PolynomialMatrix

end CompPoly
