/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf

/-!
# Recursive PM-Basis Driver

Runtime data for recursive PM-basis computation, the fuel-bounded
divide-and-conquer driver, root normalization, the `pmBasis` entry point, and
the `PMBasisContext` contract structure.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

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

/-- Monomial completion never returns an empty matrix for problems with at
least one module row: an empty candidate set is completed with one monomial
row per module coordinate. -/
theorem completeMissingPivotRows_size_pos
    (problem : XAdicProblem F) (shift : Array Nat) (rows : PolynomialMatrix F)
    (hsize : 0 < problem.matrix.size) :
    0 < (completeMissingPivotRows problem shift rows).size := by
  rw [completeMissingPivotRows, Array.size_append]
  by_cases hrows : rows.size = 0
  · have hempty : rows = #[] := Array.eq_empty_of_size_eq_zero hrows
    subst hempty
    have hmissing : (missingCompletionRows problem shift (#[] : PolynomialMatrix F)).size =
        problem.matrix.size := by
      simp [missingCompletionRows, rowsContainLeadingPosition]
    omega
  · omega

/-- The root-normalized recursive PM-basis is nonempty for problems with at
least one module row. -/
theorem pmBasisNormalizeRoot_size_pos
    (problem : XAdicProblem F) (shift : Array Nat) (basis : PolynomialMatrix F)
    (hsize : 0 < problem.matrix.size) :
    0 < (pmBasisNormalizeRoot problem shift basis).size := by
  rw [pmBasisNormalizeRoot]
  exact completeMissingPivotRows_size_pos problem shift _ hsize

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
      0 < problem.matrix.size →
      WellFormed problem.matrix →
      (∀ j, j < problem.orders.size →
        truncateX (problem.orders.getD j 0)
          (rowGet (rowMulMatrixWith runtime.mulContext row problem.matrix) j) = 0) →
      rowIsZero row = false →
      row.size ≤ problem.matrix.size →
        ∃ basisRow degree,
          basisRow ∈ MatrixRows (basis problem shift) ∧
          basisRow.size ≤ problem.matrix.size ∧
          rowShiftedDegree? basisRow shift = some degree ∧
          ∀ rowDegree, rowShiftedDegree? row shift = some rowDegree →
            degree ≤ rowDegree

end Approximant

end PolynomialMatrix

end CompPoly
