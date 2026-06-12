/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Operations

/-!
# X-Adic Approximant Problems

Basic data structures for approximant-basis computations over polynomial
matrices.

## References

* [Beckermann, B., and Labahn, G., *A uniform approach for the fast
    computation of matrix-type Pade approximants*][BL94]
* [Giorgi, P., Jeannerod, C.-P., and Villard, G., *On the complexity of
    polynomial matrix computations*][GJV03]
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*}

/-- A row approximant problem `p * matrix = 0 mod X^orders`. -/
structure XAdicProblem (F : Type*) [Zero F] where
  orders : Array Nat
  matrix : PolynomialMatrix F

/-- Maximum X-adic order in a problem. -/
def maxOrder [Zero F] (problem : XAdicProblem F) : Nat :=
  problem.orders.foldl max 0

/-- Sum of X-adic orders. -/
def totalOrder [Zero F] (problem : XAdicProblem F) : Nat :=
  problem.orders.foldl (fun acc order ↦ acc + order) 0

/-- Truncate every problem order to at most `d`. -/
def lowerOrders [Zero F] (problem : XAdicProblem F) (d : Nat) : Array Nat :=
  problem.orders.map fun order ↦ min order d

/-- Remaining orders after the first `d` coefficients have been consumed. -/
def residualOrders [Zero F] (problem : XAdicProblem F) (d : Nat) : Array Nat :=
  problem.orders.map fun order ↦ order - d

/-- Shift update used by the second recursive PM-basis call. -/
def updateShiftByRows [Zero F] [BEq F]
    (basis : PolynomialMatrix F) (shift : Array Nat) : Array Nat :=
  (List.range basis.size).map
    (fun i ↦
      match rowShiftedDegree? (basis.getD i #[]) shift with
      | none => shift.getD i 0
      | some degree => degree) |>.toArray

/-- Residual matrix `(P * A) div X^d`, using an explicit product kernel and
truncating to the requested residual orders columnwise. -/
def residualMatrixWithProduct [Semiring F] [BEq F] [LawfulBEq F]
    (productKernel :
      Array Nat → PolynomialMatrix F → PolynomialMatrix F → PolynomialMatrix F)
    (basis : PolynomialMatrix F) (matrix : PolynomialMatrix F)
    (d : Nat) (orders : Array Nat) : PolynomialMatrix F :=
  let product := productKernel (orders.map fun order ↦ order + d) basis matrix
  PolynomialMatrix.ofFn product.size (PolynomialMatrix.MatrixWidth product) fun i j ↦
    PolynomialMatrix.divXTrunc d (orders.getD j 0)
      (PolynomialMatrix.rowGet (product.getD i #[]) j)

/-- Residual matrix `(P * A) div X^d`, truncated to the requested residual
orders columnwise, using the direct low-product row-column kernel. -/
def residualMatrix [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : PolynomialMatrix.MulLowContext F)
    (basis : PolynomialMatrix F) (matrix : PolynomialMatrix F)
    (d : Nat) (orders : Array Nat) : PolynomialMatrix F :=
  residualMatrixWithProduct (PolynomialMatrix.mulTruncColumnWith lowCtx)
    basis matrix d orders

end Approximant

end PolynomialMatrix

end CompPoly
