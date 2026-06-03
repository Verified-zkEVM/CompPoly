/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Lagrange

/-!
# Array Wrappers for Computable Lagrange Interpolation

Finite-index adapters for `CPolynomial.CLagrange.interpolate`.
-/

namespace CompPoly

namespace CPolynomial

namespace CLagrange

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The `i`th node in an array, exposed through a `Fin` index. -/
def arrayNode (xs : Array F) (i : Fin xs.size) : F :=
  xs[i]

/-- The `i`th value in an array, defaulting only when the value array is shorter. -/
def arrayValue (ys : Array F) {n : Nat} (i : Fin n) : F :=
  ys.getD i 0

/-- Lagrange interpolation from separate node and value arrays. -/
def interpolateArrays (xs ys : Array F) : CPolynomial F :=
  interpolate (Finset.univ : Finset (Fin xs.size))
    (arrayNode xs) (arrayValue ys)

/-- The `x` coordinate of the `i`th packed point. -/
def pointNode (points : Array (F × F)) (i : Fin points.size) : F :=
  (points[i]).1

/-- The `y` coordinate of the `i`th packed point. -/
def pointValue (points : Array (F × F)) (i : Fin points.size) : F :=
  (points[i]).2

/-- Lagrange interpolation from packed `(x, y)` points. -/
def interpolateArray (points : Array (F × F)) : CPolynomial F :=
  interpolate (Finset.univ : Finset (Fin points.size))
    (pointNode points) (pointValue points)

/-- Packed points have pairwise distinct Lagrange nodes. -/
def DistinctPointNodes (points : Array (F × F)) : Prop :=
  (points.toList.map fun point ↦ point.1).Nodup

/-- Evaluating the packed-array interpolant at one indexed node returns the indexed value. -/
theorem eval_interpolateArray_at_index
    (points : Array (F × F)) (hdistinct : DistinctPointNodes points)
    (i : Fin points.size) :
    CPolynomial.eval (pointNode points i) (interpolateArray points) =
      pointValue points i := by
  sorry

/-- Evaluating the packed-array interpolant at a listed point returns that point's value. -/
theorem eval_interpolateArray_at_mem
    (points : Array (F × F)) (hdistinct : DistinctPointNodes points)
    {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1 (interpolateArray points) = point.2 := by
  sorry

end CLagrange

end CPolynomial

end CompPoly
