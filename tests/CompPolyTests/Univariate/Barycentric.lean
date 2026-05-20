/-
Copyright (c) 2026 CompPoly, Elias Judin, Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic)
-/
import CompPoly.Univariate.Barycentric

/-!
# Barycentric Interpolation Tests

Regression tests for `BarycentricDomain` and its evaluator, ensuring the
structure is constructible, the weights match the product-inverse formula,
and the evaluator agrees with `CLagrange.interpolate` for concrete examples.
-/

namespace CompPoly.CPolynomial.CLagrange

open Finset

/-! ### Construction smoke test -/

/-- Three distinct rational nodes: 0, 1, 2. -/
def testDom3 : BarycentricDomain ℚ 3 :=
  BarycentricDomain.mk' ![0, 1, 2] <| by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ### Weight sanity -/

/-- The stored weights agree with `Lagrange.nodalWeight`. -/
example : ∀ i : Fin 3, testDom3.weights i =
    Lagrange.nodalWeight Finset.univ testDom3.nodes i :=
  testDom3.weights_eq_nodalWeight

/-! ### Evaluator at-node tests -/

/-- Evaluating at node 0 returns y 0. -/
example (y : Fin 3 → ℚ) : testDom3.eval y 0 = y 0 := by
  have h := testDom3.eval_at_node y 0
  simp [testDom3, BarycentricDomain.mk', Matrix.cons_val_zero] at h
  exact h

/-- Evaluating at node 1 returns y 1. -/
example (y : Fin 3 → ℚ) : testDom3.eval y 1 = y 1 := by
  have h := testDom3.eval_at_node y 1
  simp [testDom3, BarycentricDomain.mk'] at h
  exact h

/-- Evaluating at node 2 returns y 2. -/
example (y : Fin 3 → ℚ) : testDom3.eval y 2 = y 2 := by
  have h := testDom3.eval_at_node y 2
  simp [testDom3, BarycentricDomain.mk'] at h
  exact h

/-! ### Equivalence with CLagrange.interpolate -/

/-- The barycentric evaluator agrees with interpolate for any query point. -/
example (y : Fin 3 → ℚ) (z : ℚ) :
    testDom3.eval y z =
    (CLagrange.interpolate Finset.univ testDom3.nodes y).eval z :=
  testDom3.eval_eq_cinterpolate_eval y z

/-! ### Equivalence with Lagrange.interpolate (Mathlib) -/

/-- The barycentric evaluator agrees with Mathlib's `Lagrange.interpolate`. -/
example (y : Fin 3 → ℚ) (z : ℚ) :
    testDom3.eval y z =
    (Lagrange.interpolate Finset.univ testDom3.nodes y).eval z :=
  testDom3.eval_eq_interpolate_eval y z

end CompPoly.CPolynomial.CLagrange
