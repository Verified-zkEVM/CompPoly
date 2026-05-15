/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.Basic

/-!
# Naive Batch Evaluation

Specification-level batch evaluators for canonical univariate polynomials.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

/-- Evaluate a polynomial at every point using the direct sum-of-powers evaluator. -/
def evalBatch [Semiring R] (p : CPolynomial R) (xs : Array R) : Array R :=
  xs.map fun x ↦ p.eval x

/-- Evaluate a polynomial at every point using Horner evaluation. -/
@[inline, specialize]
def evalBatchHorner [Semiring R] (p : CPolynomial R) (xs : Array R) : Array R :=
  xs.map fun x ↦ p.evalHorner x

end CPolynomial
end CompPoly
