/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.BatchEval.Naive

/-!
# Batch Evaluation Correctness

Correctness theorems for univariate batch-evaluation implementations.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

/-- Batched Horner evaluation agrees with the direct batched evaluator. -/
theorem evalBatchHorner_eq_evalBatch [Semiring R] (p : CPolynomial R) (xs : Array R) :
    evalBatchHorner p xs = evalBatch p xs := by
  simp [evalBatchHorner, evalBatch, eval_horner_eq_eval]

end CPolynomial
end CompPoly
