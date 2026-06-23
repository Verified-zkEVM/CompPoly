/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.BatchEval.Correctness

/-!
# Batch-Evaluation Contexts

Explicit context wrappers for reusable univariate batch-evaluation backends.
-/

namespace CompPoly

namespace CPolynomial

/-- Contract wrapper for batch evaluation backends. -/
structure BatchEvalContext (R : Type*) [Semiring R] where
  evalBatchWith : CPolynomial R → Array R → Array R
  correct : ∀ p xs, evalBatchWith p xs = CPolynomial.evalBatch p xs

namespace BatchEvalContext

/-- Horner-backed batch evaluation context. -/
def horner (R : Type*) [Semiring R] : BatchEvalContext R where
  evalBatchWith := CPolynomial.evalBatchHorner
  correct := by
    intro p xs
    exact CPolynomial.evalBatchHorner_eq_evalBatch p xs

/-- Subproduct-tree-backed batch evaluation context. -/
def subproduct (R : Type*) [Field R] [BEq R] [LawfulBEq R]
    (M : CPolynomial.MulContext R) (D : CPolynomial.ModContext R) :
    BatchEvalContext R where
  evalBatchWith := CPolynomial.evalBatchSubproduct M D
  correct := by
    intro p xs
    exact CPolynomial.evalBatchSubproduct_eq_evalBatch M D p xs

end BatchEvalContext

end CPolynomial

end CompPoly
