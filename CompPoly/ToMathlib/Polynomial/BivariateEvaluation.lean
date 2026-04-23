/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import CompPoly.ToMathlib.Polynomial.BivariateDegree

/-!
# Mathlib-Facing Bivariate Evaluation Helpers

This file collects evaluation-oriented helpers for Mathlib's
bivariate polynomial surface `R[X][Y]`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section CommSemiring

variable [CommSemiring F]

/-- Evaluation of a bivariate polynomial is commutative,
  i.e. evaluating in `X` and then in `Y` is the same as
  evaluating in `Y` first and then in `X`. -/
theorem eval_comm {f : Polynomial (Polynomial F)} {a x : F} :
  (f.eval (Polynomial.C a)).eval x = 
    (Polynomial.map (evalRingHom x) f).eval a := by
  simp only [Polynomial.eval_map]
  have h_eval : Polynomial.eval (Polynomial.C a) f = 
    ∑ i ∈ f.support, f.coeff i * (Polynomial.C a) ^ i := by
    aesop (add simp [Polynomial.eval_eq_sum])
  simp [h_eval, Polynomial.eval_finset_sum, 
        Polynomial.eval₂_eq_sum, Polynomial.sum_def]

end CommSemiring

end
end Polynomial.Bivariate
