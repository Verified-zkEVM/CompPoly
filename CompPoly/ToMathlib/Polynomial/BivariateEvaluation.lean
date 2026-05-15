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
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add, Polynomial.map_add, hp, hq]
  | monomial n c =>
      simp only [Polynomial.eval_monomial, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.map_monomial, Polynomial.coe_evalRingHom]

end CommSemiring

end
end Polynomial.Bivariate
