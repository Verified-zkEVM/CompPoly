/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Multivariate.CMvPolynomialEvalLemmas
public import CompPoly.Multivariate.PartialEval

/-!
  # Multivariate Partial Evaluation Tests

  Checks what `partialEvalFirst` does on generators, that it agrees with direct
  evaluation on a concrete polynomial, and that it does not raise the degree of
  the remaining variables.

  The checks are symbolic rather than `decide`-based: `CMvPolynomial` is carried
  by a quotient of `Std.ExtTreeMap`, so kernel reduction gets stuck on
  `Quot.lift` (the same reason `Multivariate/Restrict.lean`'s tests are
  symbolic).
-/

@[expose] public section

namespace CPoly

open _root_.CPoly.CMvPolynomial

/-- `eval` on a variable. The library has `eval_C`/`eval_add`/`eval_mul` as
`simp` lemmas but no `eval_X`, so the concrete check below supplies it. -/
private lemma eval_X_apply {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (i : Fin n) (v : Fin n → R) :
    (CMvPolynomial.X i : CMvPolynomial n R).eval v = v i := by
  simp [eval_equiv, fromCMvPolynomial_X]

/-! ## Action on generators -/

-- Fixing variable `0` leaves constants alone.
example (a c : ℚ) :
    partialEvalFirst (n := 1) a (CMvPolynomial.C c) = CMvPolynomial.C c := by
  simp [partialEvalFirst]

-- Variable `0` becomes the scalar it was fixed to.
example (a : ℚ) :
    partialEvalFirst (n := 1) a (CMvPolynomial.X 0) = CMvPolynomial.C a := by
  simp [partialEvalFirst]

-- Every other variable is shifted down by one.
example (a : ℚ) (i : Fin 1) :
    partialEvalFirst a (CMvPolynomial.X i.succ) = CMvPolynomial.X i := by
  simp [partialEvalFirst]

/-! ## Agreement with direct evaluation -/

/-- `X 0 * X 1 + 3` over `Fin 2`. -/
private def testPoly : CMvPolynomial 2 ℚ :=
  CMvPolynomial.X 0 * CMvPolynomial.X 1 + CMvPolynomial.C 3

-- Fixing variable `0` to `2`, then evaluating the remaining variable at `5`,
-- gives `2 * 5 + 3 = 13`.
example : (partialEvalFirst (2 : ℚ) testPoly).eval (fun _ => 5) = 13 := by
  rw [partialEvalFirst_eval]
  simp only [testPoly, eval_add, eval_mul, eval_C, eval_X_apply, Fin.cons_zero]
  norm_num

-- The same value reached through the general theorem rather than by computing.
example :
    (partialEvalFirst (2 : ℚ) testPoly).eval (fun _ => 5)
      = testPoly.eval (Fin.cons 2 (fun _ => 5)) :=
  partialEvalFirst_eval _ _ _

/-! ## Degree preservation -/

-- Fixing a variable cannot raise the degree of any variable that remains: a
-- bound on variable `1` of `p` transfers to variable `0` of the restriction.
example (a : ℚ) (deg : ℕ) (p : CMvPolynomial 2 ℚ)
    (hp : ∀ mono ∈ Lawful.monomials p, mono.degreeOf (Fin.succ 0) ≤ deg) :
    ∀ mono ∈ Lawful.monomials (partialEvalFirst a p), mono.degreeOf 0 ≤ deg :=
  partialEvalFirst_degreeOf_le a 0 p hp

end CPoly
