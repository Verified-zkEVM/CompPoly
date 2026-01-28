/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Natalia Klaus, Frantisek Silvasi, Derek Sorensen
-/
import CompPoly.Multivariate.MvPolyEquiv

/-!
# simp/grind lemmas for `CPoly.CMvPolynomial.eval`

These lemmas are meant to support proof automation (simp/grind normalization)
when reasoning about polynomial evaluation (e.g. Horner correctness proofs).
-/
namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
variable (vals : Fin n → R)

@[simp]
lemma eval_add (p q : CMvPolynomial n R) :
    (p + q).eval vals = p.eval vals + q.eval vals := by simp [eval_equiv]

@[simp]
lemma eval_mul (p q : CMvPolynomial n R) :
    (p * q).eval vals = p.eval vals * q.eval vals := by simp [eval_equiv]

end

attribute [grind =] eval_add eval_mul

end CPoly
