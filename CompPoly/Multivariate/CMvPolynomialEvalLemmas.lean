/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Natalia Klaus, Frantisek Silvasi, Derek Sorensen
-/
import CompPoly.Multivariate.MvPolyEquiv.Eval

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
lemma eval_zero : (0 : CMvPolynomial n R).eval vals = 0 := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_zero

@[simp]
lemma eval_one : (1 : CMvPolynomial n R).eval vals = 1 := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_one

@[simp]
lemma eval_C (c : R) : (CMvPolynomial.C c : CMvPolynomial n R).eval vals = c := by
  simp [eval_equiv, fromCMvPolynomial_C]

@[simp]
lemma eval_add (p q : CMvPolynomial n R) :
    (p + q).eval vals = p.eval vals + q.eval vals := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_add p q

@[simp]
lemma eval_mul (p q : CMvPolynomial n R) :
    (p * q).eval vals = p.eval vals * q.eval vals := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_mul p q

end

section

variable {n : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R]
variable (vals : Fin n → R)

@[simp]
lemma eval_neg (p : CMvPolynomial n R) :
    (-p).eval vals = -(p.eval vals) := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_neg p

@[simp]
lemma eval_sub (p q : CMvPolynomial n R) :
    (p - q).eval vals = p.eval vals - q.eval vals := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_sub p q

end

attribute [grind =] eval_zero eval_one eval_C eval_add eval_mul eval_neg eval_sub

end CPoly
