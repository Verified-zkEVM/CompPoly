/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Multivariate.MvPolyEquiv
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# `vars`/`degrees` lemmas for `CPoly.CMvPolynomial`

These lemmas validate the basic behavior of `CMvPolynomial.vars` and
`CMvPolynomial.degrees`, and provide the expected additive subset property for `vars`.
-/
namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type}

lemma mem_vars_iff_degreeOf_pos [Zero R]
    (i : Fin n) (p : CMvPolynomial n R) :
    i ∈ p.vars ↔ 0 < p.degreeOf i := by
  simp [CMvPolynomial.vars]

lemma degrees_equiv [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) :
    p.degrees = (fromCMvPolynomial p).degrees := by
  ext i
  have hdeg : p.degreeOf i = (fromCMvPolynomial p).degreeOf i :=
    congrFun (degreeOf_equiv (S := R) (p := p)) i
  simpa [degreeOf_eq_count_degrees, MvPolynomial.degreeOf_def] using hdeg

lemma vars_equiv [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) :
    p.vars = (fromCMvPolynomial p).vars := by
  ext i
  rw [mem_vars_iff_degreeOf_pos]
  have hdeg : p.degreeOf i = (fromCMvPolynomial p).degreeOf i :=
    congrFun (degreeOf_equiv (S := R) (p := p)) i
  rw [hdeg, MvPolynomial.degreeOf_def, MvPolynomial.vars_def]
  simpa [Multiset.mem_toFinset] using
    (Multiset.count_pos (a := i) (s := (fromCMvPolynomial p).degrees))

lemma degrees_zero [CommSemiring R] [BEq R] [LawfulBEq R] :
    (0 : CMvPolynomial n R).degrees = 0 := by
  simp [degrees_equiv, map_zero]

lemma vars_zero [CommSemiring R] [BEq R] [LawfulBEq R] :
    (0 : CMvPolynomial n R).vars = ∅ := by
  simp [vars_equiv, map_zero]

lemma degreeOf_zero [CommSemiring R] [BEq R] [LawfulBEq R]
    (i : Fin n) :
    (0 : CMvPolynomial n R).degreeOf i = 0 := by
  rw [degreeOf_eq_count_degrees, degrees_zero, Multiset.count_zero]

lemma vars_add_subset [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CMvPolynomial n R) :
    (p + q).vars ⊆ p.vars ∪ q.vars := by
  rw [vars_equiv (p := p + q), vars_equiv (p := p), vars_equiv (p := q)]
  simpa [map_add] using
    (MvPolynomial.vars_add_subset (fromCMvPolynomial p) (fromCMvPolynomial q))

end

end CPoly
