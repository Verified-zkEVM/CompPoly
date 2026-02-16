/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Natalia Klaus, Frantisek Silvasi, Derek Sorensen
-/
import CompPoly.Multivariate.MvPolyEquiv
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Lemmas for `CMvPolynomial.vars` and `CMvPolynomial.degrees`

Correctness lemmas relating `vars`, `degrees`, and `degreeOf` to Mathlib's `MvPolynomial`.
-/
namespace CPoly

open CMvPolynomial

variable {n : ℕ} {R : Type}

@[simp]
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

@[simp]
lemma degreeOf_zero [Zero R] [BEq R] [LawfulBEq R]
    (i : Fin n) :
    (0 : CMvPolynomial n R).degreeOf i = 0 := by
  have hmonomials_zero : Lawful.monomials (0 : CMvPolynomial n R) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro m hm
    exact Lawful.not_mem_zero (x := m) ((Lawful.mem_monomials_iff).1 hm)
  simp [CMvPolynomial.degreeOf, hmonomials_zero]

@[simp]
lemma degrees_zero [Zero R] [BEq R] [LawfulBEq R] :
    (0 : CMvPolynomial n R).degrees = 0 := by
  simp [CMvPolynomial.degrees, degreeOf_zero]

@[simp]
lemma vars_zero [Zero R] [BEq R] [LawfulBEq R] :
    (0 : CMvPolynomial n R).vars = ∅ := by
  simp [CMvPolynomial.vars, degreeOf_zero]

@[simp]
lemma degrees_one [CommSemiring R] [BEq R] [LawfulBEq R] :
    (1 : CMvPolynomial n R).degrees = 0 := by
  simp [degrees_equiv, map_one]

lemma vars_add_subset [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CMvPolynomial n R) :
    (p + q).vars ⊆ p.vars ∪ q.vars := by
  rw [vars_equiv (p := p + q), vars_equiv (p := p), vars_equiv (p := q)]
  simpa [map_add] using
    (MvPolynomial.vars_add_subset (fromCMvPolynomial p) (fromCMvPolynomial q))

attribute [grind] mem_vars_iff_degreeOf_pos
attribute [grind =] degreeOf_zero degrees_zero vars_zero degrees_one

end CPoly
