/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Dimitris Mitsios
-/
import CompPoly.Multivariate.MvPolyEquiv.Instances

/-!
# `CMvPolynomial`/`MvPolynomial` Evaluation

Evaluation lemmas for the `CMvPolynomial` and `MvPolynomial` conversions.
-/

open Std

namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

omit [BEq R] [LawfulBEq R] in
lemma eval₂_equiv {S : Type*} {p : CMvPolynomial n R} [CommSemiring S] {f : (R →+* S)}
    {vals : Fin n → S} : p.eval₂ f vals = (fromCMvPolynomial p).eval₂ f vals := by
  unfold CMvPolynomial.eval₂ MvPolynomial.eval₂
  rw [foldl_eq_sum]
  congr 1
  unfold Function.comp
  simp only
  ext m c
  congr 1
  unfold MonoR.evalMonomial Finsupp.prod
  simp only
  refine Eq.symm (Finset.prod_subset_one_on_sdiff ?_ ?_ ?_)
  · exact Finset.subset_univ _
  · intros x h
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finsupp.mem_support_iff, ne_eq, Decidable.not_not,
      true_and] at h
    unfold CMvMonomial.ofFinsupp
    simp [h]
  · intros x _
    congr 1
    unfold CMvMonomial.ofFinsupp
    simp

omit [BEq R] [LawfulBEq R] in
lemma eval_equiv {p : CMvPolynomial n R} {vals : Fin n → R} :
    p.eval vals = (fromCMvPolynomial p).eval vals := by
  unfold CMvPolynomial.eval MvPolynomial.eval MvPolynomial.eval₂Hom
  simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  exact eval₂_equiv

omit [BEq R] [LawfulBEq R] in
lemma totalDegree_equiv {S : Type*} {p : CMvPolynomial n R} [CommSemiring S] :
    p.totalDegree = (fromCMvPolynomial p).totalDegree := by rfl

omit [BEq R] [LawfulBEq R] in
lemma degreeOf_equiv {S : Type*} {p : CMvPolynomial n R} [CommSemiring S] :
    p.degreeOf = (fromCMvPolynomial p).degreeOf := by
  ext i
  unfold MvPolynomial.degreeOf MvPolynomial.degrees
  unfold MvPolynomial.support fromCMvPolynomial
  simp only
  unfold degreeOf
  congr
  unfold instDecidableEqFin Classical.decEq inferInstance
  unfold Classical.propDecidable
  ext a b
  next h heq =>
    by_contra! h
    generalize h' : Classical.choice _ = out at h
    match h'' : out with
    | isTrue g => grind
    | isFalse g =>
      apply g
      split at h
      · next g' g'' g''' => grind
      · simp at h

end

namespace CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `eval₂` as a ring homomorphism. -/
def eval₂Hom {S : Type*} [CommSemiring S]
    (f : R →+* S) (vs : Fin n → S) : CMvPolynomial n R →+* S where
  toFun := eval₂ f vs
  map_zero' := by simp [eval₂_equiv]
  map_one' := by simp [eval₂_equiv]
  map_add' _ _ := by simp [eval₂_equiv, MvPolynomial.eval₂_add]
  map_mul' _ _ := by simp [eval₂_equiv, MvPolynomial.eval₂_mul]

@[simp]
lemma eval₂Hom_apply {S : Type*} [CommSemiring S]
    (f : R →+* S) (vs : Fin n → S) (p : CMvPolynomial n R) :
    eval₂Hom f vs p = eval₂ f vs p := rfl

end CMvPolynomial

end CPoly
