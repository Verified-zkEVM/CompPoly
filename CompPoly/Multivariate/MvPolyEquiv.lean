/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa
-/
import Batteries.Data.Vector.Lemmas
import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Ring.Defs
import CompPoly.Multivariate.Lawful
import Batteries.Data.Vector.Basic

/-!
# `Equiv` and `RingEquiv` between `CMvPolynomial` and `MvPolynomial`.

## Main results

* `CPoly.polyEquiv` - `Equiv` between `CMvPolynomial` and `MvPolynomial`
* `CPoly.polyRingEquiv` - `RingEquiv` between `CMvPolynomial` and `MvPolynomial`
-/
open Std

namespace CPoly
open CMvPolynomial

section

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

noncomputable def toCMvPolynomial (p : MvPolynomial (Fin n) R) : CMvPolynomial n R :=
  let ⟨s, f, _⟩ := p
  let unlawful := .ofList <| s.toList.map fun m ↦ (CMvMonomial.ofFinsupp m, f m)
  ⟨
    unlawful,
    by
      intros m contra
      obtain ⟨elem, h₁⟩ : ∃ (h : m ∈ unlawful), unlawful[m] = 0 :=
        ExtTreeMap.getElem?_eq_some_iff.1 contra
      obtain ⟨a, ha₁, ⟨rfl⟩⟩ : ∃ a ∈ s, .ofFinsupp a = m := by
        simp [unlawful] at elem; rw [ExtTreeMap.mem_ofList] at elem; simp at elem
        exact elem
      have : f a = 0 := by
        dsimp [unlawful] at h₁
        erw [ExtTreeMap.getElem_ofList_of_mem (v := f a)
                                              (mem := by simp; use a)
                                              (distinct := ?distinct)] at h₁ <;> try simp
        exact h₁
        case distinct =>
          simp only [List.pairwise_map]
          exact List.distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
      grind
  ⟩

instance {n : ℕ} {R : Type} : Membership (Vector ℕ n) (Unlawful n R) := inferInstance

omit [BEq R] [LawfulBEq R] in
@[grind =, simp]
theorem toCMvPolynomial_fromCMvPolynomial {p : CMvPolynomial n R} :
    toCMvPolynomial (fromCMvPolynomial p) = p := by
  unfold fromCMvPolynomial toCMvPolynomial
  dsimp
  ext m; simp only [CMvPolynomial.coeff]; congr 1
  by_cases eq : m ∈ p <;> simp [eq]
  · erw [ExtTreeMap.getElem?_ofList_of_mem (k := m)
                                           (k_eq := by simp)
                                           (v := p[m])
                                           (mem := by simp; grind)
                                           (distinct := ?distinct)]
    grind
    case distinct =>
      simp only [Std.compare_eq_iff_eq, List.pairwise_map]
      exact List.distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
  · erw [ExtTreeMap.getElem?_ofList_of_contains_eq_false]
    simpa

omit [BEq R] [LawfulBEq R] in
@[grind=, simp]
theorem fromCMvPolynomial_toCMvPolynomial {p : MvPolynomial (Fin n) R} :
    fromCMvPolynomial (toCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toCMvPolynomial, fromCMvPolynomial]
  ext m; simp [MvPolynomial.coeff]
  rcases p with ⟨s, f, hf⟩
  simp only [Finsupp.coe_mk]
  generalize eq : (ExtTreeMap.ofList _ _) = p
  by_cases eq₁ : CMvMonomial.ofFinsupp m ∈ p
  · obtain ⟨m', hm'₁, hm'₂⟩ : ∃ a ∈ s, CMvMonomial.ofFinsupp a = CMvMonomial.ofFinsupp m := by
      aesop
    have : f m' ≠ 0 := by grind
    obtain ⟨rfl⟩ : m' = m := CMvMonomial.injective_ofFinsupp hm'₂
    suffices p[CMvMonomial.ofFinsupp m] = f m by simpa [eq₁]
    simp_rw [←eq]
    rw [ExtTreeMap.getElem_ofList_of_mem (k := CMvMonomial.ofFinsupp m) (k_eq := by simp)
                                         (mem := by simp; use m) (distinct := ?distinct)]
    case distinct =>
      simp only [Std.compare_eq_iff_eq, List.pairwise_map]
      exact List.distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
  · have : ∀ x ∈ s, CMvMonomial.ofFinsupp x ≠ CMvMonomial.ofFinsupp m := by aesop
    grind

noncomputable def polyEquiv :
    Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R) where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ toCMvPolynomial_fromCMvPolynomial
  right_inv := fun _ ↦ fromCMvPolynomial_toCMvPolynomial

noncomputable def polyRingEquiv :
  RingEquiv (CPoly.CMvPolynomial n R) (MvPolynomial (Fin n) R) where
  toEquiv := CPoly.polyEquiv
  map_mul' := map_mul
  map_add' := map_add

omit [BEq R] [LawfulBEq R] in
lemma eval₂_equiv {S : Type} {p : CMvPolynomial n R} [CommSemiring S] {f : (R →+* S)}
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
lemma totalDegree_equiv {S : Type} {p : CMvPolynomial n R} [CommSemiring S] :
    p.totalDegree = (fromCMvPolynomial p).totalDegree := by rfl

omit [BEq R] [LawfulBEq R] in
lemma degreeOf_equiv {S : Type} {p : CMvPolynomial n R} [CommSemiring S] :
    p.degreeOf = (fromCMvPolynomial p).degreeOf := by
  ext i
  unfold MvPolynomial.degreeOf MvPolynomial.degrees
  unfold MvPolynomial.support fromCMvPolynomial
  simp only
  unfold CMvPolynomial.degreeOf
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

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `eval₂` as a ring homomorphism. -/
def eval₂Hom {S : Type} [CommSemiring S]
    (f : R →+* S) (vs : Fin n → S) : CMvPolynomial n R →+* S where
  toFun := eval₂ f vs
  map_zero' := by simp [eval₂_equiv]
  map_one' := by simp [eval₂_equiv]
  map_add' _ _ := by simp [eval₂_equiv, MvPolynomial.eval₂_add]
  map_mul' _ _ := by simp [eval₂_equiv, MvPolynomial.eval₂_mul]

@[simp]
lemma eval₂Hom_apply {S : Type} [CommSemiring S]
    (f : R →+* S) (vs : Fin n → S) (p : CMvPolynomial n R) :
    eval₂Hom f vs p = eval₂ f vs p := rfl

/-- Ring equivalence between `CMvPolynomial 0 R` and `R`. -/
noncomputable def isEmptyRingEquiv : CMvPolynomial 0 R ≃+* R :=
  polyRingEquiv.trans (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv

instance instSMul : SMul R (CMvPolynomial n R) where
  smul r p := C r * p

instance instSMulZeroClass : SMulZeroClass R (CMvPolynomial n R) where
  smul_zero r := mul_zero (C r)

@[simp]
lemma smul_def (r : R) (p : CMvPolynomial n R) : r • p = C r * p := rfl

end CMvPolynomial

end CPoly
