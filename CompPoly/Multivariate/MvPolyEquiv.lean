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

def fromCMvPolynomial  (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
  let support : List (Fin n →₀ ℕ) := p.monomials.map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by grind
  Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

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

lemma fromCMvPolynomial_injective : Function.Injective (@fromCMvPolynomial n R _) := by
  rw [Function.injective_iff_hasLeftInverse]
  exists toCMvPolynomial
  apply toCMvPolynomial_fromCMvPolynomial

omit [BEq R] [LawfulBEq R] in
lemma coeff_eq {m} (a : CMvPolynomial n R) :
    MvPolynomial.coeff m (fromCMvPolynomial a) = a.coeff (CMvMonomial.ofFinsupp m) := rfl

@[aesop simp]
lemma eq_iff_fromCMvPolynomial {u v: CMvPolynomial n R} :
    u = v ↔ fromCMvPolynomial u = fromCMvPolynomial v := by
  have := fromCMvPolynomial_injective (n := n) (R := R)
  aesop

@[simp]
lemma map_add (a b : CMvPolynomial n R) :
    fromCMvPolynomial (a + b) = fromCMvPolynomial a + fromCMvPolynomial b := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_eq, coeff_eq, coeff_eq]
  unfold CMvPolynomial.coeff
  unfold_projs
  unfold CPoly.Lawful.add
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  unfold_projs
  unfold Unlawful.add Lawful.fromUnlawful
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  erw [Unlawful.filter_get]
  by_cases h : (CMvMonomial.ofFinsupp m) ∈ a.1 <;> by_cases h' : (CMvMonomial.ofFinsupp m) ∈ b.1
  · erw [ExtTreeMap.mergeWith_of_mem_mem h h', Option.getD_some]
    have h₁ : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) =
      (a.1)[CMvMonomial.ofFinsupp m] := by simp [h]
    have h₂ : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) =
      (b.1)[CMvMonomial.ofFinsupp m] := by simp [h']
    erw [h₁, h₂]
    rfl
  · erw [ExtTreeMap.mergeWith_of_mem_left h h']
    have : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h']
    erw [this]
    have {x : R} : x + 0 = x := by simp
    specialize @this ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0)
    unfold_projs at this
    erw [this]
    rfl
  · erw [ExtTreeMap.mergeWith_of_mem_right h h']
    have : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h]
    erw [this]
    have {x : R} : 0 + x = x := by simp
    specialize @this ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0)
    unfold_projs at this
    erw [this]
    rfl
  · erw [ExtTreeMap.mergeWith_of_not_mem h h']
    have h₁ : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h]
    have h₂ : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h']
    erw [h₁, h₂, Option.getD_none]
    have : 0 + 0 = (0 : R) := by simp
    unfold_projs at this
    erw [this]
    rfl

@[simp]
lemma map_zero : fromCMvPolynomial (0 : CMvPolynomial n R) = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  unfold fromCMvPolynomial
  simp only
    [ Lawful.mem_iff_cast,
      Lawful.not_mem_zero,
      not_false_eq_true,
      getElem?_neg, Option.getD_none
    ]
  rfl

instance : TransCmp (fun x y ↦ compareOfLessAndEq (α := ℕ) x y) where
  eq_swap {a b} := by apply compareOfLessAndEq_eq_swap <;> omega
  isLE_trans {a b c} h₁ h₂ := by rw [isLE_compareOfLessAndEq] at * <;> omega

instance {n : ℕ} : TransCmp (α := CMvMonomial n)
    (Vector.compareLex (n := n) fun x y => compareOfLessAndEq (α := ℕ) x y) :=
  inferInstanceAs (TransCmp (Vector.compareLex (n := n) fun x y => compareOfLessAndEq (α := ℕ) x y))

@[simp]
lemma map_one : fromCMvPolynomial (1 : CMvPolynomial n R) = 1 := by
  ext m
  have : MvPolynomial.coeff m 1 = if m = 0 then 1 else (0 : R) := by
    unfold MvPolynomial.coeff
    unfold_projs
    simp only [Nat.zero_eq, Unlawful.zero_eq_zero]
    split_ifs with h <;>
      unfold AddMonoidAlgebra.single Finsupp.toFun Finsupp.single <;>
        simp [h]
  rw [this]
  unfold fromCMvPolynomial MvPolynomial.coeff
  simp only [Lawful.getElem?_eq_val_getElem?, Finsupp.coe_mk]
  unfold_projs
  unfold Lawful.C Unlawful.C MonoR.C
  simp only [Nat.cast_one]

  have triv_lem : (1 : R) = 0 → ∀ x y : R, x = y := by
    intros h
    have (x : R) : x = 0 := by
      have : x * 1 = x * 0 := by
        rw [h]
      simp only [mul_one, mul_zero] at this
      exact this
    intros x y; rw [this x, this y]

  split_ifs with g g' g'
  · rw [Nat.cast_one] at g; apply triv_lem g
  · rw [Nat.cast_one] at g; apply triv_lem g
  · have finsupp_m_eq_one : CMvMonomial.ofFinsupp m = CMvMonomial.zero := by
      rw [g']
      unfold CMvMonomial.ofFinsupp CMvMonomial.zero
      ext i h
      simp only [Nat.zero_eq, Finsupp.coe_mk]
      grind
    rw [finsupp_m_eq_one]
    have one_one_get₁ :
      ({(CMvMonomial.zero, 1)} : Unlawful n R)[(@CMvMonomial.zero n)]?.getD 0 = One.one := by
      unfold_projs; simp only [ExtTreeMap.empty_eq_emptyc, ExtTreeMap.get?_eq_getElem?,
        ExtTreeMap.getElem?_insert_self, Unlawful.zero_eq_zero, Option.getD_some]
    convert one_one_get₁
  · have : CMvMonomial.ofFinsupp m ≠ CMvMonomial.zero := by
      unfold CMvMonomial.ofFinsupp CMvMonomial.zero
      intros h
      have {i} : (Vector.ofFn m).get i = (Vector.replicate n 0).get i := by
        rw [h]
      apply g'
      ext i
      simp only [Finsupp.coe_mk]
      simp only [Vector.get_ofFn, Vector.get_replicate] at this
      exact this
    rw [ExtTreeMap.get?_eq_getElem?, getElem?_neg]
    simp only [Unlawful.zero_eq_zero, Option.getD_none]
    unfold Unlawful.ofList
    simp only [ExtTreeMap.ofList_singleton, ExtTreeMap.mem_insert, Std.compare_eq_iff_eq,
      ExtTreeMap.not_mem_empty, or_false]
    tauto

noncomputable def polyEquiv :
    Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R) where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ toCMvPolynomial_fromCMvPolynomial
  right_inv := fun _ ↦ fromCMvPolynomial_toCMvPolynomial

attribute [local grind=] Unlawful.add Lawful.add Unlawful.mul Lawful.mul

instance {n : ℕ} : AddCommSemigroup (CPoly.CMvPolynomial n R) where
  add_assoc := by aesop (add safe apply add_assoc)
  add_comm := by grind

instance {n : ℕ} : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add _ := by aesop
  add_zero _ := by aesop
  nsmul n p := (List.replicate n p).sum
  nsmul_succ {m x} := by grind

instance {n : ℕ} : AddCommMonoid (CPoly.CMvPolynomial n R) where
  toAddMonoid := inferInstance
  add_comm := by grind

omit [BEq R] [LawfulBEq R] in
lemma toList_pairs_monomial_coeff {β : Type} [AddCommMonoid β]
    {t : Unlawful n R}
  {f : CMvMonomial n → R → β} :
  t.toList.map (fun term => f term.1 term.2) =
    t.monomials.map (fun m => f m (t.coeff m)) := by
  unfold Unlawful.monomials Unlawful.coeff
  rw [←ExtTreeMap.map_fst_toList_eq_keys]
  rw [List.map_congr_left, List.map_map]
  grind

omit [BEq R] [LawfulBEq R] in
lemma foldl_eq_sum {β : Type} [AddCommMonoid β]
    {t : CMvPolynomial n R}
    {f : CMvMonomial n → R → β} :
    ExtTreeMap.foldl (fun x m c => (f m c) + x) 0 t.1 =
      Finsupp.sum (fromCMvPolynomial t) (f ∘ CMvMonomial.ofFinsupp) := by
  unfold Finsupp.sum Finset.sum
  simp only [Function.comp_apply, add_comm]
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  rw [←List.foldl_map (g := fun x y ↦ x + y), ←List.sum_eq_foldl]
  rw [toList_pairs_monomial_coeff]
  conv => rhs; arg 1; arg 1; ext x; arg 2; rw [←MvPolynomial.coeff, coeff_eq]
  congr 1
  have monomials_dedup_self : (Lawful.monomials t).dedup = Lawful.monomials t := by
    unfold Lawful.monomials
    simp only [List.dedup_eq_self]
    grind [ExtTreeMap.distinct_keys_toList]
  rw [List.dedup_map_of_injective CMvMonomial.injective_toFinsupp]
  rw [monomials_dedup_self]
  aesop

lemma coeff_sum [AddCommMonoid α]
    (s : Finset α)
    (f : α → CMvPolynomial n R)
    (m : CMvMonomial n) :
    coeff m (∑ x ∈ s, f x) = ∑ x ∈ s, coeff m (f x) := by
  rw [←Finset.sum_map_toList s, ←Finset.sum_map_toList s]
  induction' s.toList with h t ih
  · grind
  · simp [coeff_add]
    congr

lemma fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial
    {f : (Fin n →₀ ℕ) → R → Lawful n R }
    {a : CMvPolynomial n R} :
    fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) f) =
      Finsupp.sum (fromCMvPolynomial a) (fun m c ↦ fromCMvPolynomial (f m c)) := by
  unfold Finsupp.sum; ext
  simp [MvPolynomial.coeff_sum, coeff_eq, coeff_sum]

@[simp]
lemma map_mul (a b : CMvPolynomial n R) :
    fromCMvPolynomial (a * b) = fromCMvPolynomial a * fromCMvPolynomial b := by
  dsimp only [HMul.hMul, Mul.mul, Lawful.mul, Unlawful.mul]
  simp only [CMvPolynomial.fromUnlawful_fold_eq_fold_fromUnlawful]
  unfold MonoidAlgebra.mul'
  rw [foldl_eq_sum]; simp_rw [foldl_eq_sum]
  let F₀ (p q) : CMvMonomial n → R → Lawful n R :=
    fun p_1 q_1 ↦ Lawful.fromUnlawful {(p + p_1 , q * q_1)}
  set F₁ : (Fin n →₀ ℕ) → R → Lawful n R :=
    (fun p q ↦ Finsupp.sum (fromCMvPolynomial b) (F₀ p q ∘ CMvMonomial.ofFinsupp))
      ∘ CMvMonomial.ofFinsupp with eqF₁
  let F₂ a₁ b₁ :
    Multiplicative (Fin n →₀ ℕ) → R → MonoidAlgebra R (Multiplicative (Fin n →₀ ℕ)) :=
    fun a₂ b₂ ↦ MonoidAlgebra.single (a₁ * a₂) (b₁ * b₂)
  set F₃ : Multiplicative (Fin n →₀ ℕ) → R → MvPolynomial (Fin n) R :=
    fun a₁ b₁ ↦ Finsupp.sum (fromCMvPolynomial b) (F₂ a₁ b₁) with eqF₃
  have fromCMvPolynomial_F₁_eq_F₃ {m₁ : Multiplicative (Fin n →₀ ℕ)} {c₁ : R} :
      fromCMvPolynomial (F₁ m₁ c₁) = F₃ m₁ c₁ := by
    dsimp only [Function.comp_apply, F₁, F₀, F₃, F₂]
    rw [fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial]
    simp only [Function.comp_apply]
    congr
    ext (m₂ : Multiplicative _) c₂ m
    rw [coeff_eq]
    unfold coeff Lawful.fromUnlawful
    erw [Unlawful.filter_get, ←CMvMonomial.map_mul, ExtTreeMap.singleton_eq_insert]
    erw [ExtTreeMap.getElem?_insert]
    by_cases m_in : m = m₁ * m₂
    · rw [←m_in]
      simp only [compare_self]
      unfold MvPolynomial.coeff MonoidAlgebra.single
      simp only [m_in, Finsupp.single_eq_same]
      rfl
    · simp only
        [ Std.compare_eq_iff_eq,
          ExtTreeMap.not_mem_empty,
          not_false_eq_true,
          getElem?_neg
        ]
      unfold MvPolynomial.coeff MonoidAlgebra.single
      rw [Finsupp.single_eq_of_ne (by symm; grind)]
      split
      next h contra =>
        exfalso; apply m_in; symm
        apply CMvMonomial.injective_ofFinsupp contra
      next h => simp_all only [Option.getD_none]
  have : F₃ = fun σ x ↦ fromCMvPolynomial (F₁ σ x) := by
    ext x
    rw [fromCMvPolynomial_F₁_eq_F₃]
  rw [this]
  rw [fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial]
  rfl

instance {n : ℕ} : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by aesop
  mul_zero := by aesop
  mul_assoc := by aesop (add safe apply _root_.mul_assoc)
  one_mul := by aesop
  mul_one := by aesop

instance {n : ℕ} : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib {p q r} := by
    simp_all only [eq_iff_fromCMvPolynomial, map_mul, map_add]
    apply mul_add
  right_distrib {p q r} := by
    simp_all only [eq_iff_fromCMvPolynomial, map_mul, map_add]
    apply add_mul

instance {n : ℕ} : CommSemiring (CPoly.CMvPolynomial n R) where
  natCast_zero := by grind
  natCast_succ := by intro n; simp
  npow_zero := by intro x; simp [npowRecAuto, npowRec]
  npow_succ := by intro n x; simp [npowRecAuto, npowRec]
  mul_comm := by aesop (add safe apply _root_.mul_comm)

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
