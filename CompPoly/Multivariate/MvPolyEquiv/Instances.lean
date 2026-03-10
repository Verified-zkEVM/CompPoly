 /-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Dimitris Mitsios
 -/
import CompPoly.Multivariate.MvPolyEquiv.Core

open Std

namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

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

attribute [local grind=] Unlawful.add Lawful.add Unlawful.mul Lawful.mul

instance {n : ℕ} : AddCommSemigroup (CPoly.CMvPolynomial n R) where
  add_assoc a b c := by
    apply fromCMvPolynomial_injective
    simp [add_assoc]
  add_comm a b := by
    apply fromCMvPolynomial_injective
    simp [add_comm]

instance {n : ℕ} : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add a := by
    apply fromCMvPolynomial_injective
    simp
  add_zero a := by
    apply fromCMvPolynomial_injective
    simp
  nsmul := nsmulRec

instance {n : ℕ} : AddCommMonoid (CPoly.CMvPolynomial n R) where
  toAddMonoid := inferInstance
  add_comm a b := by
    apply fromCMvPolynomial_injective
    simp [add_comm]

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
  zero_mul a := by
    apply fromCMvPolynomial_injective
    simp
  mul_zero a := by
    apply fromCMvPolynomial_injective
    simp
  mul_assoc a b c := by
    apply fromCMvPolynomial_injective
    simp [mul_assoc]
  one_mul a := by
    apply fromCMvPolynomial_injective
    simp
  mul_one a := by
    apply fromCMvPolynomial_injective
    simp

instance {n : ℕ} : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib {p q r} := by
    simp_all only [eq_iff_fromCMvPolynomial, map_mul, map_add]
    apply mul_add
  right_distrib {p q r} := by
    simp_all only [eq_iff_fromCMvPolynomial, map_mul, map_add]
    apply add_mul

instance {n : ℕ} : CommSemiring (CPoly.CMvPolynomial n R) where
  natCast_zero := rfl
  natCast_succ := by intro n; simp
  npow_zero := by intro x; simp [npowRecAuto, npowRec]
  npow_succ := by intro n x; simp [npowRecAuto, npowRec]
  mul_comm a b := by
    apply fromCMvPolynomial_injective
    simp [mul_comm]

section CommRing

variable {n : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R]

@[simp]
lemma map_neg (a : CMvPolynomial n R) :
    fromCMvPolynomial (-a) = -fromCMvPolynomial a := by
  ext m
  simp only [MvPolynomial.coeff_neg, coeff_eq]
  unfold CMvPolynomial.coeff
  unfold_projs
  unfold Lawful.neg Unlawful.neg Lawful.fromUnlawful
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  erw [Unlawful.filter_get, ExtTreeMap.getElem?_map]
  cases h : (a.1)[CMvMonomial.ofFinsupp m]? with
  | none => simp
  | some v => simp

lemma map_sub (a b : CMvPolynomial n R) :
    fromCMvPolynomial (Sub.sub a b) = fromCMvPolynomial a - fromCMvPolynomial b := by
  unfold Sub.sub Lawful.instSub Lawful.sub
  rw [map_add, map_neg, sub_eq_add_neg]

instance : CommRing (CMvPolynomial n R) where
  neg_add_cancel a := by
    apply fromCMvPolynomial_injective
    simp [map_neg, map_add, map_zero]
  mul_comm a b := by
    apply fromCMvPolynomial_injective
    simp [mul_comm]
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

end CommRing

noncomputable def polyRingEquiv :
  RingEquiv (CPoly.CMvPolynomial n R) (MvPolynomial (Fin n) R) where
  toEquiv := CPoly.polyEquiv
  map_mul' := map_mul
  map_add' := map_add

end

namespace CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Ring equivalence between `CMvPolynomial 0 R` and `R`. -/
noncomputable def isEmptyRingEquiv : CMvPolynomial 0 R ≃+* R :=
  polyRingEquiv.trans (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv

instance instSMul : SMul R (CMvPolynomial n R) where
  smul r p := C r * p

instance instSMulZeroClass : SMulZeroClass R (CMvPolynomial n R) where
  smul_zero r := mul_zero (C r)

@[simp]
lemma smul_def (r : R) (p : CMvPolynomial n R) : r • p = C r * p := rfl

section Algebra

lemma fromCMvPolynomial_C (r : R) :
    fromCMvPolynomial (C r : CMvPolynomial n R) = MvPolynomial.C r := by
  by_cases hr : r = 0
  · subst hr
    have : (C 0 : CMvPolynomial n R) = 0 := by show Lawful.C 0 = Lawful.C 0; rfl
    rw [this, CPoly.map_zero, MvPolynomial.C_0]
  · ext m
    rw [coeff_eq, MvPolynomial.coeff_C]
    unfold C Lawful.C coeff Unlawful.C MonoR.C
    simp only [hr, ite_false]
    have ofFinsupp_zero : CMvMonomial.ofFinsupp (0 : Fin n →₀ ℕ) = CMvMonomial.zero := by
      unfold CMvMonomial.ofFinsupp CMvMonomial.zero; ext i hi; grind
    by_cases hm : (0 : Fin n →₀ ℕ) = m
    · subst hm; rw [if_pos rfl]
      erw [ExtTreeMap.getElem?_ofList_of_mem
        (k := CMvMonomial.zero) (k' := CMvMonomial.ofFinsupp 0)
        (by rw [ofFinsupp_zero]; exact compare_self)
        (v := r) (by simp) (by simp)]
      simp
    · rw [if_neg hm]
      have hne : CMvMonomial.ofFinsupp m ≠ CMvMonomial.zero := by
        intro h; apply hm; ext i
        have hi := congr_fun (congr_arg Vector.get h) i
        simp [CMvMonomial.ofFinsupp, CMvMonomial.zero] at hi; exact hi.symm
      erw [ExtTreeMap.getElem?_ofList_of_contains_eq_false (by simp [hne])]
      rfl

noncomputable def CRingHom : R →+* CMvPolynomial n R where
  toFun := C
  map_one' := by
    rw [eq_iff_fromCMvPolynomial]
    simp [fromCMvPolynomial_C, CPoly.map_one]
  map_mul' x y := by
    rw [eq_iff_fromCMvPolynomial]
    simp [fromCMvPolynomial_C, CPoly.map_mul]
  map_zero' := by
    rw [eq_iff_fromCMvPolynomial]
    simp [fromCMvPolynomial_C, CPoly.map_zero]
  map_add' x y := by
    rw [eq_iff_fromCMvPolynomial]
    simp [fromCMvPolynomial_C, CPoly.map_add]

noncomputable instance instAlgebra : Algebra R (CMvPolynomial n R) :=
  Algebra.mk (toSMul := instSMul) CRingHom
    (fun r x => mul_comm (C r) x)
    (fun _ _ => rfl)

end Algebra

end CMvPolynomial

end CPoly
