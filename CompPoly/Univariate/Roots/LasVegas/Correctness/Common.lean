/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Shared Correctness Lemmas for Las Vegas Splitting

Shared algebraic, root-preservation, degree, and work-measure lemmas used by
the Las Vegas splitter correctness modules.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

theorem finiteFieldRootProductWith_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    lasVegasSplitterInput ctx.q (finiteFieldRootProductWith M D ctx p) := by
  exact ⟨finiteFieldRootProductWith_ne_zero_of_ne_zero M D ctx hp,
    finiteFieldRootProductWith_dvd_frobenius_of_context M D ctx hp⟩

/-- Default-backend field-root products satisfy the Las Vegas splitter input predicate. -/
theorem finiteFieldRootProduct_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    lasVegasSplitterInput ctx.q (finiteFieldRootProduct ctx p) := by
  exact finiteFieldRootProductWith_lasVegasSplitterInput
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx hp

theorem eval_reduceModWith_eq_self_of_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (D : CPolynomial.Raw.ModContext F)
    {modulus h : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a modulus = 0) :
    CPolynomial.eval a (reduceModWith D modulus h) = CPolynomial.eval a h := by
  unfold reduceModWith
  by_cases hzero : modulus == 0
  · rw [if_pos hzero]
  · rw [if_neg hzero]
    have hrootMonic : CPolynomial.eval a (CPolynomial.monicNormalize modulus) = 0 :=
      monicNormalize_root_of_root hroot
    change
      CPolynomial.Raw.eval a
          (D.modByMonic h.val (CPolynomial.monicNormalize modulus).val).trim =
        CPolynomial.Raw.eval a h.val
    rw [CPolynomial.Raw.eval_trim_eq_eval]
    rw [D.modByMonic_eq_modByMonic _ _ (CPolynomial.trim_eq h)
      (CPolynomial.trim_eq (CPolynomial.monicNormalize modulus))]
    exact CPolynomial.Raw.eval_modByMonic_eq_self_of_eval_eq_zero
      h.val (CPolynomial.monicNormalize modulus).val hrootMonic

theorem eval_powModWith_eq_pow {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus base : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a modulus = 0) (n : Nat) :
    CPolynomial.eval a (powModWith M D modulus base n) = CPolynomial.eval a base ^ n := by
  unfold powModWith
  change
    CPolynomial.Raw.eval a
        (CPolynomial.Raw.powModWith M D modulus.val base.val n).trim =
      CPolynomial.Raw.eval a base.val ^ n
  rw [CPolynomial.Raw.eval_trim_eq_eval]
  exact raw_eval_powModWith_eq_pow M D hroot n

theorem nontrivialProperChildren_mem_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {children : Array (CPolynomial F)}
    (hmem : child ∈ children.toList)
    (hproper : isNontrivialProperChild parent child = true) :
    child ∈ (nontrivialProperChildren parent children).toList := by
  unfold nontrivialProperChildren
  simp [hmem, hproper]

theorem proper_of_mem_nontrivialProperChildren {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {children : Array (CPolynomial F)}
    (hmem : child ∈ (nontrivialProperChildren parent children).toList) :
    isNontrivialProperChild parent child = true := by
  unfold nontrivialProperChildren at hmem
  simp at hmem
  rcases hmem with ⟨_hmem, hproper⟩
  exact hproper

lemma mem_eraseDups_fold {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ (xs : List α) (out : Array α),
      a ∈ List.foldl (fun out x ↦ if x ∈ out then out else out.push x) out xs →
        a ∈ out ∨ a ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro out h
      exact Or.inl h
  | cons x xs ih =>
      intro out h
      simp only [List.foldl_cons] at h
      by_cases hx : x ∈ out
      · have h' := ih out (by simpa [hx] using h)
        cases h' with
        | inl hout => exact Or.inl hout
        | inr hxs => exact Or.inr (by simp [hxs])
      · have h' := ih (out.push x) (by simpa [hx] using h)
        cases h' with
        | inl hout =>
            simp at hout
            cases hout with
            | inl hout => exact Or.inl hout
            | inr hax => exact Or.inr (by simp [hax])
        | inr hxs => exact Or.inr (by simp [hxs])

lemma mem_of_mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs.eraseDups) : a ∈ xs := by
  unfold Array.eraseDups at h
  rcases xs with ⟨l⟩
  simp at h ⊢
  have hh := mem_eraseDups_fold a l #[] h
  simpa using hh

lemma mem_eraseDups_fold_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ (xs : List α) (out : Array α),
      a ∈ out ∨ a ∈ xs →
        a ∈ List.foldl (fun out x ↦ if x ∈ out then out else out.push x) out xs := by
  intro xs
  induction xs with
  | nil =>
      intro out h
      simpa using h
  | cons x xs ih =>
      intro out h
      simp only [List.foldl_cons]
      by_cases hx : x ∈ out
      · simp [hx]
        apply ih out
        cases h with
        | inl hout => exact Or.inl hout
        | inr hmem =>
            simp at hmem
            cases hmem with
            | inl hax => exact Or.inl (by simpa [hax] using hx)
            | inr hxs => exact Or.inr hxs
      · simp [hx]
        apply ih (out.push x)
        cases h with
        | inl hout => exact Or.inl (by simp [hout])
        | inr hmem =>
            simp at hmem
            cases hmem with
            | inl hax => exact Or.inl (by simp [hax])
            | inr hxs => exact Or.inr hxs

lemma mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs) : a ∈ xs.eraseDups := by
  unfold Array.eraseDups
  rcases xs with ⟨l⟩
  simp at h ⊢
  exact mem_eraseDups_fold_of_mem a l #[] (Or.inr h)

theorem middle_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left middle right : CPolynomial F}
    (hleft : ¬ isNontrivialProperChild parent left = true)
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, middle, right]).eraseDups.size) :
    isNontrivialProperChild parent middle = true := by
  by_cases hmiddle : isNontrivialProperChild parent middle = true
  · exact hmiddle
  · by_cases hright : isNontrivialProperChild parent right = true
    · simp [nontrivialProperChildren, hleft, hmiddle, hright, Array.eraseDups] at hsize
    · simp [nontrivialProperChildren, hleft, hmiddle, hright, Array.eraseDups] at hsize

theorem right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left middle right : CPolynomial F}
    (hleft : ¬ isNontrivialProperChild parent left = true)
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, middle, right]).eraseDups.size) :
    isNontrivialProperChild parent right = true := by
  by_cases hmiddle : isNontrivialProperChild parent middle = true
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hmiddle, hright, Array.eraseDups] at hsize
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hmiddle, hright, Array.eraseDups] at hsize

theorem right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left middle right : CPolynomial F}
    (hmiddle : ¬ isNontrivialProperChild parent middle = true)
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, middle, right]).eraseDups.size) :
    isNontrivialProperChild parent right = true := by
  by_cases hleft : isNontrivialProperChild parent left = true
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hmiddle, hright, Array.eraseDups] at hsize
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hmiddle, hright, Array.eraseDups] at hsize

theorem left_proper_of_pair_filter_size_ge_two {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left right : CPolynomial F}
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, right]).size) :
    isNontrivialProperChild parent left = true := by
  by_cases hleft : isNontrivialProperChild parent left = true
  · exact hleft
  · by_cases hright : isNontrivialProperChild parent right = true
    · simp [nontrivialProperChildren, hleft, hright] at hsize
    · simp [nontrivialProperChildren, hleft, hright] at hsize

theorem right_proper_of_pair_filter_size_ge_two {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left right : CPolynomial F}
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, right]).size) :
    isNontrivialProperChild parent right = true := by
  by_cases hleft : isNontrivialProperChild parent left = true
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hright] at hsize
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hright] at hsize

theorem third_proper_of_triple_filter_size_ge_two_of_not_left {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left middle right : CPolynomial F}
    (hleft : ¬ isNontrivialProperChild parent left = true)
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, middle, right]).size) :
    isNontrivialProperChild parent right = true := by
  by_cases hmiddle : isNontrivialProperChild parent middle = true
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hmiddle, hright] at hsize
  · by_cases hright : isNontrivialProperChild parent right = true
    · exact hright
    · simp [nontrivialProperChildren, hleft, hmiddle, hright] at hsize

theorem quotientAfterChild_root_of_not_child_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {a : F}
    (hdiv : child.toPoly ∣ parent.toPoly)
    (hparent : CPolynomial.eval a parent = 0)
    (hchild : CPolynomial.eval a child ≠ 0) :
    CPolynomial.eval a (quotientAfterChild parent child) = 0 := by
  unfold quotientAfterChild
  by_cases hproper : isNontrivialProperChild parent child = true
  · rw [if_pos hproper]
    exact monicNormalize_div_root_of_dvd_of_root_of_ne_root hdiv hparent hchild
  · rw [if_neg hproper]
    exact hparent

theorem val_size_eq_natDegree_add_one_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hp : p ≠ 0) :
    p.val.size = p.natDegree + 1 := by
  cases hs : p.val.size with
  | zero =>
      exfalso
      apply hp
      apply CPolynomial.ext
      exact Array.eq_empty_of_size_eq_zero hs
  | succ n =>
      simp [CPolynomial.natDegree, hs]

theorem val_size_le_of_toPoly_natDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} (hq : q ≠ 0)
    (hdegree : p.toPoly.natDegree ≤ q.toPoly.natDegree) :
    p.val.size ≤ q.val.size := by
  by_cases hp : p = 0
  · subst p
    change 0 ≤ q.val.size
    exact Nat.zero_le _
  · rw [val_size_eq_natDegree_add_one_of_ne_zero hp,
      val_size_eq_natDegree_add_one_of_ne_zero hq]
    rw [CPolynomial.natDegree_toPoly p, CPolynomial.natDegree_toPoly q]
    omega

theorem val_size_lt_of_toPoly_degree_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} (hq : q ≠ 0)
    (hdegree : p.toPoly.degree < q.toPoly.degree) :
    p.val.size < q.val.size := by
  by_cases hp : p = 0
  · subst p
    cases hs : q.val.size with
    | zero =>
        apply False.elim
        apply hq
        apply CPolynomial.ext
        exact Array.eq_empty_of_size_eq_zero hs
    | succ n =>
        change (0 : Nat) < n + 1
        exact Nat.zero_lt_succ n
  · rw [val_size_eq_natDegree_add_one_of_ne_zero hp,
      val_size_eq_natDegree_add_one_of_ne_zero hq]
    rw [CPolynomial.natDegree_toPoly p, CPolynomial.natDegree_toPoly q]
    have hpPoly : p.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff p).not.mpr hp
    have hqPoly : q.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff q).not.mpr hq
    rw [Polynomial.degree_eq_natDegree hpPoly, Polynomial.degree_eq_natDegree hqPoly] at hdegree
    have hnat : p.toPoly.natDegree < q.toPoly.natDegree := by
      exact_mod_cast hdegree
    omega

theorem monicNormalize_size_le_self {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (p : CPolynomial F) :
    (CPolynomial.monicNormalize p).val.size ≤ p.val.size := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  by_cases hp : p = 0
  · subst p
    have hzero : CPolynomial.monicNormalize (0 : CPolynomial F) = 0 := by
      apply (CPolynomial.toPoly_eq_zero_iff _).1
      rw [CPolynomial.monicNormalize_toPoly_eq_normalize, CPolynomial.toPoly_zero, normalize_zero]
    rw [hzero]
  · have hpNorm : CPolynomial.monicNormalize p ≠ 0 := monicNormalize_ne_zero_of_ne_zero hp
    rw [val_size_eq_natDegree_add_one_of_ne_zero hpNorm,
      val_size_eq_natDegree_add_one_of_ne_zero hp]
    rw [CPolynomial.natDegree_toPoly (CPolynomial.monicNormalize p),
      CPolynomial.natDegree_toPoly p]
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    have hpPoly : p.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff p).not.mpr hp
    have hnormPoly : normalize p.toPoly ≠ 0 := by
      rw [← CPolynomial.monicNormalize_toPoly_eq_normalize]
      exact (CPolynomial.toPoly_eq_zero_iff _).not.mpr hpNorm
    have hdegree : (normalize p.toPoly).degree = p.toPoly.degree :=
      Polynomial.degree_normalize
    rw [Polynomial.degree_eq_natDegree hnormPoly,
      Polynomial.degree_eq_natDegree hpPoly] at hdegree
    have hnat : (normalize p.toPoly).natDegree = p.toPoly.natDegree := by
      exact_mod_cast hdegree
    omega

theorem polynomial_natDegree_le_of_degree_le {F : Type*} [Field F]
    {p q : Polynomial F} (hq : q ≠ 0) (hdegree : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree := by
  by_cases hp : p = 0
  · subst p
    exact Nat.zero_le _
  · rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq] at hdegree
    exact_mod_cast hdegree

theorem quotientAfterChild_size_le_parent {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} (hparent : parent ≠ 0) :
    (quotientAfterChild parent child).val.size ≤ parent.val.size := by
  unfold quotientAfterChild
  by_cases hproper : isNontrivialProperChild parent child = true
  · rw [if_pos hproper]
    letI : DecidableEq F := instDecidableEqOfLawfulBEq
    apply val_size_le_of_toPoly_natDegree_le hparent
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    change (normalize (CPolynomial.div parent child).toPoly).natDegree ≤
      parent.toPoly.natDegree
    rw [CPolynomial.div_toPoly_eq_div]
    apply polynomial_natDegree_le_of_degree_le
    · exact (CPolynomial.toPoly_eq_zero_iff parent).not.mpr hparent
    · rw [Polynomial.degree_normalize]
      exact Polynomial.degree_div_le parent.toPoly child.toPoly
  · rw [if_neg hproper]

theorem toPoly_ne_one_of_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hp : p ≠ 1) :
    p.toPoly ≠ 1 := by
  intro hpoly
  apply hp
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, hpoly, CPolynomial.toPoly_one]

theorem eq_of_toPoly_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {p q : CPolynomial F}
    (hpoly : p.toPoly = q.toPoly) : p = q := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, hpoly]

theorem eq_of_monic_toPoly_dvd_of_natDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {p q : CPolynomial F}
    (hp : p.toPoly.Monic) (hq : q.toPoly.Monic)
    (hdvd : p.toPoly ∣ q.toPoly)
    (hdegree : q.toPoly.natDegree ≤ p.toPoly.natDegree) :
    q = p := by
  apply eq_of_toPoly_eq
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hq hdvd hdegree

theorem monicNormalize_toPoly_degree_pos_of_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent p : CPolynomial F}
    (hproper : isNontrivialProperChild parent (CPolynomial.monicNormalize p) = true) :
    0 < (CPolynomial.monicNormalize p).toPoly.degree := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  unfold isNontrivialProperChild at hproper
  simp at hproper
  have hpNormNe : CPolynomial.monicNormalize p ≠ 0 := hproper.1.1
  have hpNormNotOne : CPolynomial.monicNormalize p ≠ 1 := hproper.1.2
  have hpPoly : p.toPoly ≠ 0 := by
    intro hpZero
    apply hpNormNe
    exact (CPolynomial.toPoly_eq_zero_iff _).1 (by
      rw [CPolynomial.monicNormalize_toPoly_eq_normalize, hpZero, normalize_zero])
  have hmonic : (CPolynomial.monicNormalize p).toPoly.Monic := by
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    exact Polynomial.monic_normalize hpPoly
  exact (Polynomial.Monic.degree_pos hmonic).2
    (toPoly_ne_one_of_ne_one hpNormNotOne)

theorem quotientAfterChild_size_lt_parent_of_monicNormalize_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent childSource : CPolynomial F} (hparent : parent ≠ 0)
    (hproper :
      isNontrivialProperChild parent (CPolynomial.monicNormalize childSource) = true) :
    (quotientAfterChild parent (CPolynomial.monicNormalize childSource)).val.size <
      parent.val.size := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  unfold quotientAfterChild
  rw [if_pos hproper]
  apply val_size_lt_of_toPoly_degree_lt hparent
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
  change
    (normalize
      (CPolynomial.div parent (CPolynomial.monicNormalize childSource)).toPoly).degree <
        parent.toPoly.degree
  rw [CPolynomial.div_toPoly_eq_div, Polynomial.degree_normalize]
  exact Polynomial.degree_div_lt
    ((CPolynomial.toPoly_eq_zero_iff parent).not.mpr hparent)
    (monicNormalize_toPoly_degree_pos_of_proper hproper)

theorem div_ne_zero_of_dvd_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hdiv : child.toPoly ∣ parent.toPoly) (hparent : parent ≠ 0)
    (hchild : child ≠ 0) :
    CPolynomial.div parent child ≠ 0 := by
  intro hquot
  have hparentPoly : parent.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff parent).not.mpr hparent
  have hchildPoly : child.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff child).not.mpr hchild
  rcases hdiv with ⟨r, hr⟩
  have hquotPoly : parent.toPoly / child.toPoly = 0 := by
    have h := congrArg CPolynomial.toPoly hquot
    rw [CPolynomial.div_toPoly_eq_div] at h
    exact h
  have hdivPoly : parent.toPoly / child.toPoly = r := by
    exact (EuclideanDomain.eq_div_of_mul_eq_right hchildPoly hr.symm).symm
  have hrzero : r = 0 := by
    rw [← hdivPoly]
    exact hquotPoly
  apply hparentPoly
  rw [hr, hrzero]
  simp

theorem quotientAfterChild_ne_zero_of_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hdiv : child.toPoly ∣ parent.toPoly) (hparent : parent ≠ 0) :
    quotientAfterChild parent child ≠ 0 := by
  unfold quotientAfterChild
  by_cases hproper : isNontrivialProperChild parent child = true
  · rw [if_pos hproper]
    have hchild : child ≠ 0 := by
      unfold isNontrivialProperChild at hproper
      simp at hproper
      exact hproper.1.1
    exact monicNormalize_ne_zero_of_ne_zero
      (div_ne_zero_of_dvd_of_ne_zero hdiv hparent hchild)
  · rw [if_neg hproper]
    exact hparent

theorem quotientAfterChild_toPoly_dvd_parent {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hdiv : child.toPoly ∣ parent.toPoly) :
    (quotientAfterChild parent child).toPoly ∣ parent.toPoly := by
  unfold quotientAfterChild
  by_cases hproper : isNontrivialProperChild parent child = true
  · rw [if_pos hproper]
    have hchild : child ≠ 0 := by
      unfold isNontrivialProperChild at hproper
      simp at hproper
      exact hproper.1.1
    have hchildPoly : child.toPoly ≠ 0 :=
      (CPolynomial.toPoly_eq_zero_iff child).not.mpr hchild
    rcases hdiv with ⟨r, hr⟩
    have hquotPoly : parent.toPoly / child.toPoly = r := by
      exact (EuclideanDomain.eq_div_of_mul_eq_right hchildPoly hr.symm).symm
    have hquot_dvd_parent : parent.toPoly / child.toPoly ∣ parent.toPoly := by
      rw [hquotPoly]
      exact ⟨child.toPoly, by
        rw [hr]
        exact _root_.mul_comm child.toPoly r⟩
    have hdivC : (CPolynomial.div parent child).toPoly ∣ parent.toPoly := by
      rw [CPolynomial.div_toPoly_eq_div]
      exact hquot_dvd_parent
    exact (toPoly_monicNormalize_dvd_self (CPolynomial.div parent child)).trans hdivC
  · rw [if_neg hproper]

theorem child_quotient_natDegree_le_parent {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hproper : isNontrivialProperChild parent child = true)
    (hdiv : child.toPoly ∣ parent.toPoly) (hparent : parent ≠ 0) :
    child.toPoly.natDegree + (quotientAfterChild parent child).toPoly.natDegree ≤
      parent.toPoly.natDegree := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  have hchild : child ≠ 0 := by
    unfold isNontrivialProperChild at hproper
    simp at hproper
    exact hproper.1.1
  have hparentPoly : parent.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff parent).not.mpr hparent
  have hchildPoly : child.toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff child).not.mpr hchild
  have hdegreeLe : child.toPoly.degree ≤ parent.toPoly.degree :=
    Polynomial.degree_le_of_dvd hdiv hparentPoly
  have hdegreeAdd :
      child.toPoly.degree + (parent.toPoly / child.toPoly).degree =
        parent.toPoly.degree :=
    Polynomial.degree_add_div hchildPoly hdegreeLe
  have hquotC : CPolynomial.div parent child ≠ 0 :=
    div_ne_zero_of_dvd_of_ne_zero hdiv hparent hchild
  have hnormC : CPolynomial.monicNormalize (CPolynomial.div parent child) ≠ 0 :=
    monicNormalize_ne_zero_of_ne_zero hquotC
  have hnormPoly :
      normalize (parent.toPoly / child.toPoly) ≠ 0 := by
    have hnormPolyC :
        (CPolynomial.monicNormalize (CPolynomial.div parent child)).toPoly ≠ 0 :=
      (CPolynomial.toPoly_eq_zero_iff _).not.mpr hnormC
    simpa [CPolynomial.monicNormalize_toPoly_eq_normalize,
      CPolynomial.div_toPoly_eq_div] using hnormPolyC
  unfold quotientAfterChild
  rw [if_pos hproper]
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
  change child.toPoly.natDegree +
      (normalize (CPolynomial.div parent child).toPoly).natDegree ≤
    parent.toPoly.natDegree
  rw [CPolynomial.div_toPoly_eq_div]
  have hdegreeAddNorm :
      child.toPoly.degree + (normalize (parent.toPoly / child.toPoly)).degree =
        parent.toPoly.degree := by
    rw [Polynomial.degree_normalize]
    exact hdegreeAdd
  rw [Polynomial.degree_eq_natDegree hchildPoly,
    Polynomial.degree_eq_natDegree hnormPoly,
    Polynomial.degree_eq_natDegree hparentPoly] at hdegreeAddNorm
  have hnat :
      child.toPoly.natDegree + (normalize (parent.toPoly / child.toPoly)).natDegree =
        parent.toPoly.natDegree := by
    exact_mod_cast hdegreeAddNorm
  exact le_of_eq hnat

noncomputable def splitWork {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Nat :=
  2 * p.toPoly.natDegree - 1

noncomputable def stackWork {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    List (CPolynomial F) → Nat
  | [] => 0
  | p :: ps => splitWork p + stackWork ps

noncomputable def normSplitWork {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Nat :=
  splitWork (CPolynomial.monicNormalize p)

noncomputable def normStackWork {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    List (CPolynomial F) → Nat
  | [] => 0
  | p :: ps => normSplitWork p + normStackWork ps

theorem stackWork_append {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ xs ys : List (CPolynomial F),
      stackWork (xs ++ ys) = stackWork xs + stackWork ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys
      simp [stackWork]
  | cons x xs ih =>
      intro ys
      simp [stackWork, ih, Nat.add_assoc]

theorem stackWork_push {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (out : Array (CPolynomial F)) (x : CPolynomial F) :
    stackWork (out.push x).toList = stackWork out.toList + splitWork x := by
  rw [show (out.push x).toList = out.toList ++ [x] by simp]
  rw [stackWork_append]
  simp [stackWork]

theorem stackWork_eraseDups_fold_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ (xs : List (CPolynomial F)) (out : Array (CPolynomial F)),
      stackWork (List.foldl
          (fun out x ↦ if x ∈ out then out else out.push x) out xs).toList ≤
        stackWork out.toList + stackWork xs := by
  intro xs
  induction xs with
  | nil =>
      intro out
      simp [stackWork]
  | cons x xs ih =>
      intro out
      simp only [List.foldl_cons]
      by_cases hx : x ∈ out
      · have hle := ih out
        simp [hx, stackWork] at hle ⊢
        omega
      · have hle := ih (out.push x)
        rw [stackWork_push] at hle
        simp [hx, stackWork] at hle ⊢
        omega

theorem stackWork_eraseDups_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (xs : Array (CPolynomial F)) :
    stackWork xs.eraseDups.toList ≤ stackWork xs.toList := by
  unfold Array.eraseDups
  rcases xs with ⟨l⟩
  simpa [stackWork] using
    (stackWork_eraseDups_fold_le (F := F) l #[])

theorem stackWork_eraseDups_triple_dup_right_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (x y : CPolynomial F) :
    stackWork (#[x, y, y].eraseDups).toList ≤ splitWork x + splitWork y := by
  unfold Array.eraseDups
  by_cases hxy : x = y
  · subst y
    simp [stackWork]
  · simp
    have hyx : ¬ y = x := fun hyx ↦ hxy hyx.symm
    simp [hyx, stackWork]

theorem normStackWork_append {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ xs ys : List (CPolynomial F),
      normStackWork (xs ++ ys) = normStackWork xs + normStackWork ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys
      simp [normStackWork]
  | cons x xs ih =>
      intro ys
      simp [normStackWork, ih, Nat.add_assoc]

theorem monicNormalize_toPoly_natDegree_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (p : CPolynomial F) :
    (CPolynomial.monicNormalize p).toPoly.natDegree = p.toPoly.natDegree := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  by_cases hp : p = 0
  · subst p
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize, CPolynomial.toPoly_zero, normalize_zero]
  · have hpNorm : CPolynomial.monicNormalize p ≠ 0 :=
      monicNormalize_ne_zero_of_ne_zero hp
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    have hpPoly : p.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff p).not.mpr hp
    have hnormPoly : normalize p.toPoly ≠ 0 := by
      rw [← CPolynomial.monicNormalize_toPoly_eq_normalize]
      exact (CPolynomial.toPoly_eq_zero_iff _).not.mpr hpNorm
    have hdegree : (normalize p.toPoly).degree = p.toPoly.degree :=
      Polynomial.degree_normalize
    rw [Polynomial.degree_eq_natDegree hnormPoly,
      Polynomial.degree_eq_natDegree hpPoly] at hdegree
    exact_mod_cast hdegree

theorem monicNormalize_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    CPolynomial.monicNormalize (0 : CPolynomial F) = 0 := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  apply (CPolynomial.toPoly_eq_zero_iff _).1
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize, CPolynomial.toPoly_zero, normalize_zero]

theorem splitWork_monicNormalize_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (p : CPolynomial F) :
    splitWork (CPolynomial.monicNormalize p) = splitWork p := by
  unfold splitWork
  rw [monicNormalize_toPoly_natDegree_eq]

theorem normSplitWork_eq_splitWork {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (p : CPolynomial F) :
    normSplitWork p = splitWork p := by
  unfold normSplitWork
  exact splitWork_monicNormalize_eq p

theorem normStackWork_eq_stackWork {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ xs : List (CPolynomial F), normStackWork xs = stackWork xs := by
  intro xs
  induction xs with
  | nil =>
      simp [normStackWork, stackWork]
  | cons x xs ih =>
      simp [normStackWork, stackWork, normSplitWork_eq_splitWork, ih]

theorem splitWork_pos_of_natDegree_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hdegree : 0 < p.toPoly.natDegree) :
    1 ≤ splitWork p := by
  unfold splitWork
  omega

theorem normSplitWork_pos_of_monicNormalize_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F}
    (hzero : CPolynomial.monicNormalize p ≠ 0)
    (hone : CPolynomial.monicNormalize p ≠ 1) :
    1 ≤ normSplitWork p := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  unfold normSplitWork
  apply splitWork_pos_of_natDegree_pos
  apply Polynomial.natDegree_pos_iff_degree_pos.mpr
  have hpPoly : p.toPoly ≠ 0 := by
    intro hpZero
    apply hzero
    apply (CPolynomial.toPoly_eq_zero_iff _).1
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize, hpZero, normalize_zero]
  have hmonic : (CPolynomial.monicNormalize p).toPoly.Monic := by
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
    exact Polynomial.monic_normalize hpPoly
  exact (Polynomial.Monic.degree_pos hmonic).2
    (toPoly_ne_one_of_ne_one hone)

theorem monicNormalize_toPoly_monic_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {p : CPolynomial F} (hp : p ≠ 0) :
    (CPolynomial.monicNormalize p).toPoly.Monic := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
  exact Polynomial.monic_normalize ((CPolynomial.toPoly_eq_zero_iff p).not.mpr hp)

theorem splitWork_pos_of_monic_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hmonic : p.toPoly.Monic)
    (_hzero : p ≠ 0) (hone : p ≠ 1) :
    1 ≤ splitWork p := by
  apply splitWork_pos_of_natDegree_pos
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    ((Polynomial.Monic.degree_pos hmonic).2 (toPoly_ne_one_of_ne_one hone))

theorem toPoly_natDegree_pos_of_monic_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hmonic : p.toPoly.Monic)
    (_hzero : p ≠ 0) (hone : p ≠ 1) :
    0 < p.toPoly.natDegree := by
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    ((Polynomial.Monic.degree_pos hmonic).2 (toPoly_ne_one_of_ne_one hone))

theorem normSplitWork_pos_of_monic_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hmonic : p.toPoly.Monic)
    (hzero : p ≠ 0) (hone : p ≠ 1) :
    1 ≤ normSplitWork p := by
  rw [normSplitWork_eq_splitWork]
  exact splitWork_pos_of_monic_ne_zero_ne_one hmonic hzero hone

theorem quotientAfterChild_toPoly_monic_of_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hparentMonic : parent.toPoly.Monic)
    (hdiv : child.toPoly ∣ parent.toPoly) (hparent : parent ≠ 0) :
    (quotientAfterChild parent child).toPoly.Monic := by
  unfold quotientAfterChild
  by_cases hproper : isNontrivialProperChild parent child = true
  · rw [if_pos hproper]
    have hchild : child ≠ 0 := by
      unfold isNontrivialProperChild at hproper
      simp at hproper
      exact hproper.1.1
    exact monicNormalize_toPoly_monic_of_ne_zero
      (div_ne_zero_of_dvd_of_ne_zero hdiv hparent hchild)
  · rw [if_neg hproper]
    exact hparentMonic

theorem eq_of_monic_dvd_of_val_size_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {divisor parent : CPolynomial F}
    (hdivisorMonic : divisor.toPoly.Monic) (hparentMonic : parent.toPoly.Monic)
    (hdiv : divisor.toPoly ∣ parent.toPoly)
    (hdivisor : divisor ≠ 0) (hparent : parent ≠ 0)
    (hsize : parent.val.size ≤ divisor.val.size) :
    parent = divisor := by
  apply eq_of_monic_toPoly_dvd_of_natDegree_le hdivisorMonic hparentMonic hdiv
  rw [val_size_eq_natDegree_add_one_of_ne_zero hparent,
    val_size_eq_natDegree_add_one_of_ne_zero hdivisor] at hsize
  rw [CPolynomial.natDegree_toPoly parent, CPolynomial.natDegree_toPoly divisor] at hsize
  omega

theorem eq_of_not_proper_of_monic_dvd {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hchildMonic : child.toPoly.Monic) (hparentMonic : parent.toPoly.Monic)
    (hdiv : child.toPoly ∣ parent.toPoly)
    (hchildNe : child ≠ 0) (hparentNe : parent ≠ 0) (hchildNotOne : child ≠ 1)
    (hnotProper : ¬ isNontrivialProperChild parent child = true) :
    parent = child := by
  have hnotSize : ¬ child.val.size < parent.val.size := by
    intro hsize
    apply hnotProper
    unfold isNontrivialProperChild
    simp [hchildNe, hchildNotOne, hsize]
  exact eq_of_monic_dvd_of_val_size_le hchildMonic hparentMonic hdiv
    hchildNe hparentNe (Nat.le_of_not_gt hnotSize)

def normStackReady {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (stack : List (CPolynomial F)) : Prop :=
  ∀ g, g ∈ stack → CPolynomial.monicNormalize g ≠ 0 ∧ CPolynomial.monicNormalize g ≠ 1

theorem normStackReady_tail {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {g : CPolynomial F} {stack : List (CPolynomial F)}
    (hready : normStackReady (g :: stack)) :
    normStackReady stack := by
  intro child hchild
  exact hready child (by simp [hchild])

theorem normStackReady_append {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {xs ys : List (CPolynomial F)}
    (hxs : normStackReady xs) (hys : normStackReady ys) :
    normStackReady (xs ++ ys) := by
  intro g hmem
  rw [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hxs g hmem
  · exact hys g hmem

theorem normStackWork_pos_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {stack : List (CPolynomial F)} {p : CPolynomial F}
    (hready : normStackReady stack) (hmem : p ∈ stack) :
    1 ≤ normStackWork stack := by
  induction stack with
  | nil =>
      simp at hmem
  | cons g stack ih =>
      simp at hmem
      rcases hmem with hmem | hmem
      · subst p
        have hheadReady := hready g (by simp)
        have hpos := normSplitWork_pos_of_monicNormalize_ne_zero_ne_one
          hheadReady.1 hheadReady.2
        simp [normStackWork]
        omega
      · have htail := ih (normStackReady_tail hready) hmem
        simp [normStackWork]
        omega

theorem normSplitWork_pos_ready {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hpos : 1 ≤ normSplitWork p) :
    CPolynomial.monicNormalize p ≠ 0 ∧ CPolynomial.monicNormalize p ≠ 1 := by
  constructor
  · intro hzero
    unfold normSplitWork splitWork at hpos
    rw [hzero, CPolynomial.toPoly_zero] at hpos
    simp at hpos
  · intro hone
    unfold normSplitWork splitWork at hpos
    rw [hone, CPolynomial.toPoly_one] at hpos
    simp at hpos

theorem normStackWork_tail_le_of_cons_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {fuel : Nat} {g : CPolynomial F} {stack : List (CPolynomial F)}
    (hwork : normStackWork (g :: stack) ≤ fuel + 1)
    (hpos : 1 ≤ normSplitWork g) :
    normStackWork stack ≤ fuel := by
  simp [normStackWork] at hwork
  omega

theorem normStackWork_split_stack_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {fuel : Nat} {g : CPolynomial F} {stack : List (CPolynomial F)}
    {children : Array (CPolynomial F)}
    (hwork : normStackWork (g :: stack) ≤ fuel + 1)
    (hpos : 1 ≤ normSplitWork g)
    (hchildren : stackWork children.toList ≤ normSplitWork g - 1) :
    normStackWork (children.toList ++ stack) ≤ fuel := by
  rw [normStackWork_append]
  rw [normStackWork_eq_stackWork children.toList]
  simp [normStackWork] at hwork
  omega

theorem monicNormalize_toPoly_natDegree_pos_of_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent p : CPolynomial F}
    (hproper : isNontrivialProperChild parent (CPolynomial.monicNormalize p) = true) :
    0 < (CPolynomial.monicNormalize p).toPoly.natDegree := by
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    (monicNormalize_toPoly_degree_pos_of_proper hproper)

theorem splitWork_pair_le_of_natDegree_sum_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left right : CPolynomial F}
    (hleft : 0 < left.toPoly.natDegree)
    (hright : 0 < right.toPoly.natDegree)
    (hsum : left.toPoly.natDegree + right.toPoly.natDegree ≤
      parent.toPoly.natDegree) :
    splitWork left + splitWork right ≤ splitWork parent - 1 := by
  unfold splitWork
  omega

theorem splitWork_triple_le_of_natDegree_sum_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left middle right : CPolynomial F}
    (hleft : 0 < left.toPoly.natDegree)
    (hmiddle : 0 < middle.toPoly.natDegree)
    (hright : 0 < right.toPoly.natDegree)
    (hsum : left.toPoly.natDegree + middle.toPoly.natDegree +
      right.toPoly.natDegree ≤ parent.toPoly.natDegree) :
    splitWork left + (splitWork middle + (splitWork right + 0)) ≤
      splitWork parent - 1 := by
  unfold splitWork
  omega

theorem splitWork_triple_le_of_first_two_pos_natDegree_sum_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left middle right : CPolynomial F}
    (hleft : 0 < left.toPoly.natDegree)
    (hmiddle : 0 < middle.toPoly.natDegree)
    (hsum : left.toPoly.natDegree + middle.toPoly.natDegree +
      right.toPoly.natDegree ≤ parent.toPoly.natDegree) :
    splitWork left + (splitWork middle + (splitWork right + 0)) ≤
      splitWork parent - 1 := by
  unfold splitWork
  by_cases hright : 0 < right.toPoly.natDegree
  · omega
  · have hrightZero : right.toPoly.natDegree = 0 := by omega
    omega

theorem proper_child_of_proper_intermediate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent intermediate child : CPolynomial F}
    (hproper : isNontrivialProperChild intermediate child = true)
    (hsize : intermediate.val.size ≤ parent.val.size) :
    isNontrivialProperChild parent child = true := by
  unfold isNontrivialProperChild at hproper ⊢
  simp at hproper ⊢
  exact ⟨hproper.1, lt_of_lt_of_le hproper.2 hsize⟩

theorem child_ne_zero_of_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hproper : isNontrivialProperChild parent child = true) :
    child ≠ 0 := by
  unfold isNontrivialProperChild at hproper
  simp at hproper
  exact hproper.1.1

theorem child_ne_one_of_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {child : CPolynomial F} {a : F} (hroot : CPolynomial.eval a child = 0) :
  child ≠ 1 := by
  intro hchild
  subst child
  rw [CPolynomial.eval_one] at hroot
  exact one_ne_zero hroot

theorem proper_child_of_ne_zero_root_size_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {a : F}
    (hchild : child ≠ 0) (hroot : CPolynomial.eval a child = 0)
    (hsize : child.val.size < parent.val.size) :
    isNontrivialProperChild parent child = true := by
  unfold isNontrivialProperChild
  simp [hchild, child_ne_one_of_root hroot, hsize]

theorem child_size_le_fuel_of_proper_of_parent_size_le_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {fuel : Nat}
    (hproper : isNontrivialProperChild parent child = true)
    (hparent : parent.val.size ≤ fuel + 1) :
    child.val.size ≤ fuel := by
  unfold isNontrivialProperChild at hproper
  simp at hproper
  omega

theorem split_child_or_quotient_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {a : F}
    (hdiv : child.toPoly ∣ parent.toPoly)
    (hparent : CPolynomial.eval a parent = 0) :
    (isNontrivialProperChild parent child = true ∧ CPolynomial.eval a child = 0) ∨
      CPolynomial.eval a (quotientAfterChild parent child) = 0 := by
  by_cases hchild : CPolynomial.eval a child = 0
  · by_cases hproper : isNontrivialProperChild parent child = true
    · exact Or.inl ⟨hproper, hchild⟩
    · right
      unfold quotientAfterChild
      rw [if_neg hproper]
      exact hparent
  · right
    exact quotientAfterChild_root_of_not_child_root hdiv hparent hchild

end FiniteField

end Roots

end CPolynomial

end CompPoly
