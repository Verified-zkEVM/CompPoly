/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Correctness Surface for Las Vegas Splitting

Phase-1 theorem surfaces for the bounded Las Vegas splitter. The executable
backend is deterministic for every fixed `ProbeFamily`; the hard split
preservation proofs are intentionally explicit `sorry`s here and are phase-3
proof debt.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Field-root products satisfy the Las Vegas splitter input predicate. -/
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

private theorem eval_reduceModWith_eq_self_of_root {F : Type*}
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

private theorem eval_powModWith_eq_pow {F : Type*}
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

private theorem nontrivialProperChildren_mem_of_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {children : Array (CPolynomial F)}
    (hmem : child ∈ children.toList)
    (hproper : isNontrivialProperChild parent child = true) :
    child ∈ (nontrivialProperChildren parent children).toList := by
  unfold nontrivialProperChildren
  simp [hmem, hproper]

private theorem proper_of_mem_nontrivialProperChildren {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {children : Array (CPolynomial F)}
    (hmem : child ∈ (nontrivialProperChildren parent children).toList) :
    isNontrivialProperChild parent child = true := by
  unfold nontrivialProperChildren at hmem
  simp at hmem
  rcases hmem with ⟨_hmem, hproper⟩
  exact hproper

private lemma mem_eraseDups_fold {α : Type*} [BEq α] [LawfulBEq α]
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

private lemma mem_of_mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs.eraseDups) : a ∈ xs := by
  unfold Array.eraseDups at h
  rcases xs with ⟨l⟩
  simp at h ⊢
  have hh := mem_eraseDups_fold a l #[] h
  simpa using hh

private lemma mem_eraseDups_fold_of_mem {α : Type*} [BEq α] [LawfulBEq α]
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

private lemma mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {a : α} (h : a ∈ xs) : a ∈ xs.eraseDups := by
  unfold Array.eraseDups
  rcases xs with ⟨l⟩
  simp at h ⊢
  exact mem_eraseDups_fold_of_mem a l #[] (Or.inr h)

private theorem middle_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left {F : Type*}
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

private theorem right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left {F : Type*}
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

private theorem right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle {F : Type*}
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

private theorem left_proper_of_pair_filter_size_ge_two {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left right : CPolynomial F}
    (hsize : 2 ≤ (nontrivialProperChildren parent #[left, right]).size) :
    isNontrivialProperChild parent left = true := by
  by_cases hleft : isNontrivialProperChild parent left = true
  · exact hleft
  · by_cases hright : isNontrivialProperChild parent right = true
    · simp [nontrivialProperChildren, hleft, hright] at hsize
    · simp [nontrivialProperChildren, hleft, hright] at hsize

private theorem right_proper_of_pair_filter_size_ge_two {F : Type*}
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

private theorem third_proper_of_triple_filter_size_ge_two_of_not_left {F : Type*}
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

private theorem quotientAfterChild_root_of_not_child_root {F : Type*}
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

private theorem val_size_eq_natDegree_add_one_of_ne_zero {F : Type*}
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

private theorem val_size_le_of_toPoly_natDegree_le {F : Type*}
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

private theorem val_size_lt_of_toPoly_degree_lt {F : Type*}
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

private theorem monicNormalize_size_le_self {F : Type*}
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

private theorem polynomial_natDegree_le_of_degree_le {F : Type*} [Field F]
    {p q : Polynomial F} (hq : q ≠ 0) (hdegree : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree := by
  by_cases hp : p = 0
  · subst p
    exact Nat.zero_le _
  · rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq] at hdegree
    exact_mod_cast hdegree

private theorem quotientAfterChild_size_le_parent {F : Type*}
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

private theorem toPoly_ne_one_of_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hp : p ≠ 1) :
    p.toPoly ≠ 1 := by
  intro hpoly
  apply hp
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, hpoly, CPolynomial.toPoly_one]

private theorem eq_of_toPoly_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {p q : CPolynomial F}
    (hpoly : p.toPoly = q.toPoly) : p = q := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, hpoly]

private theorem eq_of_monic_toPoly_dvd_of_natDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {p q : CPolynomial F}
    (hp : p.toPoly.Monic) (hq : q.toPoly.Monic)
    (hdvd : p.toPoly ∣ q.toPoly)
    (hdegree : q.toPoly.natDegree ≤ p.toPoly.natDegree) :
    q = p := by
  apply eq_of_toPoly_eq
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hq hdvd hdegree

private theorem monicNormalize_toPoly_degree_pos_of_proper {F : Type*}
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

private theorem quotientAfterChild_size_lt_parent_of_monicNormalize_proper {F : Type*}
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
  change (normalize (CPolynomial.div parent (CPolynomial.monicNormalize childSource)).toPoly).degree <
    parent.toPoly.degree
  rw [CPolynomial.div_toPoly_eq_div, Polynomial.degree_normalize]
  exact Polynomial.degree_div_lt
    ((CPolynomial.toPoly_eq_zero_iff parent).not.mpr hparent)
    (monicNormalize_toPoly_degree_pos_of_proper hproper)

private theorem div_ne_zero_of_dvd_of_ne_zero {F : Type*}
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

private theorem quotientAfterChild_ne_zero_of_dvd {F : Type*}
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

private theorem child_quotient_natDegree_le_parent {F : Type*}
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

private noncomputable def splitWork {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Nat :=
  2 * p.toPoly.natDegree - 1

private noncomputable def stackWork {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    List (CPolynomial F) → Nat
  | [] => 0
  | p :: ps => splitWork p + stackWork ps

private noncomputable def normSplitWork {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) : Nat :=
  splitWork (CPolynomial.monicNormalize p)

private noncomputable def normStackWork {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    List (CPolynomial F) → Nat
  | [] => 0
  | p :: ps => normSplitWork p + normStackWork ps

private theorem stackWork_append {F : Type*}
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

private theorem stackWork_push {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (out : Array (CPolynomial F)) (x : CPolynomial F) :
    stackWork (out.push x).toList = stackWork out.toList + splitWork x := by
  rw [show (out.push x).toList = out.toList ++ [x] by simp]
  rw [stackWork_append]
  simp [stackWork]

private theorem stackWork_eraseDups_fold_le {F : Type*}
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

private theorem stackWork_eraseDups_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (xs : Array (CPolynomial F)) :
    stackWork xs.eraseDups.toList ≤ stackWork xs.toList := by
  unfold Array.eraseDups
  rcases xs with ⟨l⟩
  simp
  simpa [stackWork] using
    (stackWork_eraseDups_fold_le (F := F) l #[])

private theorem stackWork_eraseDups_triple_dup_right_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (x y : CPolynomial F) :
    stackWork (#[x, y, y].eraseDups).toList ≤ splitWork x + splitWork y := by
  unfold Array.eraseDups
  by_cases hxy : x = y
  · subst y
    simp [stackWork]
  · simp [hxy, stackWork]
    have hyx : ¬ y = x := fun hyx ↦ hxy hyx.symm
    simp [hxy, hyx, stackWork]

private theorem normStackWork_append {F : Type*}
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

private theorem monicNormalize_toPoly_natDegree_eq {F : Type*}
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

private theorem splitWork_monicNormalize_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (p : CPolynomial F) :
    splitWork (CPolynomial.monicNormalize p) = splitWork p := by
  unfold splitWork
  rw [monicNormalize_toPoly_natDegree_eq]

private theorem normSplitWork_eq_splitWork {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (p : CPolynomial F) :
    normSplitWork p = splitWork p := by
  unfold normSplitWork
  exact splitWork_monicNormalize_eq p

private theorem normStackWork_eq_stackWork {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] :
    ∀ xs : List (CPolynomial F), normStackWork xs = stackWork xs := by
  intro xs
  induction xs with
  | nil =>
      simp [normStackWork, stackWork]
  | cons x xs ih =>
      simp [normStackWork, stackWork, normSplitWork_eq_splitWork, ih]

private theorem splitWork_pos_of_natDegree_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hdegree : 0 < p.toPoly.natDegree) :
    1 ≤ splitWork p := by
  unfold splitWork
  omega

private theorem normSplitWork_pos_of_monicNormalize_ne_zero_ne_one {F : Type*}
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

private theorem monicNormalize_toPoly_monic_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {p : CPolynomial F} (hp : p ≠ 0) :
    (CPolynomial.monicNormalize p).toPoly.Monic := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
  exact Polynomial.monic_normalize ((CPolynomial.toPoly_eq_zero_iff p).not.mpr hp)

private theorem splitWork_pos_of_monic_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hmonic : p.toPoly.Monic)
    (_hzero : p ≠ 0) (hone : p ≠ 1) :
    1 ≤ splitWork p := by
  apply splitWork_pos_of_natDegree_pos
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    ((Polynomial.Monic.degree_pos hmonic).2 (toPoly_ne_one_of_ne_one hone))

private theorem toPoly_natDegree_pos_of_monic_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hmonic : p.toPoly.Monic)
    (_hzero : p ≠ 0) (hone : p ≠ 1) :
    0 < p.toPoly.natDegree := by
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    ((Polynomial.Monic.degree_pos hmonic).2 (toPoly_ne_one_of_ne_one hone))

private theorem normSplitWork_pos_of_monic_ne_zero_ne_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hmonic : p.toPoly.Monic)
    (hzero : p ≠ 0) (hone : p ≠ 1) :
    1 ≤ normSplitWork p := by
  rw [normSplitWork_eq_splitWork]
  exact splitWork_pos_of_monic_ne_zero_ne_one hmonic hzero hone

private theorem quotientAfterChild_toPoly_monic_of_dvd {F : Type*}
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

private theorem eq_of_monic_dvd_of_val_size_le {F : Type*}
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

private theorem eq_of_not_proper_of_monic_dvd {F : Type*}
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

private def normStackReady {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (stack : List (CPolynomial F)) : Prop :=
  ∀ g, g ∈ stack → CPolynomial.monicNormalize g ≠ 0 ∧ CPolynomial.monicNormalize g ≠ 1

private theorem normStackReady_tail {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {g : CPolynomial F} {stack : List (CPolynomial F)}
    (hready : normStackReady (g :: stack)) :
    normStackReady stack := by
  intro child hchild
  exact hready child (by simp [hchild])

private theorem normStackReady_append {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {xs ys : List (CPolynomial F)}
    (hxs : normStackReady xs) (hys : normStackReady ys) :
    normStackReady (xs ++ ys) := by
  intro g hmem
  rw [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hxs g hmem
  · exact hys g hmem

private theorem normStackWork_tail_le_of_cons_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {fuel : Nat} {g : CPolynomial F} {stack : List (CPolynomial F)}
    (hwork : normStackWork (g :: stack) ≤ fuel + 1)
    (hpos : 1 ≤ normSplitWork g) :
    normStackWork stack ≤ fuel := by
  simp [normStackWork] at hwork
  omega

private theorem normStackWork_split_stack_le {F : Type*}
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

private theorem monicNormalize_toPoly_natDegree_pos_of_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent p : CPolynomial F}
    (hproper : isNontrivialProperChild parent (CPolynomial.monicNormalize p) = true) :
    0 < (CPolynomial.monicNormalize p).toPoly.natDegree := by
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr
    (monicNormalize_toPoly_degree_pos_of_proper hproper)

private theorem splitWork_pair_le_of_natDegree_sum_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent left right : CPolynomial F}
    (hleft : 0 < left.toPoly.natDegree)
    (hright : 0 < right.toPoly.natDegree)
    (hsum : left.toPoly.natDegree + right.toPoly.natDegree ≤
      parent.toPoly.natDegree) :
    splitWork left + splitWork right ≤ splitWork parent - 1 := by
  unfold splitWork
  omega

private theorem splitWork_triple_le_of_natDegree_sum_le {F : Type*}
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

private theorem splitWork_triple_le_of_first_two_pos_natDegree_sum_le {F : Type*}
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

private theorem proper_child_of_proper_intermediate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent intermediate child : CPolynomial F}
    (hproper : isNontrivialProperChild intermediate child = true)
    (hsize : intermediate.val.size ≤ parent.val.size) :
    isNontrivialProperChild parent child = true := by
  unfold isNontrivialProperChild at hproper ⊢
  simp at hproper ⊢
  exact ⟨hproper.1, lt_of_lt_of_le hproper.2 hsize⟩

private theorem child_ne_zero_of_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F}
    (hproper : isNontrivialProperChild parent child = true) :
    child ≠ 0 := by
  unfold isNontrivialProperChild at hproper
  simp at hproper
  exact hproper.1.1

private theorem child_ne_one_of_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {child : CPolynomial F} {a : F} (hroot : CPolynomial.eval a child = 0) :
  child ≠ 1 := by
  intro hchild
  subst child
  rw [CPolynomial.eval_one] at hroot
  exact one_ne_zero hroot

private theorem proper_child_of_ne_zero_root_size_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {a : F}
    (hchild : child ≠ 0) (hroot : CPolynomial.eval a child = 0)
    (hsize : child.val.size < parent.val.size) :
    isNontrivialProperChild parent child = true := by
  unfold isNontrivialProperChild
  simp [hchild, child_ne_one_of_root hroot, hsize]

private theorem child_size_le_fuel_of_proper_of_parent_size_le_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent child : CPolynomial F} {fuel : Nat}
    (hproper : isNontrivialProperChild parent child = true)
    (hparent : parent.val.size ≤ fuel + 1) :
    child.val.size ≤ fuel := by
  unfold isNontrivialProperChild at hproper
  simp at hproper
  omega

private theorem split_child_or_quotient_root {F : Type*}
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

private theorem cantorZassenhausEvenTraceAttemptWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hroot' : CPolynomial.eval a g' = 0 := (monicNormalize_root_iff hg).2 hroot
    have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
      dsimp [tracePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' tracePoly)
    by_cases htraceRoot : CPolynomial.eval a tracePart = 0
    · refine ⟨tracePart, ?_, htraceRoot⟩
      change tracePart ∈ (nontrivialProperChildren g' #[tracePart, complement]).toList
      have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
        simpa [g', h, tracePoly, tracePart, complement] using hsize
      have hproperTrace : isNontrivialProperChild g' tracePart = true :=
        left_proper_of_pair_filter_size_ge_two hsize'
      exact nontrivialProperChildren_mem_of_mem (by simp) hproperTrace
    · have hcomplementRoot : CPolynomial.eval a complement = 0 := by
        dsimp [complement]
        exact quotientAfterChild_root_of_not_child_root hdivTrace hroot' htraceRoot
      refine ⟨complement, ?_, hcomplementRoot⟩
      change complement ∈ (nontrivialProperChildren g' #[tracePart, complement]).toList
      have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
        simpa [g', h, tracePoly, tracePart, complement] using hsize
      have hproperComplement : isNontrivialProperChild g' complement = true :=
        right_proper_of_pair_filter_size_ge_two hsize'
      exact nontrivialProperChildren_mem_of_mem (by simp) hproperComplement
  next hsize =>
    simp at htry

private theorem cantorZassenhausEvenTraceAttemptWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    exact proper_of_mem_nontrivialProperChildren hmem
  next hsize =>
    simp at htry

private theorem cantorZassenhausEvenTraceAttemptWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hg : g ≠ 0) :
    stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
      simpa [g', h, tracePoly, tracePart, complement] using hsize
    have hproperTrace : isNontrivialProperChild g' tracePart = true :=
      left_proper_of_pair_filter_size_ge_two hsize'
    have hproperComplement : isNontrivialProperChild g' complement = true :=
      right_proper_of_pair_filter_size_ge_two hsize'
    have hchildrenList :
        (nontrivialProperChildren g' #[tracePart, complement]).toList =
          [tracePart, complement] := by
      unfold nontrivialProperChildren
      simp [hproperTrace, hproperComplement]
    have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
      dsimp [tracePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' tracePoly)
    have hsum :
        tracePart.toPoly.natDegree + complement.toPoly.natDegree ≤
          g'.toPoly.natDegree := by
      dsimp [complement]
      exact child_quotient_natDegree_le_parent hproperTrace hdivTrace hg'
    have htracePos : 0 < tracePart.toPoly.natDegree := by
      have hproperTrace' :
          isNontrivialProperChild g'
            (CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)) = true := by
        simpa [tracePart] using hproperTrace
      simpa [tracePart] using
        (monicNormalize_toPoly_natDegree_pos_of_proper hproperTrace')
    have hcomplementPos : 0 < complement.toPoly.natDegree := by
      have hproperComplement' :
          isNontrivialProperChild g'
            (CPolynomial.monicNormalize (CPolynomial.div g' tracePart)) = true := by
        simpa [complement, quotientAfterChild, hproperTrace] using hproperComplement
      simpa [complement, quotientAfterChild, hproperTrace] using
        (monicNormalize_toPoly_natDegree_pos_of_proper hproperComplement')
    rw [hchildrenList]
    simp [stackWork]
    have hsum' :
        tracePart.toPoly.natDegree + complement.toPoly.natDegree ≤
          (CPolynomial.monicNormalize g).toPoly.natDegree := by
      simpa [g'] using hsum
    exact splitWork_pair_le_of_natDegree_sum_le htracePos hcomplementPos hsum'
  next _hsize =>
    simp at htry

private theorem cantorZassenhausEvenTraceAttemptWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hg : g ≠ 0) (hmem : child ∈ children.toList) :
    1 ≤ normSplitWork child := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
      simpa [g', h, tracePoly, tracePart, complement] using hsize
    have hproperTrace : isNontrivialProperChild g' tracePart = true :=
      left_proper_of_pair_filter_size_ge_two hsize'
    have hproperComplement : isNontrivialProperChild g' complement = true :=
      right_proper_of_pair_filter_size_ge_two hsize'
    have hchildrenList :
        (nontrivialProperChildren g' #[tracePart, complement]).toList =
          [tracePart, complement] := by
      unfold nontrivialProperChildren
      simp [hproperTrace, hproperComplement]
    rw [hchildrenList] at hmem
    simp at hmem
    rcases hmem with hmem | hmem
    · subst child
      have htraceNe : tracePart ≠ 0 := by
        unfold isNontrivialProperChild at hproperTrace
        simp at hproperTrace
        exact hproperTrace.1.1
      have htraceNotOne : tracePart ≠ 1 := by
        unfold isNontrivialProperChild at hproperTrace
        simp at hproperTrace
        exact hproperTrace.1.2
      have htraceMonic : tracePart.toPoly.Monic := by
        dsimp [tracePart]
        exact monicNormalize_toPoly_monic_of_ne_zero
          (gcdMonic_ne_zero_of_left hg')
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        htraceMonic htraceNe htraceNotOne
    · subst child
      have hcomplementNe : complement ≠ 0 := by
        unfold isNontrivialProperChild at hproperComplement
        simp at hproperComplement
        exact hproperComplement.1.1
      have hcomplementNotOne : complement ≠ 1 := by
        unfold isNontrivialProperChild at hproperComplement
        simp at hproperComplement
        exact hproperComplement.1.2
      have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
        dsimp [tracePart]
        exact (toPoly_monicNormalize_dvd_self _).trans
          (toPoly_gcdMonic_dvd_left g' tracePoly)
      have hg'Monic : g'.toPoly.Monic := by
        dsimp [g']
        exact monicNormalize_toPoly_monic_of_ne_zero hg
      have hcomplementMonic : complement.toPoly.Monic := by
        dsimp [complement]
        exact quotientAfterChild_toPoly_monic_of_dvd hg'Monic hdivTrace hg'
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hcomplementMonic hcomplementNe hcomplementNotOne
  next _hsize =>
    simp at htry

private theorem tryEvenTraceSplitAttemptsWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_root
            M D traceCtx q probes hsplit hg hroot

private theorem tryEvenTraceSplitAttemptsWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F} :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        child ∈ children.toList →
          isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry hmem
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry hmem
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_child_proper
            M D traceCtx q probes hsplit hmem

private theorem tryEvenTraceSplitAttemptsWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_stackWork_le
            M D traceCtx q probes hsplit hg

private theorem tryEvenTraceSplitAttemptsWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        child ∈ children.toList →
          1 ≤ normSplitWork child := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry hmem
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry hmem
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_child_normSplitWork_pos
            M D traceCtx q probes hsplit hg hmem

private theorem cantorZassenhausOddAttemptWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hroot' : CPolynomial.eval a g' = 0 := (monicNormalize_root_iff hg).2 hroot
    have hsize' :
        2 ≤ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups.size := by
      simpa [g', h, s, zeroPart, afterZero, squarePart, afterSquare] using hsize
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    have hzeroMem (hproperZero : isNontrivialProperChild g' zeroPart = true) :
        zeroPart ∈
          ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList := by
      have hraw :
          zeroPart ∈ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).toList :=
        nontrivialProperChildren_mem_of_mem (by simp) hproperZero
      simpa using (mem_eraseDups_of_mem (by simpa using hraw))
    have hsquareMem (hproperSquare : isNontrivialProperChild g' squarePart = true) :
        squarePart ∈
          ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList := by
      have hraw :
          squarePart ∈ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).toList :=
        nontrivialProperChildren_mem_of_mem (by simp) hproperSquare
      simpa using (mem_eraseDups_of_mem (by simpa using hraw))
    have hafterMem (hproperAfter : isNontrivialProperChild g' afterSquare = true) :
        afterSquare ∈
          ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList := by
      have hraw :
          afterSquare ∈ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).toList :=
        nontrivialProperChildren_mem_of_mem (by simp) hproperAfter
      simpa using (mem_eraseDups_of_mem (by simpa using hraw))
    have hafterZeroRoot_of_not_zero
        (hzeroRoot : CPolynomial.eval a zeroPart ≠ 0) :
        CPolynomial.eval a afterZero = 0 := by
      dsimp [afterZero]
      exact quotientAfterChild_root_of_not_child_root hdivZero hroot' hzeroRoot
    have hafterSquareRoot_of_afterZero
        (hafterZeroRoot : CPolynomial.eval a afterZero = 0)
        (hsquareRoot : CPolynomial.eval a squarePart ≠ 0) :
        CPolynomial.eval a afterSquare = 0 := by
      dsimp [afterSquare]
      exact quotientAfterChild_root_of_not_child_root hdivSquare hafterZeroRoot hsquareRoot
    by_cases hzeroRoot : CPolynomial.eval a zeroPart = 0
    · by_cases hproperZero : isNontrivialProperChild g' zeroPart = true
      · refine ⟨zeroPart, hzeroMem hproperZero, hzeroRoot⟩
      · have hafterZeroRoot : CPolynomial.eval a afterZero = 0 := by
          dsimp [afterZero, quotientAfterChild]
          rw [if_neg hproperZero]
          exact hroot'
        by_cases hsquareRoot : CPolynomial.eval a squarePart = 0
        · have hproperSquare :
              isNontrivialProperChild g' squarePart = true :=
            middle_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
              hproperZero hsize'
          refine ⟨squarePart, hsquareMem hproperSquare, hsquareRoot⟩
        · have hafterRoot : CPolynomial.eval a afterSquare = 0 :=
            hafterSquareRoot_of_afterZero hafterZeroRoot hsquareRoot
          have hproperAfter :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
              hproperZero hsize'
          refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
    · have hafterZeroRoot : CPolynomial.eval a afterZero = 0 :=
        hafterZeroRoot_of_not_zero hzeroRoot
      by_cases hsquareRoot : CPolynomial.eval a squarePart = 0
      · by_cases hproperSquare : isNontrivialProperChild g' squarePart = true
        · refine ⟨squarePart, hsquareMem hproperSquare, hsquareRoot⟩
        · have hafterRoot : CPolynomial.eval a afterSquare = 0 := by
            have hafterZeroSizeLe : afterZero.val.size ≤ g'.val.size := by
              dsimp [afterZero]
              exact quotientAfterChild_size_le_parent hg'
            have hnotProperAfterZero :
                ¬ isNontrivialProperChild afterZero squarePart = true := by
              intro hproperAfterZero
              exact hproperSquare
                (proper_child_of_proper_intermediate hproperAfterZero hafterZeroSizeLe)
            dsimp [afterSquare, quotientAfterChild]
            rw [if_neg hnotProperAfterZero]
            exact hafterZeroRoot
          have hproperAfter :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle
              hproperSquare hsize'
          refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
      · have hafterRoot : CPolynomial.eval a afterSquare = 0 :=
          hafterSquareRoot_of_afterZero hafterZeroRoot hsquareRoot
        by_cases hproperSquare : isNontrivialProperChild g' squarePart = true
        · by_cases hproperAfter : isNontrivialProperChild g' afterSquare = true
          · refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
          · by_cases hproperZero : isNontrivialProperChild g' zeroPart = true
            · have hafterZeroNe : afterZero ≠ 0 :=
                quotientAfterChild_ne_zero_of_dvd hdivZero hg'
              have hafterSquareNe : afterSquare ≠ 0 :=
                quotientAfterChild_ne_zero_of_dvd hdivSquare hafterZeroNe
              have hafterZeroSize : afterZero.val.size < g'.val.size := by
                have hproperZero' :
                    isNontrivialProperChild g'
                      (CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)) = true := by
                  simpa [zeroPart] using hproperZero
                simpa [afterZero, zeroPart] using
                  (quotientAfterChild_size_lt_parent_of_monicNormalize_proper
                    (parent := g') (childSource := CPolynomial.gcdMonic g' h)
                    hg' hproperZero')
              have hafterSquareSizeLe : afterSquare.val.size ≤ afterZero.val.size := by
                dsimp [afterSquare]
                exact quotientAfterChild_size_le_parent hafterZeroNe
              have hafterSquareSize : afterSquare.val.size < g'.val.size :=
                lt_of_le_of_lt hafterSquareSizeLe hafterZeroSize
              have hproperAfter' :
                  isNontrivialProperChild g' afterSquare = true :=
                proper_child_of_ne_zero_root_size_lt hafterSquareNe hafterRoot hafterSquareSize
              exact False.elim (hproperAfter hproperAfter')
            · have hproperAfter' :
                isNontrivialProperChild g' afterSquare = true :=
                right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
                  hproperZero hsize'
              exact False.elim (hproperAfter hproperAfter')
        · have hproperAfter :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle
              hproperSquare hsize'
          refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
  next _hsize =>
    simp at htry

private theorem cantorZassenhausOddAttemptWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next _hsize =>
    injection htry with hchildren
    subst children
    have hraw := mem_of_mem_eraseDups (by simpa using hmem)
    exact proper_of_mem_nontrivialProperChildren (by simpa using hraw)
  next _hsize =>
    simp at htry

private theorem cantorZassenhausOddAttemptWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) (hmem : child ∈ children.toList) :
    1 ≤ normSplitWork child := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next _hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hafterZeroNe : afterZero ≠ 0 := by
      dsimp [afterZero]
      exact quotientAfterChild_ne_zero_of_dvd hdivZero hg'
    have hg'Monic : g'.toPoly.Monic := by
      dsimp [g']
      exact monicNormalize_toPoly_monic_of_ne_zero hg
    have hafterZeroMonic : afterZero.toPoly.Monic := by
      dsimp [afterZero]
      exact quotientAfterChild_toPoly_monic_of_dvd hg'Monic hdivZero hg'
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    have hraw := mem_of_mem_eraseDups (by simpa using hmem)
    unfold nontrivialProperChildren at hraw
    simp at hraw
    rcases hraw with ⟨hrawMem, hproper⟩
    rcases hrawMem with hchild | hchild | hchild
    · subst child
      have hzeroNe : zeroPart ≠ 0 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.1
      have hzeroNotOne : zeroPart ≠ 1 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.2
      have hzeroMonic : zeroPart.toPoly.Monic := by
        dsimp [zeroPart]
        exact monicNormalize_toPoly_monic_of_ne_zero
          (gcdMonic_ne_zero_of_left hg')
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hzeroMonic hzeroNe hzeroNotOne
    · subst child
      have hsquareNe : squarePart ≠ 0 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.1
      have hsquareNotOne : squarePart ≠ 1 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.2
      have hsquareMonic : squarePart.toPoly.Monic := by
        dsimp [squarePart]
        exact monicNormalize_toPoly_monic_of_ne_zero
          (gcdMonic_ne_zero_of_left hafterZeroNe)
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hsquareMonic hsquareNe hsquareNotOne
    · subst child
      have hafterNe : afterSquare ≠ 0 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.1
      have hafterNotOne : afterSquare ≠ 1 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.2
      have hafterMonic : afterSquare.toPoly.Monic := by
        dsimp [afterSquare]
        exact quotientAfterChild_toPoly_monic_of_dvd
          hafterZeroMonic hdivSquare hafterZeroNe
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hafterMonic hafterNe hafterNotOne
  next _hsize =>
    simp at htry

set_option maxHeartbeats 800000 in
private theorem cantorZassenhausOddAttemptWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) :
    stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hsize' :
        2 ≤ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups.size := by
      simpa [g', h, s, zeroPart, afterZero, squarePart, afterSquare] using hsize
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hg'Monic : g'.toPoly.Monic := by
      dsimp [g']
      exact monicNormalize_toPoly_monic_of_ne_zero hg
    have hafterZeroNe : afterZero ≠ 0 := by
      dsimp [afterZero]
      exact quotientAfterChild_ne_zero_of_dvd hdivZero hg'
    have hafterZeroMonic : afterZero.toPoly.Monic := by
      dsimp [afterZero]
      exact quotientAfterChild_toPoly_monic_of_dvd hg'Monic hdivZero hg'
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    by_cases hproperZero : isNontrivialProperChild g' zeroPart = true
    · have hzeroPos : 0 < zeroPart.toPoly.natDegree := by
        have hproperZero' :
            isNontrivialProperChild g'
              (CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)) = true := by
          simpa [zeroPart] using hproperZero
        simpa [zeroPart] using
          (monicNormalize_toPoly_natDegree_pos_of_proper hproperZero')
      have hzeroAfterSum :
          zeroPart.toPoly.natDegree + afterZero.toPoly.natDegree ≤
            g'.toPoly.natDegree := by
        dsimp [afterZero]
        exact child_quotient_natDegree_le_parent hproperZero hdivZero hg'
      by_cases hproperSquareAfter : isNontrivialProperChild afterZero squarePart = true
      · have hafterZeroSizeLe : afterZero.val.size ≤ g'.val.size := by
          dsimp [afterZero]
          exact quotientAfterChild_size_le_parent hg'
        have hproperSquareG : isNontrivialProperChild g' squarePart = true :=
          proper_child_of_proper_intermediate hproperSquareAfter hafterZeroSizeLe
        have hsquarePos : 0 < squarePart.toPoly.natDegree := by
          have hproperSquare' :
              isNontrivialProperChild afterZero
                (CPolynomial.monicNormalize
                  (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))) = true := by
            simpa [squarePart] using hproperSquareAfter
          simpa [squarePart] using
            (monicNormalize_toPoly_natDegree_pos_of_proper hproperSquare')
        have hsquareAfterSum :
            squarePart.toPoly.natDegree + afterSquare.toPoly.natDegree ≤
              afterZero.toPoly.natDegree := by
          dsimp [afterSquare]
          exact child_quotient_natDegree_le_parent hproperSquareAfter hdivSquare hafterZeroNe
        have hsum :
            zeroPart.toPoly.natDegree + squarePart.toPoly.natDegree +
              afterSquare.toPoly.natDegree ≤ g'.toPoly.natDegree := by
          omega
        have hraw :
            stackWork
                ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
              splitWork zeroPart + (splitWork squarePart + (splitWork afterSquare + 0)) := by
          have herase :=
            stackWork_eraseDups_le
              (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare])
          by_cases hproperAfterG : isNontrivialProperChild g' afterSquare = true
          · unfold nontrivialProperChildren at herase ⊢
            simp [hproperZero, hproperSquareG, hproperAfterG, stackWork] at herase ⊢
            omega
          · unfold nontrivialProperChildren at herase ⊢
            simp [hproperZero, hproperSquareG, hproperAfterG, stackWork] at herase ⊢
            omega
        have hwork :
            splitWork zeroPart + (splitWork squarePart + (splitWork afterSquare + 0)) ≤
              splitWork g' - 1 :=
          splitWork_triple_le_of_first_two_pos_natDegree_sum_le hzeroPos hsquarePos hsum
        exact le_trans hraw (by simpa [g'] using hwork)
      · have hafterEq : afterSquare = afterZero := by
          dsimp [afterSquare, quotientAfterChild]
          rw [if_neg hproperSquareAfter]
        by_cases hproperSquareG : isNontrivialProperChild g' squarePart = true
        · have hsquareNe : squarePart ≠ 0 := by
            unfold isNontrivialProperChild at hproperSquareG
            simp at hproperSquareG
            exact hproperSquareG.1.1
          have hsquareNotOne : squarePart ≠ 1 := by
            unfold isNontrivialProperChild at hproperSquareG
            simp at hproperSquareG
            exact hproperSquareG.1.2
          have hsquareMonic : squarePart.toPoly.Monic := by
            dsimp [squarePart]
            exact monicNormalize_toPoly_monic_of_ne_zero
              (gcdMonic_ne_zero_of_left hafterZeroNe)
          have hsqEq : afterZero = squarePart :=
            eq_of_not_proper_of_monic_dvd hsquareMonic hafterZeroMonic hdivSquare
              hsquareNe hafterZeroNe hsquareNotOne hproperSquareAfter
          have hafterZeroPos : 0 < afterZero.toPoly.natDegree := by
            rw [hsqEq]
            exact toPoly_natDegree_pos_of_monic_ne_zero_ne_one
              hsquareMonic hsquareNe hsquareNotOne
          have hpair :
              splitWork zeroPart + splitWork afterZero ≤ splitWork g' - 1 :=
            splitWork_pair_le_of_natDegree_sum_le hzeroPos hafterZeroPos hzeroAfterSum
          have hraw :
              stackWork
                  ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
                splitWork zeroPart + splitWork afterZero := by
            rw [hafterEq, hsqEq]
            unfold nontrivialProperChildren
            simp [hproperZero, hproperSquareG]
            exact stackWork_eraseDups_triple_dup_right_le zeroPart afterZero
          exact le_trans hraw (by simpa [g'] using hpair)
        · have hproperAfterG :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle
              hproperSquareG hsize'
          have hafterZeroProper : isNontrivialProperChild g' afterZero = true := by
            simpa [hafterEq] using hproperAfterG
          have hafterZeroPos : 0 < afterZero.toPoly.natDegree := by
            have hafterZeroNe' : afterZero ≠ 0 := by
              unfold isNontrivialProperChild at hafterZeroProper
              simp at hafterZeroProper
              exact hafterZeroProper.1.1
            have hafterZeroNotOne : afterZero ≠ 1 := by
              unfold isNontrivialProperChild at hafterZeroProper
              simp at hafterZeroProper
              exact hafterZeroProper.1.2
            exact toPoly_natDegree_pos_of_monic_ne_zero_ne_one
              hafterZeroMonic hafterZeroNe' hafterZeroNotOne
          have hpair :
              splitWork zeroPart + splitWork afterZero ≤ splitWork g' - 1 :=
            splitWork_pair_le_of_natDegree_sum_le hzeroPos hafterZeroPos hzeroAfterSum
          have hraw :
              stackWork
                  ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
                splitWork zeroPart + splitWork afterZero := by
            rw [hafterEq]
            unfold nontrivialProperChildren
            simp [hproperZero, hproperSquareG, hafterZeroProper, stackWork]
          exact le_trans hraw (by simpa [g'] using hpair)
    · have hafterZeroEq : afterZero = g' := by
        dsimp [afterZero, quotientAfterChild]
        rw [if_neg hproperZero]
      have hproperSquareG :
          isNontrivialProperChild g' squarePart = true :=
        middle_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
          hproperZero hsize'
      have hproperAfterG :
          isNontrivialProperChild g' afterSquare = true :=
        right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
          hproperZero hsize'
      have hproperSquareAfter : isNontrivialProperChild afterZero squarePart = true := by
        simpa [hafterZeroEq] using hproperSquareG
      have hsquarePos : 0 < squarePart.toPoly.natDegree := by
        have hproperSquare' :
            isNontrivialProperChild g'
              (CPolynomial.monicNormalize
                (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))) = true := by
          simpa [squarePart] using hproperSquareG
        simpa [squarePart] using
          (monicNormalize_toPoly_natDegree_pos_of_proper hproperSquare')
      have hafterMonic : afterSquare.toPoly.Monic := by
        dsimp [afterSquare]
        exact quotientAfterChild_toPoly_monic_of_dvd
          (by simpa [hafterZeroEq] using hg'Monic) hdivSquare
          (by simpa [hafterZeroEq] using hg')
      have hafterPos : 0 < afterSquare.toPoly.natDegree := by
        have hafterNe : afterSquare ≠ 0 := by
          unfold isNontrivialProperChild at hproperAfterG
          simp at hproperAfterG
          exact hproperAfterG.1.1
        have hafterNotOne : afterSquare ≠ 1 := by
          unfold isNontrivialProperChild at hproperAfterG
          simp at hproperAfterG
          exact hproperAfterG.1.2
        exact toPoly_natDegree_pos_of_monic_ne_zero_ne_one
          hafterMonic hafterNe hafterNotOne
      have hsquareAfterSum :
          squarePart.toPoly.natDegree + afterSquare.toPoly.natDegree ≤
            g'.toPoly.natDegree := by
        have hsum := child_quotient_natDegree_le_parent hproperSquareAfter hdivSquare
          (by simpa [hafterZeroEq] using hg')
        simpa [hafterZeroEq] using hsum
      have hpair :
          splitWork squarePart + splitWork afterSquare ≤ splitWork g' - 1 :=
        splitWork_pair_le_of_natDegree_sum_le hsquarePos hafterPos hsquareAfterSum
      have hraw :
          stackWork
              ((nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
            splitWork squarePart + splitWork afterSquare := by
        have herase :=
          stackWork_eraseDups_le
            (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare])
        unfold nontrivialProperChildren at herase ⊢
        simp [hproperZero, hproperSquareG, hproperAfterG, stackWork] at herase ⊢
        omega
      exact le_trans hraw (by simpa [g'] using hpair)
  next _hsize =>
    simp at htry

private theorem tryOddSplitAttemptsWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry
      cases htry
  | succ attempts ih =>
      intro offset children htry
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_root M D q probes hsplit hg hroot

private theorem tryOddSplitAttemptsWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F} :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        child ∈ children.toList →
          isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry hmem
      cases htry
  | succ attempts ih =>
      intro offset children htry hmem
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_child_proper M D q probes hsplit hmem

private theorem tryOddSplitAttemptsWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        child ∈ children.toList →
          1 ≤ normSplitWork child := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry hmem
      cases htry
  | succ attempts ih =>
      intro offset children htry hmem
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_child_normSplitWork_pos
            M D q probes hsplit hg hmem

private theorem representedEnumeratedLinearFactors_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (representedLinearFactorsOnly (enumeratedLinearFactors enumeration p)).toList ∧
        IsLinearRootFactorCandidate factor a := by
  refine ⟨CPolynomial.linearFactor a, ?_, linearFactor_isRootFactorCandidate a⟩
  apply representedLinearFactorsOnly_mem_of_mem
  · rw [enumeratedLinearFactors]
    simpa using
      (List.mem_map.mpr
        ⟨a, rootsInFieldByEnumeration_complete enumeration hroot, rfl⟩)
  · exact linearFactor_isRepresentedLinearFactor a

private theorem linearFactor_mem_enumeratedLinearFactors {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.linearFactor a ∈ (enumeratedLinearFactors enumeration p).toList := by
  rw [enumeratedLinearFactors]
  simpa using
    (List.mem_map.mpr
      ⟨a, rootsInFieldByEnumeration_complete enumeration hroot, rfl⟩)

private theorem lasVegasSplitLoopWith_mem_of_mem_out {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {factor : CPolynomial F} :
    ∀ fuel stack out,
      factor ∈ out.toList →
        factor ∈
          (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack out).toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack out hmem
      simp [lasVegasSplitLoopWith, hmem]
  | succ fuel ih =>
      intro stack out hmem
      cases stack with
      | nil =>
          simp [lasVegasSplitLoopWith, hmem]
      | cons g stack =>
          rw [lasVegasSplitLoopWith.eq_def]
          simp only
          by_cases hskip : (CPolynomial.monicNormalize g == 0 ||
              CPolynomial.monicNormalize g == 1) = true
          · rw [if_pos hskip]
            exact ih stack out hmem
          · rw [if_neg hskip]
            by_cases hlin : isRepresentedLinearFactor (CPolynomial.monicNormalize g) = true
            · rw [if_pos hlin]
              exact ih stack (out.push (CPolynomial.monicNormalize g)) (by simp [hmem])
            · rw [if_neg hlin]
              by_cases hodd : (cfg.tryOddRandomizedSplitting && q % 2 == 1) = true
              · rw [if_pos hodd]
                cases htry :
                    tryOddSplitAttemptsWith M D q probes (CPolynomial.monicNormalize g)
                      cfg.cutoff 0 with
                | none =>
                    simp only
                    exact ih stack
                      (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                      (by simp [hmem])
                | some children =>
                    simp only
                    exact ih (children.toList ++ stack) out hmem
              · rw [if_neg hodd]
                by_cases heven : (cfg.tryEvenTraceSplitting && q % 2 == 0) = true
                · rw [if_pos heven]
                  cases traceCtx? with
                  | none =>
                      simp only
                      exact ih stack
                        (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                        (by simp [hmem])
                  | some traceCtx =>
                      simp only
                      by_cases hmatch : traceContextMatchesQ traceCtx q = true
                      · rw [if_pos hmatch]
                        cases htry :
                            tryEvenTraceSplitAttemptsWith M D traceCtx q probes
                              (CPolynomial.monicNormalize g) cfg.cutoff 0 with
                        | none =>
                            simp only
                            exact ih stack
                              (out ++ enumeratedLinearFactors enumeration
                                (CPolynomial.monicNormalize g))
                              (by simp [hmem])
                        | some children =>
                            simp only
                            exact ih (children.toList ++ stack) out hmem
                      · rw [if_neg hmatch]
                        exact ih stack
                          (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                          (by simp [hmem])
                · rw [if_neg heven]
                  exact ih stack
                    (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                    (by simp [hmem])

private theorem lasVegasSplitLoopWith_represented_mem_of_mem_out {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {factor : CPolynomial F} {fuel : Nat} {stack : List (CPolynomial F)}
    {out : Array (CPolynomial F)}
    (hmem : factor ∈ out.toList) (hlin : isRepresentedLinearFactor factor = true) :
    factor ∈
      (representedLinearFactorsOnly
        (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack out)).toList := by
  apply representedLinearFactorsOnly_mem_of_mem
  · exact lasVegasSplitLoopWith_mem_of_mem_out
      M D enumeration traceCtx? cfg probes q fuel stack out hmem
  · exact hlin

private theorem lasVegasSplitLoopWith_fallback_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {fuel : Nat} {stack : List (CPolynomial F)} {out : Array (CPolynomial F)}
    {g : CPolynomial F} {a : F} (hroot : CPolynomial.eval a g = 0) :
    ∃ factor,
      factor ∈
          (representedLinearFactorsOnly
            (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
              (out ++ enumeratedLinearFactors enumeration g))).toList ∧
        IsLinearRootFactorCandidate factor a := by
  refine ⟨CPolynomial.linearFactor a, ?_, linearFactor_isRootFactorCandidate a⟩
  apply lasVegasSplitLoopWith_represented_mem_of_mem_out
    M D enumeration traceCtx? cfg probes q
  · simp [linearFactor_mem_enumeratedLinearFactors enumeration hroot]
  · exact linearFactor_isRepresentedLinearFactor a

/-- Completeness surface for bounded Las Vegas splitting plus enumeration fallback. -/
theorem lasVegasSplitLinearFactorsWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat)
    {p : CPolynomial F} {a : F}
    (hvalid : lasVegasSplitterInput q p) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          (lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  sorry

/-- Completeness surface for bounded Las Vegas splitting with characteristic-two trace metadata. -/
theorem lasVegasSplitLinearFactorsWithTrace_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {p : CPolynomial F} {a : F}
    (hvalid : lasVegasSplitterInput q p) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          (lasVegasSplitLinearFactorsWithTrace M D enumeration traceCtx cfg probes q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  sorry

/-- Package bounded Las Vegas splitting as a finite-field linear-factor splitter. -/
def lasVegasLinearFactorProductSplitterWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (_ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun q p ↦
    lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p
  validInput := fun q p ↦ lasVegasSplitterInput q p
  sound := by
    intro q p factor h
    exact lasVegasSplitLinearFactorsWith_sound M D enumeration cfg probes q h
  complete := by
    intro q p a hvalid hp hroot
    exact lasVegasSplitLinearFactorsWith_complete
      M D enumeration cfg probes q hvalid hp hroot

/-- Package bounded Las Vegas trace splitting as a finite-field linear-factor splitter. -/
def lasVegasLinearFactorProductSplitterWithTrace {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (_ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun q p ↦
    lasVegasSplitLinearFactorsWithTrace M D enumeration traceCtx cfg probes q p
  validInput := fun q p ↦ lasVegasSplitterInput q p
  sound := by
    intro q p factor h
    exact lasVegasSplitLinearFactorsWithTrace_sound M D enumeration traceCtx cfg probes q h
  complete := by
    intro q p a hvalid hp hroot
    exact lasVegasSplitLinearFactorsWithTrace_complete
      M D enumeration traceCtx cfg probes q hvalid hp hroot

/-- Alias emphasizing the root-product precondition used by Las Vegas completeness. -/
theorem rootProduct_satisfies_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F)
    {p : CPolynomial F} (hp : p ≠ 0) :
    (lasVegasLinearFactorProductSplitterWith M D ctx enumeration cfg probes).validInput ctx.q
      (finiteFieldRootProductWith M D ctx p) := by
  exact finiteFieldRootProductWith_lasVegasSplitterInput M D ctx hp

end FiniteField

end Roots

end CPolynomial

end CompPoly
