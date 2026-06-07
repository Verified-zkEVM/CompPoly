/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Basic

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

private theorem splitWork_pos_of_natDegree_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} (hdegree : 0 < p.toPoly.natDegree) :
    1 ≤ splitWork p := by
  unfold splitWork
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
    exact splitWork_pair_le_of_natDegree_sum_le htracePos hcomplementPos hsum
  next hsize =>
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

private theorem cantorZassenhausOddAttemptWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  sorry

private theorem cantorZassenhausOddAttemptWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  sorry

private theorem tryOddSplitAttemptsWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  sorry

private theorem tryOddSplitAttemptsWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F} :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        child ∈ children.toList →
          isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  sorry

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
