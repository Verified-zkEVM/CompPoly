/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdusa
-/
import CompPoly.Multivariate.CMvMonomial
import CompPoly.Multivariate.Wheels
import Mathlib.Algebra.Lie.OfAssociative
import Std.Data.DTreeMap.Lemmas
import Std.Data.ExtDTreeMap.Lemmas
import Std.Data.ExtTreeMap.Lemmas

/-!
# Unlawful multivariate polynomials

This file defines the `Unlawful` type, which represents multivariate polynomials
as a map from monomials to coefficients. Unlike `Lawful`, it does not enforce
the absence of zero coefficients.

## Main definitions

* `CPoly.Unlawful n R`: A map from `CMvMonomial n` to `R`, implemented using `Std.ExtTreeMap`.
-/
set_option allowUnsafeReducibility true in
attribute [local reducible] instDecidableEqOfLawfulBEq
attribute [local instance 5] instDecidableEqOfLawfulBEq

universe u v

namespace Std

attribute [local instance low] beqOfOrd

namespace DTreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

theorem Const.get?_foldl_no_touch
    [TransCmp cmp] [LawfulEqCmp cmp]
    (k : α) (f : α → β → β → β)
    (l : List (α × β)) (t : DTreeMap α (fun _ => β) cmp)
    (hno : ∀ p ∈ l, cmp p.1 k ≠ .eq) :
    Const.get? (l.foldl (fun acc p =>
      Const.alter acc p.1 (fun
        | none => some p.2
        | some b₁ => some (f p.1 b₁ p.2))) t) k = Const.get? t k := by
  classical
  revert t hno
  induction l with
  | nil =>
      intro t hno
      simp [List.foldl]
  | cons hd tl ih =>
      intro t hno
      have hno_hd : cmp hd.1 k ≠ .eq := by
        apply hno hd
        simp
      have hno_tl : ∀ p ∈ tl, cmp p.1 k ≠ .eq := by
        intro p hp
        exact hno p (by simp [hp])
      have hstep := get?_alter (t := t) (k := hd.1) (k' := k)
        (f := fun
          | none => some hd.2
          | some b₁ => some (f hd.1 b₁ hd.2))
      have hstep' :
          get? (alter t hd.1 (fun
              | none => some hd.2
              | some b₁ => some (f hd.1 b₁ hd.2))) k =
            get? t k := by
        simpa [hno_hd] using hstep
      have ih' := ih
        (alter t hd.1 (fun
          | none => some hd.2
          | some b₁ => some (f hd.1 b₁ hd.2))) hno_tl
      simpa [List.foldl, hstep'] using ih'

theorem Const.get?_mergeWith
    [TransCmp cmp] [LawfulEqCmp cmp]
    (f : α → β → β → β) (t₁ t₂ : DTreeMap α (fun _ => β) cmp) (k : α) :
    get? (mergeWith f t₁ t₂) k =
      match get? t₁ k, get? t₂ k with
      | some v₁, some v₂ => some (f k v₁ v₂)
      | some v₁, none => some v₁
      | none, some v₂ => some v₂
      | none, none => none := by
  letI : Ord α := ⟨cmp⟩
  let l : List (α × β) := toList t₂
  let pred : (α × β) → Bool := fun p => cmp p.1 k == .eq
  have hFindToGet : (l.find? pred).map Prod.snd = get? t₂ k := by
    cases h : l.find? pred with
    | none =>
        have hc : t₂.contains k = false :=
          (find?_toList_eq_none_iff_contains_eq_false (t := t₂) (k := k) |>.1)
            (by simp [l, pred, h])
        have hk := get?_eq_none_of_contains_eq_false (t := t₂) (a := k) hc
        simp [hk]
    | some p =>
        rcases p with ⟨k', v⟩
        have hv := (find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some
          (t := t₂) (k := k) (k' := k') (v := v)).1 (by simpa [l, pred] using h)
        have hGet : get? t₂ k = some v := hv.2
        simp [hGet]
  have hPair : List.Pairwise (fun a b : α × β => cmp a.1 b.1 ≠ .eq) l := by
    simpa using (distinct_keys_toList (t := t₂))
  have hFold :
      ∀ (l' : List (α × β))
        (hp : List.Pairwise (fun a b : α × β => cmp a.1 b.1 ≠ .eq) l')
        (t : DTreeMap α (fun _ => β) cmp),
        get? (l'.foldl (fun acc p =>
          alter acc p.1 (fun
            | none => some p.2
            | some b₁ => some (f p.1 b₁ p.2))) t) k =
          (match get? t k, (l'.find? pred).map Prod.snd with
          | some v₁, some v₂ => some (f k v₁ v₂)
          | some v₁, none => some v₁
          | none, some v₂ => some v₂
          | none, none => none) := by
    intro l' hp t
    induction l' generalizing t with
    | nil =>
        cases h₁ : get? t k <;> simp [List.find?, h₁]
    | cons hd tl ih =>
        rcases hd with ⟨a, b₂⟩
        have hpCons := (List.pairwise_cons).1 hp
        have hpTl : List.Pairwise (fun x y : α × β => cmp x.1 y.1 ≠ .eq) tl := hpCons.2
        have hkeys : ∀ p ∈ tl, cmp a p.1 ≠ .eq := by
          intro p hp'
          exact hpCons.1 p hp'
        by_cases heq : cmp a k = .eq
        · have hstep := get?_alter (t := t) (k := a) (k' := k)
            (f := fun
              | none => some b₂
              | some b₁ => some (f a b₁ b₂))
          have hcongr : get? t a = get? t k := get?_congr (t := t) (hab := heq)
          have hno_a : ∀ p ∈ tl, cmp p.1 a ≠ .eq := by
            intro p hp' hpa
            have hapEq : p.1 = a :=
              (LawfulEqCmp.compare_eq_iff_eq (cmp := cmp) (a := p.1) (b := a)).1 hpa
            have : cmp a p.1 = .eq :=
              (LawfulEqCmp.compare_eq_iff_eq (cmp := cmp) (a := a) (b := p.1)).2 hapEq.symm
            exact (hkeys p hp') this
          have htail_a := Const.get?_foldl_no_touch
            (k := a) (f := f) tl
            (alter t a (fun
              | none => some b₂
              | some b₁ => some (f a b₁ b₂))) hno_a
          have hcongrBefore :=
            get?_congr (t := alter t a (fun
              | none => some b₂
              | some b₁ => some (f a b₁ b₂))) (hab := heq)
          have hcongrAfter := get?_congr
            (t := tl.foldl (fun acc p =>
              alter acc p.1 (fun
                | none => some p.2
                | some b₁ => some (f p.1 b₁ p.2)))
              (alter t a (fun
                | none => some b₂
                | some b₁ => some (f a b₁ b₂)))) (hab := heq)
          have htail_k :
              get? (tl.foldl (fun acc p =>
                alter acc p.1 (fun
                  | none => some p.2
                  | some b₁ => some (f p.1 b₁ p.2)))
                (alter t a (fun
                  | none => some b₂
                  | some b₁ => some (f a b₁ b₂)))) k =
                get? (alter t a (fun
                  | none => some b₂
                  | some b₁ => some (f a b₁ b₂))) k := by
            simpa [hcongrAfter, hcongrBefore] using htail_a
          cases hget : get? t k with
          | none =>
              simp [List.find?, pred, heq, htail_k, hstep, hcongr, hget]
          | some v₁ =>
              have ak : a = k :=
                (LawfulEqCmp.compare_eq_iff_eq (cmp := cmp) (a := a) (b := k)).1 heq
              have hhead :
                  get? (alter t a (fun
                      | none => some b₂
                      | some b₁ => some (f a b₁ b₂))) k =
                    some (f k v₁ b₂) := by
                simp [hget, ak]
              have lhs :
                  get? (tl.foldl (fun acc p =>
                    alter acc p.1 (fun
                      | none => some p.2
                      | some b₁ => some (f p.1 b₁ p.2)))
                    (alter t a (fun
                      | none => some b₂
                      | some b₁ => some (f a b₁ b₂)))) k =
                    some (f k v₁ b₂) := by
                simp [hhead, htail_k]
              simp [List.find?, pred, heq, List.foldl, lhs]
        · have hstep := get?_alter (t := t) (k := a) (k' := k)
            (f := fun
              | none => some b₂
              | some b₁ => some (f a b₁ b₂))
          have ih' := ih hpTl
            (alter t a (fun
              | none => some b₂
              | some b₁ => some (f a b₁ b₂)))
          have hbeq : (cmp a k == .eq) = false := by
            cases hcmp : cmp a k with
            | lt => rfl
            | gt => rfl
            | eq =>
                have : False := heq (by simp only [hcmp])
                cases this
          simp [List.find?, pred, hbeq, List.foldl, hstep, heq, ih']
  have hFindToGetInt : (l.find? pred).map Prod.snd = Internal.Impl.Const.get? t₂.inner k := by
    simp [get?, hFindToGet]
  have hFoldInt :
      Internal.Impl.Const.get?
          ((l.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁).inner) k =
        (match Internal.Impl.Const.get? t₁.inner k, (l.find? pred).map Prod.snd with
        | some v₁, some v₂ => some (f k v₁ v₂)
        | some v₁, none => some v₁
        | none, some v₂ => some v₂
        | none, none => none) := by
    simpa [get?] using (hFold l hPair t₁)
  have h₀ :
      Internal.Impl.Const.get?
          (Internal.Impl.Const.mergeWith f t₁.inner t₂.inner t₁.wf.balanced |>.1) k =
        Internal.Impl.Const.get?
          ((l.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁).inner) k := by
    clear hFoldInt
    have hFoldInner :
        ((l.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁).inner) =
          (List.foldl
            (fun a b =>
              Internal.Impl.Const.alter! b.1
                (fun x =>
                  match x with
                  | none => some b.2
                  | some b₁ => some (f b.1 b₁ b.2))
                a)
            t₁.inner l) := by
      revert t₁
      induction l with
      | nil =>
          intro t₁
          simp
      | cons hd tl ih =>
          intro t₁
          rcases hd with ⟨a, b⟩
          simpa [List.foldl, alter, Internal.Impl.Const.alter_eq_alter!]
            using ih (alter t₁ a (fun
              | none => some b
              | some b₁ => some (f a b₁ b)))
    rw [Internal.Impl.Const.mergeWith_eq_mergeWith!,
      Internal.Impl.Const.mergeWith!,
      Internal.Impl.Const.foldl_eq_foldl_toList]
    have hFoldInnerToList :
        ((List.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁ (Internal.Impl.Const.toList t₂.inner)).inner) =
          (List.foldl
            (fun a b =>
              Internal.Impl.Const.alter! b.1
                (fun x =>
                  match x with
                  | none => some b.2
                  | some b₁ => some (f b.1 b₁ b.2))
                a)
            t₁.inner (Internal.Impl.Const.toList t₂.inner)) := by
      simpa only [alter, Internal.Impl.Const.alter_eq_alter!, toList, l] using hFoldInner
    simpa using congrArg (fun m => Internal.Impl.Const.get? m k) hFoldInnerToList.symm
  calc
    get? (mergeWith f t₁ t₂) k
        = Internal.Impl.Const.get?
            (Internal.Impl.Const.mergeWith f t₁.inner t₂.inner t₁.wf.balanced |>.1) k := by
              rfl
    _ = Internal.Impl.Const.get?
          ((l.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁).inner) k := h₀
    _ = match Internal.Impl.Const.get? t₁.inner k, (l.find? pred).map Prod.snd with
          | some v₁, some v₂ => some (f k v₁ v₂)
          | some v₁, none => some v₁
          | none, some v₂ => some v₂
          | none, none => none := hFoldInt
    _ = match get? t₁ k, get? t₂ k with
          | some v₁, some v₂ => some (f k v₁ v₂)
          | some v₁, none => some v₁
          | none, some v₂ => some v₂
          | none, none => none := by
            simp [get?, hFindToGet]

end DTreeMap

theorem ExtDTreeMap.get?_filter_with_getKey_pfilter {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtDTreeMap α (fun _ => β) cmp) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f) k =
      (Const.get? m k).pfilter (fun v h' =>
        f (m.getKey k (Const.contains_eq_isSome_get?.trans (Option.isSome_of_eq_some h'))) v) := by
  exact Const.get?_filter

namespace ExtTreeMap

variable {α : Type u} {β : Type v}

attribute [grind ext] ExtTreeMap.ext_getElem?
attribute [grind .] ExtTreeMap.distinct_keys_toList ExtTreeMap.getElem?_ofList_of_mem

@[grind =]
theorem getElem?_pfilter
    {cmp : α → α → Ordering} [TransCmp cmp]
    {m : ExtTreeMap α β cmp} {f : α → β → Bool} {k : α} :
    (m.filter f)[k]? =
      m[k]?.pfilter (fun v h' =>
        f (m.getKey k (contains_eq_isSome_getElem?.trans (Option.isSome_of_eq_some h'))) v) := by
  generalize_proofs at *
  apply Std.ExtDTreeMap.get?_filter_with_getKey_pfilter

variable {cmp : α → α → Ordering}
variable {k : α} {m m₁ m₂ : ExtTreeMap α β cmp} {f : α → β → β → β}

variable [TransCmp cmp] [LawfulEqCmp cmp]

theorem get?_mergeWith_at :
    (m₁.mergeWith f m₂)[k]? =
      match m₁[k]?, m₂[k]? with
      | .some v₁, .some v₂ => .some (f k v₁ v₂)
      | .some v₁, .none => .some v₁
      | .none, .some v₂ => .some v₂
      | .none, .none => .none := by
  let mergeValues : Option β → Option β → Option β := fun
    | .some v₁, .some v₂ => .some (f k v₁ v₂)
    | .some v₁, .none => .some v₁
    | .none, .some v₂ => .some v₂
    | .none, .none => .none
  change _ = mergeValues _ _
  match m₁ with
  | ExtTreeMap.mk t₁ =>
    match m₂ with
    | ExtTreeMap.mk t₂ =>
      induction t₁, t₂ using ExtDTreeMap.inductionOn₂ with
      | mk t₁ t₂ =>
        change DTreeMap.Const.get? (DTreeMap.Const.mergeWith f t₁ t₂) k =
          mergeValues (DTreeMap.Const.get? t₁ k) (DTreeMap.Const.get? t₂ k)
        cases h₁ : DTreeMap.Const.get? t₁ k <;>
          cases h₂ : DTreeMap.Const.get? t₂ k <;>
          simp [mergeValues, DTreeMap.Const.get?_mergeWith, h₁, h₂]

lemma mergeWith_of_mem_mem (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
    (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k]) := by
  have h₁' : m₁[k]? = .some m₁[k] := getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] := getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

lemma mergeWith_of_mem_left (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
    (m₁.mergeWith f m₂)[k]? = m₁[k]? := by
  have h₁' : m₁[k]? = .some m₁[k] := getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none := getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

lemma mergeWith_of_mem_right (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
    (m₁.mergeWith f m₂)[k]? = m₂[k]? := by
  have h₁' : m₁[k]? = .none := getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] := getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

lemma mergeWith_of_not_mem (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
    (m₁.mergeWith f m₂)[k]? = .none := by
  have h₁' : m₁[k]? = .none := getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none := getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

grind_pattern mergeWith_of_mem_mem => k ∈ m₁, k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith_of_mem_left => k ∈ m₁, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith_of_mem_right => k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith_of_not_mem => (ExtTreeMap.mergeWith f m₁ m₂)[k]?

@[grind =]
lemma getElem?_filter_with_getKey {k : α} {m : ExtTreeMap α β cmp} {f : α → β → Bool} :
    (m.filter f)[k]? = m[k]?.filter (f k) := by
  simp

end ExtTreeMap
end Std

namespace CPoly

open Std

/--
  Polynomial in `n` variables with coefficients in `R`.
  Internally represented as a tree map from monomials to coefficients.
-/
abbrev Unlawful (n : ℕ) (R : Type*) : Type _ :=
  Std.ExtTreeMap (CMvMonomial n) R (Ord.compare (α := CMvMonomial n))

section Instances

variable {n : ℕ} {R : Type*}

instance : EmptyCollection (Unlawful n R) := ⟨(∅ : Std.ExtTreeMap (CMvMonomial n) R compare)⟩

instance : Singleton (MonoR n R) (Unlawful n R) :=
  inferInstanceAs (Singleton (MonoR n R) (Std.ExtTreeMap (CMvMonomial n) R compare))

instance : Insert (MonoR n R) (Unlawful n R) :=
  inferInstanceAs (Insert (MonoR n R) (Std.ExtTreeMap (CMvMonomial n) R compare))

instance : LawfulSingleton (MonoR n R) (Unlawful n R) :=
  inferInstanceAs (LawfulSingleton (MonoR n R) (Std.ExtTreeMap (CMvMonomial n) R compare))

instance : Membership (CMvMonomial n) (Unlawful n R) :=
  inferInstanceAs (Membership (CMvMonomial n) (Std.ExtTreeMap (CMvMonomial n) R compare))

@[default_instance]
instance (priority := high) : GetElem (Unlawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (GetElem (Std.ExtTreeMap (CMvMonomial n) R compare) (CMvMonomial n) R (fun lp m ↦ m ∈ lp))

instance : GetElem? (Unlawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (GetElem? (Std.ExtTreeMap (CMvMonomial n) R compare) (CMvMonomial n) R (fun lp m ↦ m ∈ lp))

instance : LawfulGetElem (Unlawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (LawfulGetElem (Std.ExtTreeMap (CMvMonomial n) R compare) (CMvMonomial n) R (fun lp m ↦ m ∈ lp))

end Instances

namespace Unlawful

attribute [grind ext] Std.ExtTreeMap.ext_getElem?

@[ext, grind ext]
lemma ext_getElem? {n R} {t₁ t₂ : Unlawful n R}
    (h : ∀ (k : CMvMonomial n), t₁[k]? = t₂[k]?) : t₁ = t₂ :=
  Std.ExtTreeMap.ext_getElem? h

variable {n : ℕ} {R : Type*}

/-- Construct an `Unlawful` polynomial from a list of monomial-coefficient pairs. -/
@[simp, grind =]
def ofList (l : List (CMvMonomial n × R)) : Unlawful n R := ExtTreeMap.ofList l compare

/-- Extend the number of variables by padding monomials with zeros. -/
def extend (n' : ℕ) (p : Unlawful n R) : Unlawful (n ⊔ n') R :=
  .ofList (p.keys.map (CMvMonomial.extend n') |>.zip p.values)

/-- Check if the polynomial has no zero coefficients. -/
abbrev isNoZeroCoef [Zero R] (p : Unlawful n R) : Prop := ∀ (m : CMvMonomial n), p[m]? ≠ some 0

def toFinset [DecidableEq R] (p : Unlawful n R) : Finset (CMvMonomial n × R) :=
  p.toList.toFinset

/-- The list of monomials present in the polynomial. -/
abbrev monomials (p : Unlawful n R) : List (CMvMonomial n) :=
  p.keys

@[simp]
lemma mem_monomials {m : CMvMonomial n} {up : Unlawful n R} :
    m ∈ up.monomials ↔ m ∈ up := ExtTreeMap.mem_keys

instance [Repr R] : Repr (Unlawful n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

/-- Constant polynomial. -/
@[grind =]
def C [BEq R] [LawfulBEq R] [Zero R] (c : R) : Unlawful n R :=
  if c = 0 then ∅ else .ofList [MonoR.C c]

section

variable {m : ℕ} [Zero R] {x : CMvMonomial n}

section

variable [BEq R] [LawfulBEq R]

instance : OfNat (Unlawful n R) 0 := ⟨C 0⟩

instance [NatCast R] [NeZero m] : OfNat (Unlawful n R) m := ⟨C m⟩

@[simp, grind =]
lemma C_zero : C (n := n) (0 : R) = 0 := rfl

end

@[simp, grind =]
lemma C_zero' : C (n := n) (0 : ℕ) = 0 := rfl

@[simp, grind =]
lemma zero_eq_zero : (Zero.zero : R) = 0 := rfl

lemma zero_eq_empty [BEq R] [LawfulBEq R] : (0 : Unlawful n R) = ∅ := by unfold_projs; simp [C]; rfl

@[simp, grind .]
lemma not_mem_C_zero : x ∉ C 0 := by grind

section

variable [BEq R] [LawfulBEq R]

@[simp, grind .]
lemma not_mem_zero : x ∉ (0 : Unlawful n R) := by rw [←C_zero]; grind

@[simp, grind .]
lemma isNoZeroCoef_zero : isNoZeroCoef (n := n) (R := R) 0 := by rw [←C_zero]; grind

end

end

/-- Pointwise addition of coefficients. -/
def add [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (Unlawful n R) := ⟨add⟩

@[grind=]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Unlawful n R} :
    p₁ + p₂ = p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂ := rfl

/-- Add a single monomial-coefficient term to a polynomial. -/
def addMonoR [Add R] (p : Unlawful n R) (term : MonoR n R) : Unlawful n R :=
  p + .ofList [term]

/-- Multiply a polynomial by a single monomial term. -/
def mul₀ [Mul R] (t : MonoR n R) (p : Unlawful n R) : Unlawful n R :=
  .ofList (p.toList.map fun (k, v) ↦ (t.1+k, t.2*v))

attribute [grind=] ExtTreeMap.ofList_eq_empty_iff List.map_eq_nil_iff ExtTreeMap.toList_eq_nil_iff

@[simp, grind=]
lemma mul₀_zero [Zero R] [BEq R] [LawfulBEq R] [Mul R] {t : MonoR n R} : mul₀ t 0 = 0 := by
  unfold mul₀
  grind

/-- Polynomial multiplication using a nested fold (distributive law). -/
def mul [Mul R] [Add R] [Zero R] [BEq R] [LawfulBEq R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.foldl (init := 0)
    fun p m₁ c₁ ↦
      (p₂.foldl (init := 0) fun p' m₂ c₂ ↦ {(m₁ + m₂, c₁ * c₂)} + p') + p

instance [BEq R] [LawfulBEq R] [Mul R] [Add R] [Zero R] : Mul (Unlawful n R) := ⟨mul⟩

section Neg

variable [Neg R]

/-- Negation (negates all coefficients). -/
def neg (p : Unlawful n R) : Unlawful n R :=
  p.map fun _ v ↦ -v

instance : Neg (Unlawful n R) := ⟨neg⟩

/-- Subtraction. -/
def sub [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  Unlawful.add p₁ (-p₂)

instance [Add R] : Sub (Unlawful n R) := ⟨sub⟩

end Neg

/-- Return the term with the lexicographically largest monomial. -/
def leadingTerm? : Unlawful n R → Option (MonoR n R) :=
  ExtTreeMap.maxEntry?

/-- Return the lexicographically largest monomial. -/
def leadingMonomial? : Unlawful n R → Option (CMvMonomial n) :=
  .map Prod.fst ∘ Unlawful.leadingTerm?

instance instDecidableEq [DecidableEq R] : DecidableEq (Unlawful n R) := fun x y ↦
  if h : x.toList = y.toList
  then Decidable.isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else Decidable.isFalse (by grind)

def coeff {R : Type*} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : Unlawful n R) : R :=
  p[m]?.getD 0

@[simp, grind =]
lemma filter_get {R : Type*} [BEq R] [LawfulBEq R] {v : R} {m : CMvMonomial n} (a : Unlawful n R) :
    (ExtTreeMap.filter (fun _ c => c != v) a)[m]?.getD v = a[m]?.getD v := by
  grind

lemma add_getD? [CommSemiring R] {m : CMvMonomial n} {p q : Unlawful n R} :
    (p.add q)[m]?.getD 0 = p[m]?.getD 0 + q[m]?.getD 0 := by
  by_cases hp : m ∈ p <;> by_cases hq : m ∈ q
  · simpa [Unlawful.add, hp, hq] using congrArg (fun o => o.getD 0)
      (ExtTreeMap.mergeWith_of_mem_mem
        (m₁ := p) (m₂ := q) (f := fun _ c₁ c₂ => c₁ + c₂) (k := m) hp hq)
  · simpa [Unlawful.add, hp, hq, add_zero] using congrArg (fun o => o.getD 0)
      (ExtTreeMap.mergeWith_of_mem_left
        (m₁ := p) (m₂ := q) (f := fun _ c₁ c₂ => c₁ + c₂) (k := m) hp hq)
  · simpa [Unlawful.add, hp, hq, zero_add] using congrArg (fun o => o.getD 0)
      (ExtTreeMap.mergeWith_of_mem_right
        (m₁ := p) (m₂ := q) (f := fun _ c₁ c₂ => c₁ + c₂) (k := m) hp hq)
  · simpa [Unlawful.add, hp, hq] using congrArg (fun o => o.getD 0)
      (ExtTreeMap.mergeWith_of_not_mem
        (m₁ := p) (m₂ := q) (f := fun _ c₁ c₂ => c₁ + c₂) (k := m) hp hq)

end Unlawful

end CPoly
