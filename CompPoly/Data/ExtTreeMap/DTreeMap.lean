/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Std.Data.DTreeMap.Lemmas

/-!
# Auxiliary lemmas for `Std.DTreeMap`

Lemmas about `mergeWith` and `filter` on `Std.DTreeMap` (and its internal
implementation) that are used downstream by the multivariate polynomial
representation in `CompPoly.Multivariate.Unlawful`.

Vendored from
[`Verified-zkEVM/ExtTreeMapLemmas`](https://github.com/Verified-zkEVM/ExtTreeMapLemmas)
(tag `v4.29.1`, commit `3fee686227f18dca03bb7fc42ca5a9275d6cfda6`).
-/

universe u v

namespace Std

namespace DTreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

-- Folding alters at keys ≠ `k` does not change `get? _ k`.
theorem Const.get?_foldl_no_touch
    [TransCmp cmp] [LawfulEqCmp cmp]
    (k : α) (f : α → β → β → β)
    (l : List (α × β)) (t : DTreeMap α (fun _ => β) cmp)
    (hno : ∀ p ∈ l, cmp p.1 k ≠ .eq) :
    Const.get? (l.foldl (fun acc p =>
      Const.alter acc p.1 (fun
        | none => some p.2
        | some b₁ => some (f p.1 b₁ p.2))
    ) t) k = Const.get? t k := by
  classical
  revert t hno
  induction l with
  | nil =>
    intro t hno; simp [List.foldl]
  | @cons hd tl ih =>
    intro t hno
    have hno_hd : cmp hd.1 k ≠ .eq := by
      apply hno hd
      simp
    have hno_tl : ∀ p ∈ tl, cmp p.1 k ≠ .eq := by
      intro p hp; exact hno p (by simp [hp])
    -- One step of alter does not affect `k` since keys differ
    have hstep := get?_alter (t := t) (k := hd.1) (k' := k)
      (f := fun | none => some hd.2 | some b₁ => some (f hd.1 b₁ hd.2))
    have hstep' :
        get? (alter t hd.1 (fun | none => some hd.2 | some b₁ => some (f hd.1 b₁ hd.2))) k
        = get? t k := by
      simpa [hno_hd] using hstep
    have ih' := ih (alter t hd.1 (fun | none => some hd.2 | some b₁ => some (f hd.1 b₁ hd.2))) hno_tl
    simpa [List.foldl, hstep'] using ih'

-- Pointwise description of `mergeWith` on `get?` at a fixed key.
theorem Const.get?_mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    (f : α → β → β → β) (t₁ t₂ : DTreeMap α (fun _ => β) cmp) (k : α) :
    get? (mergeWith f t₁ t₂) k =
      match get? t₁ k, get? t₂ k with
      | some v₁, some v₂ => some (f k v₁ v₂)
      | some v₁, none => some v₁
      | none, some v₂ => some v₂
      | none, none => none := by
  letI : Ord α := ⟨cmp⟩
  let l : List (α × β) := toList t₂
  let pred : (α × β) → Bool := fun p => (cmp p.1 k == .eq)
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
  -- Main induction: effect of folding alters over l on get? at key k
  have hFold :
      ∀ (l' : List (α × β)) (hp : List.Pairwise (fun a b : α × β => cmp a.1 b.1 ≠ .eq) l') (t : DTreeMap α (fun _ => β) cmp),
        get? (l'.foldl (fun acc p =>
          alter acc p.1 (fun
            | none => some p.2
            | some b₁ => some (f p.1 b₁ p.2))
        ) t) k
        = (match get? t k, (l'.find? pred).map Prod.snd with
           | some v₁, some v₂ => some (f k v₁ v₂)
           | some v₁, none => some v₁
           | none, some v₂ => some v₂
           | none, none => none) := by
    intro l' hp t
    induction l' generalizing t with
    | nil =>
      cases h₁ : get? t k <;> simp [List.find?, h₁]
    | @cons hd tl ih =>
      rcases hd with ⟨a, b₂⟩
      have hp_cons := (List.pairwise_cons).1 hp
      have hp_tl : List.Pairwise (fun x y : α × β => cmp x.1 y.1 ≠ .eq) tl := hp_cons.2
      have hkeys : ∀ p ∈ tl, cmp a p.1 ≠ .eq := by intro p hp; exact hp_cons.1 p hp
      by_cases heq : cmp a k = .eq
      · have hstep := get?_alter (t := t) (k := a) (k' := k)
          (f := fun | none => some b₂ | some b₁ => some (f a b₁ b₂))
        have hcongr : get? t a = get? t k := get?_congr (t := t) (hab := heq)
        -- Tail does not touch key a
        have hno_a : ∀ p ∈ tl, cmp p.1 a ≠ .eq := by
          intro p hp hpa
          have hap_eq : p.1 = a := (LawfulEqCmp.compare_eq_iff_eq (cmp := cmp) (a := p.1) (b := a)).1 hpa
          have : cmp a p.1 = .eq := (LawfulEqCmp.compare_eq_iff_eq (cmp := cmp) (a := a) (b := p.1)).2 hap_eq.symm
          exact (hkeys p hp) this
        have htail_a := Const.get?_foldl_no_touch (k := a) (f := f) tl (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂))) hno_a
        have hcongr_before := get?_congr (t := alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂))) (hab := heq)
        have hcongr_after  := get?_congr (t := tl.foldl (fun acc p => alter acc p.1 (fun | none => some p.2 | some b₁ => some (f p.1 b₁ p.2))) (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)))) (hab := heq)
        have htail_k :
            get? (tl.foldl (fun acc p =>
              alter acc p.1 (fun | none => some p.2 | some b₁ => some (f p.1 b₁ p.2)))
              (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)))) k
            = get? (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂))) k := by
          simpa [hcongr_after, hcongr_before] using htail_a
        cases hget : get? t k with
        | none =>
          -- here, find? hits head
          simp [List.find?, pred, heq, htail_k, hstep, hcongr, hget]
        | some v₁ =>
          have ak : a = k := (LawfulEqCmp.compare_eq_iff_eq (cmp := cmp) (a := a) (b := k)).1 heq
          have hhead :
              get? (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂))) k
              = some (f k v₁ b₂) := by
            simp [hget, ak]
          have lhs :
              get? (tl.foldl (fun acc p =>
                alter acc p.1 (fun | none => some p.2 | some b₁ => some (f p.1 b₁ p.2)))
                (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)))) k
              = some (f k v₁ b₂) := by
            simp [hhead, htail_k]
          -- Normalize the cons-level goal to the tail form and close using lhs
          simp [List.find?, pred, heq, List.foldl, lhs]
      · have hstep := get?_alter (t := t) (k := a) (k' := k)
          (f := fun | none => some b₂ | some b₁ => some (f a b₁ b₂))
        have ih' := ih hp_tl (alter t a (fun | none => some b₂ | some b₁ => some (f a b₁ b₂)))
        -- simplify find? on cons using boolean predicate value is false
        have hbeq : (cmp a k == .eq) = false := by
          cases hcmp : cmp a k with
          | lt => rfl
          | gt => rfl
          | eq =>
            have : False := heq (by simp only [hcmp])
            cases this
        simp [List.find?, pred, hbeq, List.foldl, hstep, heq, ih']
  -- From fold characterization to mergeWith via internal equivalences
  have hFindToGetInt : (l.find? pred).map Prod.snd = Internal.Impl.Const.get? t₂.inner k := by
    simp [get?, hFindToGet]
  have hFoldInt :
      Internal.Impl.Const.get? ((l.foldl (fun acc p =>
        alter acc p.1 (fun
          | none => some p.2
          | some b₁ => some (f p.1 b₁ p.2))
      ) t₁).inner) k
      = (match Internal.Impl.Const.get? t₁.inner k, (l.find? pred).map Prod.snd with
         | some v₁, some v₂ => some (f k v₁ v₂)
         | some v₁, none => some v₁
         | none, some v₂ => some v₂
         | none, none => none) := by
    simpa [get?] using (hFold l hPair t₁)
  -- Relate internal mergeWith to a fold over toList
  have h₀ :
      Internal.Impl.Const.get? (Internal.Impl.Const.mergeWith f t₁.inner t₂.inner t₁.wf.balanced |>.1) k
      = Internal.Impl.Const.get? ((l.foldl (fun acc p =>
          alter acc p.1 (fun
            | none => some p.2
            | some b₁ => some (f p.1 b₁ p.2))
        ) t₁).inner) k := by
    clear hFoldInt
    -- Bridge the foldl over DTreeMap with the foldl over the internal Impl
    have hFoldInner :
        ((l.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁).inner)
        = (List.foldl
            (fun a b =>
              Internal.Impl.Const.alter! b.1
                (fun x => match x with | none => some b.2 | some b₁ => some (f b.1 b₁ b.2))
                a)
            t₁.inner l) := by
      -- Prove by induction on the list `l`
      revert t₁
      induction l with
      | nil => intro t₁; simp
      | @cons hd tl ih =>
        intro t₁; rcases hd with ⟨a, b⟩
        simpa [List.foldl, alter, Internal.Impl.Const.alter_eq_alter!]
          using ih (alter t₁ a (fun
            | none => some b
            | some b₁ => some (f a b₁ b)))
    -- Now rewrite mergeWith to the internal foldl and align both sides
    rw [Internal.Impl.Const.mergeWith_eq_mergeWith!,
        Internal.Impl.Const.mergeWith!,
        Internal.Impl.Const.foldl_eq_foldl_toList]
    -- Specialize the bridge to `toList t₂.inner`
    have hFoldInner_toList :
        ((List.foldl (fun acc p =>
            alter acc p.1 (fun
              | none => some p.2
              | some b₁ => some (f p.1 b₁ p.2))) t₁ (Internal.Impl.Const.toList t₂.inner)).inner)
        = (List.foldl
            (fun a b =>
              Internal.Impl.Const.alter! b.1
                (fun x => match x with | none => some b.2 | some b₁ => some (f b.1 b₁ b.2))
                a)
            t₁.inner (Internal.Impl.Const.toList t₂.inner)) := by
      simpa only [alter, Internal.Impl.Const.alter_eq_alter!, toList, l] using hFoldInner
    simpa using congrArg (fun m => Internal.Impl.Const.get? m k) hFoldInner_toList.symm
  -- Finish by rewriting with h₀ and identifying find? with get?
  simp [get?, mergeWith, h₀, hFindToGetInt, hFoldInt]


/-
  PROOF BY Markus Himmel from:
  ```
    https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ExtTreeMap.20-.20Filter.20.2F.20MergeWith/near/530761978
  ```
-/

attribute [local instance low] beqOfOrd

theorem Internal.Impl.Const.get?_filter_with_getKey_pfilter [Ord α] [TransOrd α]
    (m : DTreeMap.Internal.Impl α (fun _ => β)) (h : m.WF) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f h.balanced).1 k = (Const.get? m k).pfilter (fun v h' => f (m.getKey k ((contains_eq_isSome_get? h).trans (Option.isSome_of_eq_some h'))) v) := by
  -- This manual proof is usually done by the `simp_to_model` tactic
  simp only [Const.get?_eq_getValue? h.filter.ordered, toListModel_filter,
    Const.get?_eq_getValue? h.ordered, getKey_eq_getKey h.ordered]
  apply Std.Internal.List.Const.getValue?_filter
  apply h.ordered.distinctKeys

theorem get?_filter_with_getKey_pfilter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : DTreeMap α (fun _ => β) cmp) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun v h' => f (m.getKey k (Const.contains_eq_isSome_get?.trans (Option.isSome_of_eq_some h'))) v) :=
  letI : Ord α := ⟨cmp⟩
  DTreeMap.Internal.Impl.Const.get?_filter_with_getKey_pfilter m.inner m.wf _ _

end DTreeMap

end Std
