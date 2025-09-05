import Aesop
import Mathlib.Logic.Function.Defs
import ExtTreeMapLemmas.ExtTreeMap
import Mathlib.Tactic.Cases

lemma distinct_of_inj_nodup {α β : Type*} {l : List α} {f : α → β}
  (h₁ : Function.Injective f) (h₂ : l.Nodup) :
  List.Pairwise (fun a b => f a ≠ f b) l := by
  induction' l with hd tl ih
  · simp
  · simp_all only [ne_eq, List.nodup_cons, List.pairwise_cons, and_true, forall_const]
    intros a' ha' contra
    have : hd = a' := by aesop
    aesop

namespace ExtTreeMap

variable {α β : Type}
         {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
         {k : α} {m m₁ m₂ : Std.ExtTreeMap α β cmp} {f : α → β → β → β}

@[simp, grind=]
lemma mergeWith_empty {f : α → β → β → β} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {t : Std.ExtTreeMap α β cmp} :
  Std.ExtTreeMap.mergeWith f t ∅ = t := by ext; grind

lemma mergeWith_of_comm (h : ∀ {x}, Std.Commutative (f x)) :
    m₁.mergeWith f m₂ = m₂.mergeWith f m₁ := by
  ext k v
  by_cases h' : k ∈ m₁ <;> by_cases h'' : k ∈ m₂
  · rw [Std.ExtTreeMap.mergeWith₀ h' h'', Std.ExtTreeMap.mergeWith₀ h'' h', h.comm]
  · rw [Std.ExtTreeMap.mergeWith₁ h' h'', Std.ExtTreeMap.mergeWith₂ h'' h']
  · rw [Std.ExtTreeMap.mergeWith₂ h' h'', Std.ExtTreeMap.mergeWith₁ h'' h']
  · rw [Std.ExtTreeMap.mergeWith₃ h' h'', Std.ExtTreeMap.mergeWith₃ h'' h']

variable [BEq α] [LawfulBEq α]

@[simp, grind=]
lemma filter_empty {α : Type} {f : α → β → Bool} {cmp : α → α → Ordering} : Std.ExtTreeMap.filter f (∅ : Std.ExtTreeMap α β cmp) = ∅ := by
  rfl

@[simp, grind=]
lemma toList_ofList {a : Std.ExtTreeMap α β cmp} : @Std.ExtTreeMap.ofList α β (@Std.ExtTreeMap.toList α β cmp _ a) cmp = a := by
  ext k v
  revert v
  by_cases h : ∃ v, (k, v) ∈ a.toList
  · rcases h with ⟨v, h⟩
    rw [@Std.ExtTreeMap.getElem?_ofList_of_mem α β cmp _ a.toList k k (by grind) v Std.ExtTreeMap.distinct_keys_toList h]
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at h
    rw [h]
    simp
  · simp only [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, not_exists] at h
    intros v
    simp only [h v, iff_false]
    rw [Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false]
    · simp
    · simp
      intros h'
      rw [←Std.ExtTreeMap.isSome_getKey?_iff_mem] at h'
      aesop

grind_pattern Std.ExtTreeMap.mergeWith₀ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern Std.ExtTreeMap.mergeWith₁ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern Std.ExtTreeMap.mergeWith₂ => k ∈ m₁, k ∈ m₂, Std.ExtTreeMap.mergeWith f m₁ m₂
grind_pattern Std.ExtTreeMap.mergeWith₃ => (Std.ExtTreeMap.mergeWith f m₁ m₂)[k]?

open Std ExtTreeMap

@[grind =]
lemma getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                      {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : Std.ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := by
  rw [Std.ExtTreeMap.getElem?_filter]
  simp

@[grind=]
lemma filter_mem {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∈ m) : f k m[k] → (Std.ExtTreeMap.filter f m)[k]? = .some m[k] := by
  intro h'
  rw [getElem?_filter]
  simp only [h, getElem?_pos, Option.filter_eq_some_iff, true_and]
  exact h'

@[grind=]
lemma filter_not_mem {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∉ m) : (Std.ExtTreeMap.filter f m)[k]? = .none := by
  rw [getElem?_filter]
  simp [h]

@[grind=]
lemma filter_not_pred {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∈ m) : ¬ (f k m[k]) → (Std.ExtTreeMap.filter f m)[k]? = .none := by
  intros h
  rw [getElem?_filter]
  grind

attribute [grind ext] Std.ExtTreeMap.ext_getElem?

end ExtTreeMap

lemma Option.filter_irrel {α : Type} {o : Option α} {p : α → Bool}
  (h : ∀ x, x ∈ o → p x) : o.filter p = o := by
  aesop (add simp Option.filter)

  variable {α : Type u} {β : Type v}

#min_imports
