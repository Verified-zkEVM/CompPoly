import Aesop
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Cases

/-!
# Auxiliary lemmas for multivariate polynomials
-/

lemma List.distinct_of_inj_nodup {α β : Type*} {l : List α} {f : α → β}
    (h₁ : Function.Injective f) (h₂ : l.Nodup) :
    List.Pairwise (fun a b => f a ≠ f b) l := by
  induction' l with hd tl ih
  · simp
  · simp_all only [ne_eq, List.nodup_cons, List.pairwise_cons, and_true, forall_const]
    intros a' ha' contra
    have : hd = a' := by aesop
    grind

lemma Option.filter_irrel {α : Type} {o : Option α} {p : α → Bool}
    (h : ∀ x, x ∈ o → p x) : o.filter p = o := by
  aesop (add simp Option.filter)