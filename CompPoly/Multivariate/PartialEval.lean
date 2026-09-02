/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Gunton
-/
module

public import CompPoly.Multivariate.Operations
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Partial evaluation of the first variable of a `CMvPolynomial`

`partialEvalFirst a p` fixes variable `0` of a multivariate computable
polynomial to a scalar value, together with its evaluation lemma and the
per-variable degree-bound lemma.
-/

@[expose] public section

namespace CPoly

namespace CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalFirst_subst_degreeOf_le [Nontrivial R] (a : R)
    (i : Fin n) (j : Fin (n + 1)) :
    MvPolynomial.degreeOf i
      (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j :
        MvPolynomial (Fin n) R) ≤ if j = i.succ then 1 else 0 := by
  cases j using Fin.cases with
  | zero =>
      simp only [Fin.cases_zero, MvPolynomial.degreeOf_C, zero_le]
  | succ j =>
      by_cases h : j = i
      · subst h
        simp only [Fin.cases_succ, MvPolynomial.degreeOf_X_self, ↓reduceIte, Std.le_refl]
      · have hsucc : Fin.succ j ≠ i.succ := by
          intro h'
          exact h ((Fin.succ_injective n) h')
        have hi_ne_j : i ≠ j := fun hij => h hij.symm
        simp only [Fin.cases_succ, MvPolynomial.degreeOf_X, hi_ne_j, ↓reduceIte, hsucc,
          Std.le_refl]

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalFirst_eval₂_monomial_degreeOf_le [Nontrivial R] {deg : ℕ}
    (a : R) (i : Fin n) (s : Fin (n + 1) →₀ ℕ) (c : R)
    (hs : s i.succ ≤ deg) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Fin (n + 1) =>
          Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j)
        (MvPolynomial.monomial s c) : MvPolynomial (Fin n) R) ≤ deg := by
  rw [MvPolynomial.eval₂_monomial]
  refine (MvPolynomial.degreeOf_C_mul_le _ i c).trans ?_
  rw [Finsupp.prod]
  refine (MvPolynomial.degreeOf_prod_le i s.support
    (fun j => (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j :
      MvPolynomial (Fin n) R) ^ s j)).trans ?_
  calc
    (∑ x ∈ s.support,
        MvPolynomial.degreeOf i
          ((Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) x :
            MvPolynomial (Fin n) R) ^ s x))
        ≤ ∑ x ∈ s.support, s x * (if x = i.succ then 1 else 0) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact (MvPolynomial.degreeOf_pow_le i
            (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) x :
              MvPolynomial (Fin n) R) (s x)).trans
            (Nat.mul_le_mul_left _ (partialEvalFirst_subst_degreeOf_le a i x))
    _ ≤ s i.succ := by
          classical
          by_cases hi : i.succ ∈ s.support
          · rw [Finset.sum_eq_single i.succ]
            · simp only [↓reduceIte, mul_one, Std.le_refl]
            · intro x hx hne
              simp only [hne, ↓reduceIte, mul_zero]
            · intro hnot
              exact False.elim (hnot hi)
          · rw [Finset.sum_eq_zero]
            · simp only [zero_le]
            · intro x hx
              have hne : x ≠ i.succ := fun h => hi (h ▸ hx)
              simp only [hne, ↓reduceIte, mul_zero]
    _ ≤ deg := hs

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalFirst_eval₂_degreeOf_le [Nontrivial R] {deg : ℕ}
    (a : R) (i : Fin n) (p : MvPolynomial (Fin (n + 1)) R)
    (hDeg : ∀ s ∈ p.support, s i.succ ≤ deg) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Fin (n + 1) =>
          Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j)
        p : MvPolynomial (Fin n) R) ≤ deg := by
  rw [MvPolynomial.eval₂_eq]
  refine (MvPolynomial.degreeOf_sum_le i p.support
    (fun s => MvPolynomial.C (p.coeff s) *
      ∏ x ∈ s.support,
        (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) x :
          MvPolynomial (Fin n) R) ^ s x)).trans ?_
  apply Finset.sup_le
  intro s hs
  simpa only [MvPolynomial.eval₂_monomial, Finsupp.prod] using
    partialEvalFirst_eval₂_monomial_degreeOf_le (n := n) (R := R)
      (deg := deg) a i s (p.coeff s) (hDeg s hs)

/-! ## Core operation -/

/-- Fix variable 0 of a multivariate polynomial to a scalar value `a`. -/
def partialEvalFirst (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  bind₁ (Fin.cons (C a) X) p

/-! ## Evaluation lemma -/

/-- `partialEvalFirst a p` correctly implements partial evaluation. -/
theorem partialEvalFirst_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalFirst a p).eval v = p.eval (Fin.cons a v) := by
  unfold partialEvalFirst
  rw [eval_equiv, fromCMvPolynomial_bind₁]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id R := by
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval_C, RingHom.id_apply]
  have hv :
      (⇑(MvPolynomial.eval v) ∘
          fun i => fromCMvPolynomial
            (((Fin.cons (CMvPolynomial.C (n := n) a)
              (fun i : Fin n => CMvPolynomial.X (R := R) i)) :
                Fin (n + 1) → CMvPolynomial n R) i)) =
        Fin.cons a v := by
    funext i
    cases i using Fin.cases with
    | zero => simp only [Function.comp_apply, Fin.cons_zero, fromCMvPolynomial_C,
        MvPolynomial.eval_C]
    | succ i => simp only [Function.comp_apply, Fin.cons_succ, fromCMvPolynomial_X,
        MvPolynomial.eval_X]
  rw [hc, hv]
  exact (eval_equiv (p := p) (vals := Fin.cons a v)).symm

/-! ## Degree preservation -/

/-- `partialEvalFirst` preserves degree bounds for each remaining variable. -/
theorem partialEvalFirst_degreeOf_le [Nontrivial R] {deg : ℕ} (a : R)
    (i : Fin n) (p : CMvPolynomial (n + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf i.succ ≤ deg) :
    ∀ mono ∈ Lawful.monomials (partialEvalFirst a p), mono.degreeOf i ≤ deg := by
  intro mono hmono
  have hSupport :
      ∀ s ∈ (fromCMvPolynomial p).support, s i.succ ≤ deg := by
    apply MvPolynomial.degreeOf_le_iff.mp
    have hdegree := congrFun (degreeOf_equiv (p := p) (S := R)) i.succ
    rw [← hdegree]
    unfold CMvPolynomial.degreeOf
    apply Finset.sup_le
    intro mono hmono
    exact hDeg mono (by simpa using hmono)
  have hEval :
      MvPolynomial.degreeOf i (fromCMvPolynomial (partialEvalFirst a p)) ≤ deg := by
    unfold partialEvalFirst
    rw [fromCMvPolynomial_bind₁]
    have hvars :
        (fun i : Fin (n + 1) =>
            fromCMvPolynomial
              (((Fin.cons (CMvPolynomial.C (n := n) a)
                (fun i : Fin n => CMvPolynomial.X (R := R) i)) :
                  Fin (n + 1) → CMvPolynomial n R) i)) =
          (fun j : Fin (n + 1) =>
            Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j) := by
      funext j
      cases j using Fin.cases with
      | zero => simp only [Fin.cons_zero, fromCMvPolynomial_C, Fin.cases_zero]
      | succ j => simp only [Fin.cons_succ, fromCMvPolynomial_X, Fin.cases_succ]
    rw [hvars]
    exact partialEvalFirst_eval₂_degreeOf_le (n := n) (R := R) a i
      (fromCMvPolynomial p) hSupport
  have hdegree := congrFun (degreeOf_equiv (p := partialEvalFirst a p) (S := R)) i
  rw [← hdegree] at hEval
  exact (Finset.le_sup (s := (Lawful.monomials (partialEvalFirst a p)).toFinset)
    (f := fun m => m.degreeOf i) (by simpa using hmono)).trans hEval

end CMvPolynomial

end CPoly
