/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen, Dimitris Mitsios
-/
import CompPoly.Multivariate.CMvPolynomial

open Std

/-!
# Correctness lemmas for multivariate Horner evaluation

This file proves that the fixed-order multivariate Horner evaluator in
`CompPoly.Multivariate.CMvPolynomial` agrees with ordinary multivariate
evaluation.
-/

namespace CPoly

namespace CMvPolynomial

/-! ### Mathematical specifications for Horner helper functions -/

/-- Term-level specification: multiply the coefficient by the remaining variable powers. -/
private def eval₂HornerTermSpec {n : ℕ} {S : Type*} [CommSemiring S]
    (xs : ℕ → S) : ℕ → ℕ → HornerTerm n S → S
  | 0, _, term => term.2
  | fuel + 1, k, term =>
      eval₂HornerTermSpec xs fuel (k + 1) term * xs k ^ hornerExponent k term.1

/-- List-level specification for evaluating Horner terms as a commutative sum. -/
private def eval₂HornerTermsSpec {n : ℕ} {S : Type*} [CommSemiring S]
    (xs : ℕ → S) (fuel k : ℕ) (terms : List (HornerTerm n S)) : S :=
  (terms.map (eval₂HornerTermSpec xs fuel k)).sum

/-- Specification for one exponent group after its coefficient terms are evaluated. -/
private def groupWeightedSpec {n : ℕ} {S : Type*} [CommSemiring S]
    (weight : HornerTerm n S → S) (x : S) (group : HornerGroup n S) : S :=
  (group.2.map weight).sum * x ^ group.1

/-- Specification for a raw list of terms weighted by one variable exponent. -/
private def termsWeightedSpec {n : ℕ} {S : Type*} [CommSemiring S]
    (k : ℕ) (weight : HornerTerm n S → S) (x : S)
    (terms : List (HornerTerm n S)) : S :=
  (terms.map fun term => weight term * x ^ hornerExponent k term.1).sum

/-- Specification for evaluated exponent groups as a sparse sum of powers. -/
private def sparseGroupsSpec {S : Type*} [CommSemiring S]
    (x : S) (groups : List (ℕ × S)) : S :=
  (groups.map fun group => group.2 * x ^ group.1).sum

/-- The order invariant required by the sparse Horner gap fold. -/
private def descendingByExponent {α : Type*} (groups : List (ℕ × α)) : Prop :=
  groups.Pairwise fun group group' => group'.1 ≤ group.1

/-! ### Shared list algebra -/

private lemma foldl_add_eq_add_sum {α S : Type*} [CommSemiring S]
    (weight : α → S) :
    ∀ (terms : List α) (init : S),
      terms.foldl (fun acc term => acc + weight term) init =
        init + (terms.map weight).sum := by
  intro terms
  induction terms with
  | nil =>
      intro init
      simp
  | cons term terms ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ac_rfl

/-! ### Group sorting invariants -/

private lemma mem_insertHornerGroupDesc {n : ℕ} {S : Type*}
    (group x : HornerGroup n S) :
    ∀ groups, x ∈ insertHornerGroupDesc group groups ↔ x = group ∨ x ∈ groups := by
  intro groups
  induction groups with
  | nil =>
      simp [insertHornerGroupDesc]
  | cons group' groups ih =>
      by_cases h : group'.1 < group.1
      · simp [insertHornerGroupDesc, h]
      · simp [insertHornerGroupDesc, h, ih, or_left_comm]

private lemma insertHornerGroupDesc_pairwise {n : ℕ} {S : Type*}
    (group : HornerGroup n S) :
    ∀ groups, descendingByExponent groups →
      descendingByExponent (insertHornerGroupDesc group groups) := by
  intro groups
  induction groups with
  | nil =>
      intro _
      simp [descendingByExponent, insertHornerGroupDesc]
  | cons group' groups ih =>
      intro hsorted
      unfold descendingByExponent at hsorted ⊢
      simp only [insertHornerGroupDesc]
      by_cases hlt : group'.1 < group.1
      · simp only [hlt, ↓reduceIte, List.pairwise_cons] at hsorted ⊢
        refine ⟨?_, hsorted⟩
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with hyeq | hy
          · subst y
            exact Nat.le_of_lt hlt
          · exact Nat.le_trans (hsorted.1 y hy) (Nat.le_of_lt hlt)
      · simp only [hlt, ↓reduceIte, List.pairwise_cons] at hsorted ⊢
        refine ⟨?_, ih hsorted.2⟩
        intro y hy
        rw [mem_insertHornerGroupDesc] at hy
        rcases hy with rfl | hy
        · exact Nat.le_of_not_gt hlt
        · exact hsorted.1 y hy

private lemma sortHornerGroups_descending {n : ℕ} {S : Type*}
    (groups : List (HornerGroup n S)) :
    descendingByExponent (sortHornerGroups groups) := by
  unfold sortHornerGroups
  have hsort :
      ∀ (groups sorted : List (HornerGroup n S)),
        descendingByExponent sorted →
          descendingByExponent
            (groups.foldl (fun sorted group => insertHornerGroupDesc group sorted) sorted) := by
    intro groups
    induction groups with
    | nil =>
        intro sorted hsorted
        exact hsorted
    | cons group groups ih =>
        intro sorted hsorted
        simp only [List.foldl_cons]
        exact ih (insertHornerGroupDesc group sorted)
          (insertHornerGroupDesc_pairwise group sorted hsorted)
  exact hsort groups [] (by simp [descendingByExponent])

private lemma hornerGroups_descending {n : ℕ} {S : Type*}
    (k : ℕ) (terms : List (HornerTerm n S)) :
    descendingByExponent (hornerGroups k terms) := by
  unfold hornerGroups
  exact sortHornerGroups_descending (collectHornerGroups k terms)

/-! ### Grouping preserves weighted sums -/

private lemma groupWeightedSpec_insertHornerGroupDesc {n : ℕ} {S : Type*}
    [CommSemiring S] (weight : HornerTerm n S → S) (x : S)
    (group : HornerGroup n S) :
    ∀ groups,
      ((insertHornerGroupDesc group groups).map (groupWeightedSpec weight x)).sum =
        groupWeightedSpec weight x group + (groups.map (groupWeightedSpec weight x)).sum := by
  intro groups
  induction groups with
  | nil =>
      simp [insertHornerGroupDesc, groupWeightedSpec]
  | cons group' groups ih =>
      by_cases hlt : group'.1 < group.1
      · simp [insertHornerGroupDesc, hlt, groupWeightedSpec]
      · simp only [insertHornerGroupDesc, hlt, ↓reduceIte, List.map_cons, List.sum_cons]
        rw [ih]
        simp [add_assoc, add_left_comm, add_comm]

private lemma groupWeightedSpec_sortGroups {n : ℕ} {S : Type*}
    [CommSemiring S] (weight : HornerTerm n S → S) (x : S) :
    ∀ (groups sorted : List (HornerGroup n S)),
      ((groups.foldl (fun sorted group => insertHornerGroupDesc group sorted) sorted).map
          (groupWeightedSpec weight x)).sum =
        (groups.map (groupWeightedSpec weight x)).sum +
          (sorted.map (groupWeightedSpec weight x)).sum := by
  intro groups
  induction groups with
  | nil =>
      intro sorted
      simp
  | cons group groups ih =>
      intro sorted
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      rw [groupWeightedSpec_insertHornerGroupDesc]
      simp [add_left_comm, add_comm]

private lemma groupWeightedSpec_insertHornerTerm {n : ℕ} {S : Type*}
    [CommSemiring S] (k : ℕ) (weight : HornerTerm n S → S) (x : S)
    (term : HornerTerm n S) :
    ∀ groups,
      ((insertHornerTerm (hornerExponent k term.1) term groups).map
          (groupWeightedSpec weight x)).sum =
        weight term * x ^ hornerExponent k term.1 +
          (groups.map (groupWeightedSpec weight x)).sum := by
  intro groups
  induction groups with
  | nil =>
      simp [insertHornerTerm, groupWeightedSpec]
  | cons group groups ih =>
      by_cases h : group.1 = hornerExponent k term.1
      · simp only [insertHornerTerm, h, ↓reduceIte, List.map_cons, List.sum_cons]
        unfold groupWeightedSpec
        rw [h]
        simp only [List.map_cons, List.sum_cons]
        rw [add_mul]
        simp [add_assoc]
      · simp only [insertHornerTerm, h, ↓reduceIte, List.map_cons, List.sum_cons]
        rw [ih]
        simp [add_assoc, add_comm]

private lemma groupWeightedSpec_groupTerms {n : ℕ} {S : Type*}
    [CommSemiring S] (k : ℕ) (weight : HornerTerm n S → S) (x : S) :
    ∀ (terms : List (HornerTerm n S)) groups,
      (((terms.foldl
        (fun groups term => insertHornerTerm (hornerExponent k term.1) term groups)
        groups).map (groupWeightedSpec weight x)).sum) =
        termsWeightedSpec k weight x terms + (groups.map (groupWeightedSpec weight x)).sum := by
  intro terms
  induction terms with
  | nil =>
      intro groups
      simp [termsWeightedSpec]
  | cons term terms ih =>
      intro groups
      simp only [List.foldl_cons]
      rw [ih]
      rw [groupWeightedSpec_insertHornerTerm]
      simp [termsWeightedSpec]
      simp [add_assoc, add_left_comm, add_comm]

private lemma groupWeightedSpec_sortHornerGroups {n : ℕ} {S : Type*}
    [CommSemiring S] (weight : HornerTerm n S → S) (x : S)
    (groups : List (HornerGroup n S)) :
    ((sortHornerGroups groups).map (groupWeightedSpec weight x)).sum =
      (groups.map (groupWeightedSpec weight x)).sum := by
  unfold sortHornerGroups
  rw [groupWeightedSpec_sortGroups]
  simp

private lemma groupWeightedSpec_collectHornerGroups {n : ℕ} {S : Type*}
    [CommSemiring S] (k : ℕ) (weight : HornerTerm n S → S) (x : S)
    (terms : List (HornerTerm n S)) :
    ((collectHornerGroups k terms).map (groupWeightedSpec weight x)).sum =
      termsWeightedSpec k weight x terms := by
  unfold collectHornerGroups
  rw [groupWeightedSpec_groupTerms]
  simp

private lemma groupWeightedSpec_hornerGroups {n : ℕ} {S : Type*}
    [CommSemiring S] (k : ℕ) (weight : HornerTerm n S → S) (x : S)
    (terms : List (HornerTerm n S)) :
    ((hornerGroups k terms).map (groupWeightedSpec weight x)).sum =
      termsWeightedSpec k weight x terms := by
  unfold hornerGroups
  rw [groupWeightedSpec_sortHornerGroups]
  rw [groupWeightedSpec_collectHornerGroups]

/-! ### Sparse Horner over evaluated groups -/

private lemma evalSparseHornerGroups_foldl_invariant {S : Type*} [CommSemiring S]
    (x : S) :
    ∀ (groups : List (ℕ × S)) (state : ℕ × S),
      descendingByExponent (state :: groups) →
        let finalState := groups.foldl
          (fun state group =>
            let previousExponent := state.1
            let acc := state.2
            let exponent := group.1
            (exponent, acc * x ^ (previousExponent - exponent) + group.2))
          state
        finalState.2 * x ^ finalState.1 =
          state.2 * x ^ state.1 + sparseGroupsSpec x groups := by
  intro groups
  induction groups with
  | nil =>
      intro state _
      simp [sparseGroupsSpec]
  | cons group groups ih =>
      intro state hsorted
      unfold descendingByExponent at hsorted
      simp only [List.foldl_cons]
      have hcons :
          (∀ y ∈ group :: groups, y.1 ≤ state.1) ∧
            (group :: groups).Pairwise (fun group group' => group'.1 ≤ group.1) := by
        simpa [List.pairwise_cons] using hsorted
      have hle : group.1 ≤ state.1 := by
        exact hcons.1 group (by simp)
      have htail : descendingByExponent
          ((group.1, state.2 * x ^ (state.1 - group.1) + group.2) :: groups) := by
        unfold descendingByExponent
        simpa [List.pairwise_cons] using hcons.2
      rw [ih (group.1, state.2 * x ^ (state.1 - group.1) + group.2) htail]
      simp only [sparseGroupsSpec, List.map_cons, List.sum_cons]
      rw [add_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      simp [add_assoc, add_left_comm, add_comm]

private lemma evalSparseHornerGroups_eq_sparseGroupsSpec {S : Type*} [CommSemiring S]
    (x : S) :
    ∀ groups, descendingByExponent groups →
      evalSparseHornerGroups x groups = sparseGroupsSpec x groups := by
  intro groups hsorted
  cases groups with
  | nil =>
      simp [evalSparseHornerGroups, sparseGroupsSpec]
  | cons group groups =>
      unfold evalSparseHornerGroups
      change
        (let state := groups.foldl
          (fun state group =>
            let previousExponent := state.1
            let acc := state.2
            let exponent := group.1
            (exponent, acc * x ^ (previousExponent - exponent) + group.2))
          group
        state.2 * x ^ state.1) =
          sparseGroupsSpec x (group :: groups)
      rw [evalSparseHornerGroups_foldl_invariant x groups group hsorted]
      simp [sparseGroupsSpec]

/-! ### Recursive term evaluator correctness -/

private lemma descendingByExponent_map {α β : Type*} (f : α → β) :
    ∀ groups : List (ℕ × α), descendingByExponent groups →
      descendingByExponent (groups.map fun group => (group.1, f group.2)) := by
  intro groups
  induction groups with
  | nil =>
      intro _
      simp [descendingByExponent]
  | cons group groups ih =>
      intro hsorted
      unfold descendingByExponent at hsorted ⊢
      simp only [List.map_cons, List.pairwise_cons] at hsorted ⊢
      refine ⟨?_, ih hsorted.2⟩
      intro y hy
      simp only [List.mem_map] at hy
      rcases hy with ⟨group', hgroup', rfl⟩
      exact hsorted.1 group' hgroup'

private lemma eval₂HornerTerms_eq_eval₂HornerTermsSpec {n : ℕ} {S : Type*}
    [CommSemiring S] (xs : ℕ → S) :
    ∀ fuel k (terms : List (HornerTerm n S)),
      eval₂HornerTerms xs fuel k terms = eval₂HornerTermsSpec xs fuel k terms
  | 0, k, terms => by
      simp only [eval₂HornerTerms, eval₂HornerTermsSpec, eval₂HornerTermSpec]
      rw [foldl_add_eq_add_sum (fun term : HornerTerm n S => term.2)]
      simp
  | fuel + 1, k, terms => by
      unfold eval₂HornerTerms
      rw [evalSparseHornerGroups_eq_sparseGroupsSpec]
      · unfold sparseGroupsSpec eval₂HornerTermsSpec
        simp only [List.map_map]
        calc
          (List.map
              (((fun group => group.2 * xs k ^ group.1) ∘
                fun group => (group.1, eval₂HornerTerms xs fuel (k + 1) group.2)))
              (hornerGroups k terms)).sum
              =
            ((hornerGroups k terms).map
              (groupWeightedSpec
                (fun term : HornerTerm n S =>
                  eval₂HornerTermSpec xs fuel (k + 1) term)
                (xs k))).sum := by
                apply congrArg List.sum
                apply List.map_congr_left
                intro group _
                unfold groupWeightedSpec
                simp only [Function.comp_apply]
                rw [eval₂HornerTerms_eq_eval₂HornerTermsSpec xs fuel (k + 1) group.2]
                rfl
          _ = termsWeightedSpec k
              (fun term : HornerTerm n S => eval₂HornerTermSpec xs fuel (k + 1) term)
              (xs k) terms := by
                exact groupWeightedSpec_hornerGroups k
                  (fun term : HornerTerm n S =>
                    eval₂HornerTermSpec xs fuel (k + 1) term)
                  (xs k) terms
          _ = (List.map (eval₂HornerTermSpec xs (fuel + 1) k) terms).sum := by
                unfold termsWeightedSpec
                simp [eval₂HornerTermSpec]
      · exact descendingByExponent_map
          (fun terms => eval₂HornerTerms xs fuel (k + 1) terms)
          (hornerGroups k terms) (hornerGroups_descending k terms)

private lemma eval₂HornerTermSpec_eq_product {n : ℕ} {S : Type*} [CommSemiring S]
    (xs : ℕ → S) :
    ∀ fuel k (term : HornerTerm n S),
      eval₂HornerTermSpec xs fuel k term =
        term.2 * ∏ i : Fin fuel,
          xs (k + (i : ℕ)) ^ hornerExponent (k + (i : ℕ)) term.1
  | 0, k, term => by
      simp [eval₂HornerTermSpec]
  | fuel + 1, k, term => by
      simp only [eval₂HornerTermSpec]
      rw [eval₂HornerTermSpec_eq_product xs fuel (k + 1) term]
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, add_zero, Fin.val_succ]
      have hprod :
          (∏ x : Fin fuel,
            xs (k + (↑x + 1)) ^ hornerExponent (k + (↑x + 1)) term.1) =
          (∏ x : Fin fuel,
            xs (k + 1 + ↑x) ^ hornerExponent (k + 1 + ↑x) term.1) := by
        apply Finset.prod_congr rfl
        intro i _
        have hidx : k + (↑i + 1) = k + 1 + ↑i := by
          rw [← Nat.add_assoc, Nat.add_right_comm]
        rw [hidx]
      rw [hprod]
      ac_rfl

private lemma eval₂HornerTermSpec_eq_evalMonomial {S : Type*} {n : ℕ}
    [CommSemiring S] (vs : Fin n → S) (m : CMvMonomial n) (c : S) :
    eval₂HornerTermSpec
        (fun k => if h : k < n then vs ⟨k, h⟩ else 0) n 0 (m, c) =
      c * MonoR.evalMonomial vs m := by
  rw [eval₂HornerTermSpec_eq_product]
  congr 1
  unfold MonoR.evalMonomial
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  · simp
  · unfold hornerExponent
    simp [Vector.get]
    rfl

private lemma eval₂HornerTerms_fold_eq_eval₂_fold {R S : Type*} {n : ℕ}
    [Semiring R] [CommSemiring S] (f : R →+* S) (vs : Fin n → S) :
    ∀ (terms : List (CMvMonomial n × R)) (init : S),
      (terms.map fun term => (term.1, f term.2)).foldl
        (fun acc term => acc +
          eval₂HornerTermSpec
            (fun k => if h : k < n then vs ⟨k, h⟩ else 0) n 0 term)
        init =
      terms.foldl
        (fun acc term => f term.2 * MonoR.evalMonomial vs term.1 + acc)
        init := by
  intro terms
  induction terms with
  | nil =>
      intro init
      simp
  | cons term terms ih =>
      intro init
      simp only [List.map_cons, List.foldl_cons]
      rw [eval₂HornerTermSpec_eq_evalMonomial]
      rw [add_comm init (f term.2 * MonoR.evalMonomial vs term.1)]
      exact ih (f term.2 * MonoR.evalMonomial vs term.1 + init)

/-- Fixed-order multivariate Horner evaluation agrees with ordinary evaluation. -/
theorem eval₂Horner_eq_eval₂ {R S : Type*} {n : ℕ} [Semiring R] [CommSemiring S]
    (f : R →+* S) (vs : Fin n → S) (p : CMvPolynomial n R) :
    eval₂Horner f vs p = eval₂ f vs p := by
  unfold eval₂Horner eval₂
  rw [eval₂HornerTerms_eq_eval₂HornerTermsSpec]
  unfold eval₂HornerTermsSpec
  have hfold :
      (List.map
        (eval₂HornerTermSpec
          (fun k => if h : k < n then vs ⟨k, h⟩ else 0) n 0)
        (p.1.toList.map fun term => (term.1, f term.2))).sum =
      (p.1.toList.map fun term => (term.1, f term.2)).foldl
        (fun acc term => acc +
          eval₂HornerTermSpec
            (fun k => if h : k < n then vs ⟨k, h⟩ else 0) n 0 term)
        0 := by
    simpa using
      (foldl_add_eq_add_sum
        (fun term : HornerTerm n S =>
          eval₂HornerTermSpec
            (fun k => if h : k < n then vs ⟨k, h⟩ else 0) n 0 term)
        (p.1.toList.map fun term => (term.1, f term.2)) 0).symm
  rw [hfold]
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  exact eval₂HornerTerms_fold_eq_eval₂_fold f vs p.1.toList 0

/-- Fixed-order multivariate Horner evaluation agrees with ordinary evaluation. -/
theorem evalHorner_eq_eval {R : Type*} {n : ℕ} [CommSemiring R]
    (vs : Fin n → R) (p : CMvPolynomial n R) :
    evalHorner vs p = eval vs p := by
  exact eval₂Horner_eq_eval₂ (RingHom.id R) vs p

end CMvPolynomial

end CPoly
