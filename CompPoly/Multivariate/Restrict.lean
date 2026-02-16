/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Natalia Klaus, Frantisek Silvasi, Derek Sorensen
-/
import CompPoly.Multivariate.CMvPolynomial

/-!
# Lemmas for `CMvPolynomial.restrictBy`, `restrictTotalDegree`, and `restrictDegree`

Degree-bounded restriction of multivariate polynomials: filtering monomials by total degree
or per-variable degree bounds.

## TODO
- Prove correspondence with Mathlib via `fromCMvPolynomial`: e.g. that
  `fromCMvPolynomial (restrictTotalDegree d p) ∈ MvPolynomial.restrictTotalDegree (Fin n) R d`
  and similarly for `restrictDegree`. This would establish correctness wrt Mathlib's submodule API.
-/
namespace CPoly

open CMvPolynomial

variable {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R]

/-- Coefficient of `restrictBy keep p` at `m`: `p.coeff m` if `keep m`, else `0`. -/
lemma coeff_restrictBy (keep : CMvMonomial n → Prop) [DecidablePred keep]
    (m : CMvMonomial n) (p : CMvPolynomial n R) :
    (CMvPolynomial.restrictBy keep p).coeff m = if keep m then p.coeff m else 0 := by
  unfold CMvPolynomial.coeff CMvPolynomial.restrictBy
  unfold Lawful.fromUnlawful
  change
    ((Std.ExtTreeMap.filter (fun _ c => c != (0 : R))
      (Std.ExtTreeMap.filter (fun m' _ => decide (keep m')) p.1))[m]?.getD 0)
      = if keep m then p.1[m]?.getD 0 else 0
  let t : Unlawful n R := Std.ExtTreeMap.filter (fun m' _ => decide (keep m')) p.1
  have h0 :
      (Std.ExtTreeMap.filter (fun _ c => c != (0 : R)) t)[m]?.getD 0 = t[m]?.getD 0 := by
    exact (Unlawful.filter_get (v := (0 : R)) (m := m) (a := t))
  have h0' :
      (Std.ExtTreeMap.filter (fun _ c => c != (0 : R))
        (Std.ExtTreeMap.filter (fun m' _ => decide (keep m')) p.1))[m]?.getD 0
        = t[m]?.getD 0 := by
    simpa [t] using h0
  rw [h0']
  change (Std.ExtTreeMap.filter (fun m' _ => decide (keep m')) p.1)[m]?.getD 0 =
      if keep m then p.1[m]?.getD 0 else 0
  rw [Std.ExtTreeMap.getElem?_filter_with_getKey]
  by_cases hk : keep m
  · cases hopt : p.1[m]? <;> simp [hk, Option.filter]
  · cases hopt : p.1[m]? <;> simp [hk, Option.filter]

/-- Coefficient of `restrictTotalDegree d p` at `m`: `p.coeff m` if `m.totalDegree ≤ d`, else `0`. -/
@[simp]
lemma coeff_restrictTotalDegree (d : ℕ) (m : CMvMonomial n) (p : CMvPolynomial n R) :
    (CMvPolynomial.restrictTotalDegree d p).coeff m =
      if m.totalDegree ≤ d then p.coeff m else 0 := by
  simpa [CMvPolynomial.restrictTotalDegree] using
    (coeff_restrictBy (keep := fun m => m.totalDegree ≤ d) m p)

/-- Coefficient of `restrictDegree d p` at `m`: `p.coeff m` if `∀ i, m.degreeOf i ≤ d`, else `0`. -/
@[simp]
lemma coeff_restrictDegree (d : ℕ) (m : CMvMonomial n) (p : CMvPolynomial n R) :
    (CMvPolynomial.restrictDegree d p).coeff m =
      if ∀ i : Fin n, m.degreeOf i ≤ d then p.coeff m else 0 := by
  simpa [CMvPolynomial.restrictDegree] using
    (coeff_restrictBy (keep := fun m => ∀ i : Fin n, m.degreeOf i ≤ d) m p)

/-- When `m.totalDegree ≤ d`, coeff at `m` is unchanged by `restrictTotalDegree d`. -/
lemma coeff_restrictTotalDegree_eq_self_of_le {d : ℕ} {m : CMvMonomial n}
    {p : CMvPolynomial n R} (h : m.totalDegree ≤ d) :
    (CMvPolynomial.restrictTotalDegree d p).coeff m = p.coeff m := by
  simp [coeff_restrictTotalDegree, h]

/-- When `d < m.totalDegree`, coeff at `m` is `0` in `restrictTotalDegree d p`. -/
lemma coeff_restrictTotalDegree_eq_zero_of_lt {d : ℕ} {m : CMvMonomial n}
    {p : CMvPolynomial n R} (h : d < m.totalDegree) :
    (CMvPolynomial.restrictTotalDegree d p).coeff m = 0 := by
  simp [coeff_restrictTotalDegree, Nat.not_le_of_lt h]

/-- When `∀ i, m.degreeOf i ≤ d`, coeff at `m` is unchanged by `restrictDegree d`. -/
lemma coeff_restrictDegree_eq_self_of_le {d : ℕ} {m : CMvMonomial n}
    {p : CMvPolynomial n R} (h : ∀ i : Fin n, m.degreeOf i ≤ d) :
    (CMvPolynomial.restrictDegree d p).coeff m = p.coeff m := by
  simp [coeff_restrictDegree, h]

/-- When `¬(∀ i, m.degreeOf i ≤ d)`, coeff at `m` is `0` in `restrictDegree d p`. -/
lemma coeff_restrictDegree_eq_zero_of_not_le {d : ℕ} {m : CMvMonomial n}
    {p : CMvPolynomial n R} (h : ¬ (∀ i : Fin n, m.degreeOf i ≤ d)) :
    (CMvPolynomial.restrictDegree d p).coeff m = 0 := by
  simp [coeff_restrictDegree, h]

/-- Monomials in `restrictTotalDegree d p` have `totalDegree ≤ d`. -/
lemma totalDegree_le_of_mem_monomials_restrictTotalDegree {d : ℕ} {m : CMvMonomial n}
    {p : CMvPolynomial n R}
    (hm : m ∈ Lawful.monomials (CMvPolynomial.restrictTotalDegree d p)) :
    m.totalDegree ≤ d := by
  have hm' : m ∈ CMvPolynomial.restrictTotalDegree d p := (Lawful.mem_monomials_iff).1 hm
  have hcoeff_ne_zero : (CMvPolynomial.restrictTotalDegree d p).coeff m ≠ 0 := by
    simpa [CMvPolynomial.coeff] using
      (Lawful.getD_getElem?_ne_zero_of_mem
        (p := CMvPolynomial.restrictTotalDegree d p) (m := m) hm')
  by_cases hdeg : m.totalDegree ≤ d
  · exact hdeg
  · have hcoeff_zero : (CMvPolynomial.restrictTotalDegree d p).coeff m = 0 := by
      simp [coeff_restrictTotalDegree, hdeg]
    exact False.elim (hcoeff_ne_zero hcoeff_zero)

/-- Monomials in `restrictDegree d p` have `degreeOf i ≤ d` for each variable `i`. -/
lemma degreeOf_le_of_mem_monomials_restrictDegree {d : ℕ} {m : CMvMonomial n}
    {p : CMvPolynomial n R}
    (hm : m ∈ Lawful.monomials (CMvPolynomial.restrictDegree d p)) :
    ∀ i : Fin n, m.degreeOf i ≤ d := by
  have hm' : m ∈ CMvPolynomial.restrictDegree d p := (Lawful.mem_monomials_iff).1 hm
  have hcoeff_ne_zero : (CMvPolynomial.restrictDegree d p).coeff m ≠ 0 := by
    simpa [CMvPolynomial.coeff] using
      (Lawful.getD_getElem?_ne_zero_of_mem
        (p := CMvPolynomial.restrictDegree d p) (m := m) hm')
  by_cases hdeg : ∀ i : Fin n, m.degreeOf i ≤ d
  · exact hdeg
  · have hcoeff_zero : (CMvPolynomial.restrictDegree d p).coeff m = 0 := by
      simp [coeff_restrictDegree, hdeg]
    exact False.elim (hcoeff_ne_zero hcoeff_zero)

/-- `List.ofFn s` sum equals `∑ i, s i`. -/
private lemma list_ofFn_sum_eq_finSum {n : ℕ} (s : Fin n → ℕ) :
    (List.ofFn s).sum = ∑ i : Fin n, s i := by
  have hfin : (∑ x : Fin (List.ofFn s).length, (List.ofFn s)[x.1]) = (List.ofFn s).sum := by
    simpa using (Fin.sum_univ_fun_getElem (l := List.ofFn s) (f := fun x : ℕ => x))
  have hfin_get :
      (∑ x : Fin (List.ofFn s).length, s ⟨x.1, by simpa [List.length_ofFn] using x.2⟩) =
      (List.ofFn s).sum := by
    simpa [List.getElem_ofFn] using hfin
  have hsum_cast :
      (∑ x : Fin (List.ofFn s).length, s ⟨x.1, by simpa [List.length_ofFn] using x.2⟩) =
      ∑ i : Fin n, s i := by
    let e : Fin (List.ofFn s).length ≃ Fin n :=
      (Fin.castOrderIso (by simp [List.length_ofFn] : (List.ofFn s).length = n)).toEquiv
    refine (Fintype.sum_equiv e (fun x => s ⟨x.1, by simpa [List.length_ofFn] using x.2⟩)
        (fun i => s i) ?_)
    intro x
    have hx : (⟨x.1, by simpa [List.length_ofFn] using x.2⟩ : Fin n) =
        Fin.cast (by simp [List.length_ofFn] : (List.ofFn s).length = n) x := by
      apply Fin.ext
      rfl
    exact congrArg s hx
  exact hfin_get.symm.trans hsum_cast

/-- `Vector.ofFn s` sum equals `∑ i, s i`. -/
private lemma vector_ofFn_sum_eq_finSum {n : ℕ} (s : Fin n → ℕ) :
    (Vector.ofFn s).sum = ∑ i : Fin n, s i := by
  calc
    (Vector.ofFn s).sum = (Array.ofFn s).sum := by
      simp [Vector.sum, Vector.toArray_ofFn]
    _ = (Array.ofFn s).toList.sum := by
      exact (Array.sum_eq_sum_toList (as := Array.ofFn s)).symm
    _ = (List.ofFn s).sum := by
      exact congrArg List.sum (Array.toList_ofFn (f := s))
    _ = ∑ i : Fin n, s i := list_ofFn_sum_eq_finSum s

/-- Monomial `totalDegree` equals `Finsupp.sum` of its exponents. -/
private lemma totalDegree_eq_finsupp_sum {n : ℕ} (m : CMvMonomial n) :
    m.totalDegree = Finsupp.sum m.toFinsupp (fun _ e => e) := by
  have hof : (CMvMonomial.ofFinsupp m.toFinsupp).totalDegree =
      Finsupp.sum m.toFinsupp (fun _ e => e) := by
    unfold CMvMonomial.totalDegree CMvMonomial.ofFinsupp
    rw [Finsupp.sum_fintype]
    · simpa using (vector_ofFn_sum_eq_finSum (s := (m.toFinsupp : Fin n →₀ ℕ)))
    · intro i
      simp
  simpa [CMvMonomial.ofFinsupp_toFinsupp] using hof

/-- `restrictTotalDegree d p` has `totalDegree ≤ d`. -/
lemma totalDegree_restrictTotalDegree_le
    {R' : Type} [CommSemiring R'] [BEq R'] [LawfulBEq R']
    (d : ℕ) (p : CMvPolynomial n R') :
    (CMvPolynomial.restrictTotalDegree d p).totalDegree ≤ d := by
  classical
  unfold CMvPolynomial.totalDegree
  refine Finset.sup_le ?_
  intro s hs
  have hs' : s ∈ List.map CMvMonomial.toFinsupp
      (Lawful.monomials (CMvPolynomial.restrictTotalDegree d p)) := by
    exact (List.mem_toFinset).1 hs
  rcases (List.mem_map).1 hs' with ⟨m, hm, rfl⟩
  have hmdeg : m.totalDegree ≤ d :=
    totalDegree_le_of_mem_monomials_restrictTotalDegree (d := d) (p := p) hm
  simpa [totalDegree_eq_finsupp_sum (m := m)] using hmdeg

/-- `restrictTotalDegree d 0 = 0`. -/
@[simp]
lemma restrictTotalDegree_zero (d : ℕ) :
    CMvPolynomial.restrictTotalDegree d (0 : CMvPolynomial n R) = 0 := by
  ext m
  simpa [CMvPolynomial.coeff] using
    (coeff_restrictTotalDegree (d := d) (m := m) (p := (0 : CMvPolynomial n R)))

/-- `restrictDegree d 0 = 0`. -/
@[simp]
lemma restrictDegree_zero (d : ℕ) :
    CMvPolynomial.restrictDegree d (0 : CMvPolynomial n R) = 0 := by
  ext m
  simpa [CMvPolynomial.coeff] using
    (coeff_restrictDegree (d := d) (m := m) (p := (0 : CMvPolynomial n R)))

/-- Double `restrictTotalDegree` equals `restrictTotalDegree (min d d')`. -/
@[simp]
lemma restrictTotalDegree_restrictTotalDegree (d d' : ℕ) (p : CMvPolynomial n R) :
    CMvPolynomial.restrictTotalDegree d (CMvPolynomial.restrictTotalDegree d' p) =
      CMvPolynomial.restrictTotalDegree (min d d') p := by
  ext m
  by_cases h₁ : m.totalDegree ≤ d <;> by_cases h₂ : m.totalDegree ≤ d' <;>
    simp [coeff_restrictTotalDegree, h₁, h₂]

/-- Double `restrictDegree` equals `restrictDegree (min d d')`. -/
@[simp]
lemma restrictDegree_restrictDegree (d d' : ℕ) (p : CMvPolynomial n R) :
    CMvPolynomial.restrictDegree d (CMvPolynomial.restrictDegree d' p) =
      CMvPolynomial.restrictDegree (min d d') p := by
  ext m
  by_cases h₁ : ∀ i : Fin n, m.degreeOf i ≤ d
  · by_cases h₂ : ∀ i : Fin n, m.degreeOf i ≤ d'
    · have hmin : ∀ i : Fin n, m.degreeOf i ≤ min d d' := by
        intro i
        exact (le_min_iff.mpr ⟨h₁ i, h₂ i⟩)
      simp [coeff_restrictDegree, h₁, h₂, hmin]
    · have hmin : ¬ (∀ i : Fin n, m.degreeOf i ≤ min d d') := by
        intro h
        exact h₂ (fun i => (le_min_iff.mp (h i)).2)
      simp [coeff_restrictDegree, h₁, h₂]
  · have hmin : ¬ (∀ i : Fin n, m.degreeOf i ≤ min d d') := by
      intro h
      exact h₁ (fun i => (le_min_iff.mp (h i)).1)
    have hpair : ¬ (∀ i : Fin n, m.degreeOf i ≤ d ∧ m.degreeOf i ≤ d') := by
      intro h
      exact h₁ (fun i => (h i).1)
    simp [coeff_restrictDegree, h₁, hpair]

/-- `restrictTotalDegree d` and `restrictDegree d'` commute. -/
@[simp]
lemma restrictTotalDegree_restrictDegree_comm (d d' : ℕ) (p : CMvPolynomial n R) :
    CMvPolynomial.restrictTotalDegree d (CMvPolynomial.restrictDegree d' p) =
      CMvPolynomial.restrictDegree d' (CMvPolynomial.restrictTotalDegree d p) := by
  ext m
  by_cases h₁ : m.totalDegree ≤ d <;> by_cases h₂ : ∀ i : Fin n, m.degreeOf i ≤ d' <;>
    simp [coeff_restrictTotalDegree, coeff_restrictDegree, h₁, h₂]

end CPoly
