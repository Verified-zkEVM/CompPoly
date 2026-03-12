/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.Bivariate.ToPoly
import Aesop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots

/-!
# Mathlib-Facing Bivariate Degree Helpers

This file collects degree- and evaluation-oriented helpers for Mathlib's bivariate
polynomial surface `R[X][Y]` that are useful as a bridge layer between CompPoly and
downstream developments such as ArkLib.

The intended split is:

- `CompPoly/Bivariate/*` for the native computable `CBivariate` representation;
- `CompPoly/ToMathlib/*` for Mathlib-facing transport and helper lemmas.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- `(i, j)`-coefficient of a polynomial, i.e. the coefficient of `X^i Y^j`. -/
def coeff (f : F[X][Y]) (i j : ℕ) : F :=
  (f.coeff j).coeff i

/-- The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY (f : F[X][Y]) : F[X] :=
  f.coeff (natDegree f)

/-- The polynomial coefficient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial. -/
@[simp, grind =]
theorem leadingCoeffY_eq_zero (f : F[X][Y]) : leadingCoeffY f = 0 ↔ f = 0 := by
  simp [leadingCoeffY]

/-- The polynomial coefficient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero. -/
@[simp, grind =]
lemma leadingCoeffY_ne_zero (f : F[X][Y]) : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  exact not_congr (leadingCoeffY_eq_zero (f := f))

/-- The `Y`-degree of a bivariate polynomial, as a natural number. -/
def natDegreeY (f : F[X][Y]) : ℕ :=
  Polynomial.natDegree f

/-- The `X`-degree of a bivariate polynomial. -/
def degreeX (f : F[X][Y]) : ℕ :=
  f.support.sup (fun n => (f.coeff n).natDegree)

/-- The total degree of a bivariate polynomial. -/
def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => (f.coeff m).natDegree + m)

/-- `(u, v)`-weighted degree of a polynomial.
The maximal `u * i + v * j` such that the polynomial `p`
contains a monomial `x^i * y^j`. -/
def weightedDegree (p : F[X][Y]) (u v : ℕ) : Option ℕ :=
  List.max? <|
    List.map (fun n => u * (p.coeff n).natDegree + v * n) (List.range p.natDegree.succ)

/-- The natural-number-valued `(u, v)`-weighted degree. -/
def natWeightedDegree (f : F[X][Y]) (u v : ℕ) : ℕ :=
  f.support.sup (fun m => u * (f.coeff m).natDegree + v * m)

variable {f : F[X][Y]}

/-- The weighted degree is always defined (never `none`). -/
lemma weightedDegree_ne_none (f : F[X][Y]) (u v : ℕ) :
    weightedDegree f u v ≠ none := by
  unfold weightedDegree
  aesop

theorem natWeightedDegree_mem_weight_list {u v : ℕ} :
    natWeightedDegree f u v ∈
      List.map (fun n => u * (f.coeff n).natDegree + v * n)
        (List.range f.natDegree.succ) := by
  classical
  by_cases hf : f = 0
  · simp [hf, natWeightedDegree]
  · have hsupp : f.support.Nonempty := by
      refine ⟨f.natDegree, ?_⟩
      exact Polynomial.natDegree_mem_support_of_nonzero (p := f) hf
    obtain ⟨m, hm, hsup⟩ :=
      Finset.exists_mem_eq_sup (s := f.support) hsupp
        (fun n => u * (f.coeff n).natDegree + v * n)
    have hm_le : m ≤ f.natDegree := Polynomial.le_natDegree_of_mem_supp (p := f) m hm
    have hm_range : m ∈ List.range f.natDegree.succ := by
      exact List.mem_range.mpr (Nat.lt_succ_of_le hm_le)
    have hw_mem :
        (u * (f.coeff m).natDegree + v * m) ∈
          List.map (fun n => u * (f.coeff n).natDegree + v * n)
            (List.range f.natDegree.succ) := by
      exact List.mem_map_of_mem (f := fun n => u * (f.coeff n).natDegree + v * n) hm_range
    unfold natWeightedDegree
    simpa [hsup] using hw_mem

theorem weight_le_natWeightedDegree_of_lt_natDegree_succ {u v n : ℕ}
    (hn : n < f.natDegree.succ) :
    u * (f.coeff n).natDegree + v * n ≤ natWeightedDegree f u v := by
  classical
  by_cases hf : f = 0
  · have hn0 : n < 1 := by simpa [hf] using hn
    have hzero : n = 0 := by simpa using hn0
    simp [hf, hzero, natWeightedDegree]
  · unfold natWeightedDegree
    by_cases hns : n ∈ f.support
    · exact Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hns
    · have hcoeff : f.coeff n = 0 := Polynomial.notMem_support_iff.1 hns
      have hnle : n ≤ f.natDegree := Nat.lt_succ_iff.mp hn
      have hmul : v * n ≤ v * f.natDegree := Nat.mul_le_mul_left v hnle
      have hdegmem : f.natDegree ∈ f.support := Polynomial.natDegree_mem_support_of_nonzero hf
      have hsup : u * (f.coeff f.natDegree).natDegree + v * f.natDegree ≤
          f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) := by
        exact Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hdegmem
      have hvdeg : v * f.natDegree ≤ u * (f.coeff f.natDegree).natDegree + v * f.natDegree := by
        exact Nat.le_add_left _ _
      have hvdeg' : v * f.natDegree ≤
          f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) :=
        le_trans hvdeg hsup
      have : v * n ≤ f.support.sup (fun m => u * (f.coeff m).natDegree + v * m) :=
        le_trans hmul hvdeg'
      simpa [hcoeff] using this

@[grind _=_]
lemma weightedDegree_eq_natWeightedDegree {u v : ℕ} :
    weightedDegree f u v = natWeightedDegree f u v := by
  by_cases hf : f = 0
  · simp [hf, weightedDegree, natWeightedDegree]
  · let w : ℕ → ℕ := fun n => u * (f.coeff n).natDegree + v * n
    let xs : List ℕ := List.map w (List.range f.natDegree.succ)
    have ha : natWeightedDegree f u v ∈ xs := by
      simpa [xs, w] using (natWeightedDegree_mem_weight_list (f := f) (u := u) (v := v))
    have hle : ∀ b, b ∈ xs → b ≤ natWeightedDegree f u v := by
      intro b hb
      rcases List.mem_map.1 hb with ⟨n, hn, rfl⟩
      have hnlt : n < f.natDegree.succ := List.mem_range.1 hn
      exact
        weight_le_natWeightedDegree_of_lt_natDegree_succ
          (f := f) (u := u) (v := v) (n := n) hnlt
    have hmax : xs.max? = some (natWeightedDegree f u v) := by
      apply (List.max?_eq_some_iff (xs := xs) (a := natWeightedDegree f u v)).2
      refine ⟨ha, ?_⟩
      intro b hb
      exact hle b hb
    simpa [weightedDegree, xs, w] using hmax

/-- The total degree of a bivariate polynomial is equal to the `(1, 1)`-weighted degree. -/
@[grind _=_]
lemma total_deg_as_weighted_deg :
    totalDegree f = natWeightedDegree f 1 1 := by
  simp [natWeightedDegree, totalDegree]

/-- The `X`-degree of a bivariate polynomial is equal to the `(1, 0)`-weighted degree. -/
@[grind _=_]
lemma degreeX_as_weighted_deg :
    degreeX f = natWeightedDegree f 1 0 := by
  simp [degreeX, natWeightedDegree]

/-- The `Y`-degree of a bivariate polynomial is equal to the `(0, 1)`-weighted degree. -/
@[grind _=_]
lemma degreeY_as_weighted_deg :
    natDegreeY f = natWeightedDegree f 0 1 := by
  by_cases hf : f = 0
  · simp [hf, natDegreeY, natWeightedDegree]
  · rw [
      natDegreeY, natWeightedDegree,
      Polynomial.natDegree_eq_support_max' (p := f) hf, Finset.max'_eq_sup'
    ]
    simp [Finset.sup'_eq_sup]

/-- Over an integral domain, the product of two non-zero bivariate polynomials is non-zero. -/
@[grind ←]
lemma mul_ne_zero [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 :=
  _root_.mul_ne_zero hf hg

/-- Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees. -/
@[simp, grind _=_]
lemma degreeY_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    natDegreeY (f * g) = natDegreeY f + natDegreeY g := by
  simpa [natDegreeY] using (Polynomial.natDegree_mul hf hg)

theorem coeff_natDegree_le_degreeX (f : F[X][Y]) (n : ℕ) : (f.coeff n).natDegree ≤ degreeX f := by
  classical
  unfold degreeX
  by_cases hn : n ∈ f.support
  · exact Finset.le_sup (s := f.support) (f := fun m => (f.coeff m).natDegree) hn
  · have hcoeff : f.coeff n = 0 := by
      exact Polynomial.notMem_support_iff.mp hn
    simp [hcoeff]

theorem degreeX_mul_le (f g : F[X][Y]) : degreeX (f * g) ≤ degreeX f + degreeX g := by
  classical
  unfold degreeX
  refine Finset.sup_le ?_
  intro k hk
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.antidiagonal k)
    (f := fun x : ℕ × ℕ => f.coeff x.1 * g.coeff x.2)
    (n := degreeX f + degreeX g) ?_
  intro x hx
  have hf : (f.coeff x.1).natDegree ≤ degreeX f := coeff_natDegree_le_degreeX f x.1
  have hg : (g.coeff x.2).natDegree ≤ degreeX g := coeff_natDegree_le_degreeX g x.2
  exact le_trans (Polynomial.natDegree_mul_le (p := f.coeff x.1) (q := g.coeff x.2))
    (Nat.add_le_add hf hg)

theorem exists_max_index_degreeX (f : F[X][Y]) (hf : f ≠ 0) :
    ∃ mm ∈ f.support,
      (f.coeff mm).natDegree = degreeX f ∧
      ∀ n, mm < n → (f.coeff n).natDegree < degreeX f ∨ f.coeff n = 0 := by
  classical
  let s₁ : Finset ℕ := f.support.filter (fun n => (f.coeff n).natDegree = degreeX f)
  have hs₁ : s₁.Nonempty := by
    have hsupp : f.support.Nonempty := (Polynomial.support_nonempty).2 hf
    obtain ⟨m, hm_mem, hm_sup⟩ :=
      Finset.exists_mem_eq_sup (s := f.support) (h := hsupp)
        (f := fun n => (f.coeff n).natDegree)
    refine ⟨m, ?_⟩
    have hm_deg : (f.coeff m).natDegree = degreeX f := by
      simpa [Polynomial.Bivariate.degreeX] using hm_sup.symm
    simp [s₁, hm_mem, hm_deg]

  set mm : ℕ := s₁.max' hs₁ with hmm
  refine ⟨mm, ?_, ?_, ?_⟩
  · have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have : mm ∈ f.support ∧ (f.coeff mm).natDegree = degreeX f := by
      simpa [s₁] using (Finset.mem_filter.1 hmm_mem)
    exact this.1
  · have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have : mm ∈ f.support ∧ (f.coeff mm).natDegree = degreeX f := by
      simpa [s₁] using (Finset.mem_filter.1 hmm_mem)
    exact this.2
  · have hmm_mem : mm ∈ s₁ := by
      simpa [hmm] using (Finset.max'_mem s₁ hs₁)
    have hmm_upper : ∀ b ∈ s₁, b ≤ mm := by
      have hchar : mm ∈ s₁ ∧ ∀ b, b ∈ s₁ → b ≤ mm := by
        simpa [hmm] using
          (Finset.max'_eq_iff (s := s₁) (H := hs₁) (a := mm)).1 rfl
      exact fun b hb => hchar.2 b hb

    intro n hmn
    by_cases hn0 : f.coeff n = 0
    · exact Or.inr hn0
    · have hn_support : n ∈ f.support := by
        exact (Polynomial.mem_support_iff).2 hn0
      have hn_le : (f.coeff n).natDegree ≤ degreeX f := coeff_natDegree_le_degreeX f n
      have hn_ne : (f.coeff n).natDegree ≠ degreeX f := by
        intro hEq
        have hn_s₁ : n ∈ s₁ := by
          simp [s₁, hn_support, hEq]
        have hn_le_mm : n ≤ mm := hmm_upper n hn_s₁
        exact (not_le_of_gt hmn) hn_le_mm
      exact Or.inl (lt_of_le_of_ne hn_le hn_ne)

theorem natDegree_sum_eq_of_unique {α : Type*} {s : Finset α} {f : α → F[X]} {deg : ℕ}
    (mx : α) (hmx : mx ∈ s) :
    (f mx).natDegree = deg →
    (∀ y ∈ s, y ≠ mx → (f y).natDegree < deg ∨ f y = 0) →
    (∑ x ∈ s, f x).natDegree = deg := by
  intro hdeg hothers
  classical
  have hle : ∀ y ∈ s, (f y).natDegree ≤ deg := by
    intro y hy
    by_cases hym : y = mx
    · subst hym
      simp [hdeg]
    · have hy' := hothers y hy hym
      cases hy' with
      | inl hlt =>
          exact le_of_lt hlt
      | inr hy0 =>
          simp [hy0]
  have hSle : (∑ x ∈ s, f x).natDegree ≤ deg :=
    Polynomial.natDegree_sum_le_of_forall_le (s := s) (f := f) (n := deg) hle
  by_cases hdeg0 : deg = 0
  · subst hdeg0
    exact Nat.eq_zero_of_le_zero hSle
  · have hmx_ne0 : f mx ≠ 0 := by
      intro h0
      apply hdeg0
      have : (0 : ℕ) = deg := by
        simpa [h0] using hdeg
      exact this.symm
    have hmx_coeff_ne0 : (f mx).coeff deg ≠ 0 := by
      have hlc : (f mx).leadingCoeff ≠ 0 :=
        (Polynomial.leadingCoeff_ne_zero).2 hmx_ne0
      simpa [Polynomial.leadingCoeff, hdeg] using hlc
    have hcoeff_others : ∀ y ∈ s, y ≠ mx → (f y).coeff deg = 0 := by
      intro y hy hym
      have hy' := hothers y hy hym
      cases hy' with
      | inl hlt =>
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      | inr hy0 =>
          simp [hy0]
    have hsum_coeff : (∑ y ∈ s, (f y).coeff deg) = (f mx).coeff deg := by
      refine Finset.sum_eq_single_of_mem mx hmx ?_
      intro y hy hym
      exact hcoeff_others y hy hym
    have hcoeff_eq : (∑ x ∈ s, f x).coeff deg = (f mx).coeff deg := by
      rw [Polynomial.finset_sum_coeff (s := s) (f := f) (n := deg)]
      exact hsum_coeff
    have hcoeff_ne0 : (∑ x ∈ s, f x).coeff deg ≠ 0 := by
      simpa [hcoeff_eq] using hmx_coeff_ne0
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hSle hcoeff_ne0

theorem degreeX_mul_ge [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    degreeX f + degreeX g ≤ degreeX (f * g) := by
  classical
  rcases exists_max_index_degreeX f hf with ⟨mmfx, hmmfx, hmmfx_deg, hmmfx_max⟩
  rcases exists_max_index_degreeX g hg with ⟨mmgx, hmmgx, hmmgx_deg, hmmgx_max⟩
  let N : ℕ := mmfx + mmgx
  let deg : ℕ := degreeX f + degreeX g
  let term : ℕ × ℕ → F[X] := fun x => f.coeff x.1 * g.coeff x.2
  have hmx : (mmfx, mmgx) ∈ Finset.antidiagonal N := by
    simp [Finset.mem_antidiagonal, N]
  have hfx0 : f.coeff mmfx ≠ 0 := by
    exact mem_support_iff.mp hmmfx
  have hgx0 : g.coeff mmgx ≠ 0 := by
    exact mem_support_iff.mp hmmgx
  have hterm_mx : (term (mmfx, mmgx)).natDegree = deg := by
    simpa [term, deg, hmmfx_deg, hmmgx_deg] using
      (Polynomial.natDegree_mul (p := f.coeff mmfx) (q := g.coeff mmgx) hfx0 hgx0)
  have hterm_other :
      ∀ y ∈ Finset.antidiagonal N, y ≠ (mmfx, mmgx) →
        (term y).natDegree < deg ∨ term y = 0 := by
    intro y hy hyne
    rcases y with ⟨i, j⟩
    have hij : i + j = N := by
      simpa [Finset.mem_antidiagonal] using hy
    have hij' : i + j = mmfx + mmgx := by
      simpa [N] using hij
    have hlt : mmfx < i ∨ mmgx < j := by
      by_contra hcontra
      have hi : i ≤ mmfx :=
        le_of_not_gt (fun hlt => hcontra (Or.inl hlt))
      have hj : j ≤ mmgx :=
        le_of_not_gt (fun hlt => hcontra (Or.inr hlt))
      have h1 : i + j ≤ i + mmgx := Nat.add_le_add_left hj i
      have h2 : mmfx + mmgx ≤ i + mmgx := by
        simpa [hij'] using h1
      have hmmfx_le_i : mmfx ≤ i := (Nat.add_le_add_iff_right).1 h2
      have h3 : i + j ≤ mmfx + j := Nat.add_le_add_right hi j
      have h4 : mmfx + mmgx ≤ mmfx + j := by
        simpa [hij'] using h3
      have hmmgx_le_j : mmgx ≤ j := (Nat.add_le_add_iff_left).1 h4
      have hi_eq : i = mmfx := Nat.le_antisymm hi hmmfx_le_i
      have hj_eq : j = mmgx := Nat.le_antisymm hj hmmgx_le_j
      exact hyne (by
        cases hi_eq
        cases hj_eq
        rfl)
    cases hlt with
    | inl hi_lt =>
        have hfi : (f.coeff i).natDegree < degreeX f ∨ f.coeff i = 0 :=
          hmmfx_max i hi_lt
        cases hfi with
        | inr hfi0 =>
            right
            simp [term, hfi0]
        | inl hfi_lt =>
            by_cases hgj0 : g.coeff j = 0
            · right
              simp [term, hgj0]
            · left
              have hnat_le :
                  (term (i, j)).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
                simpa [term] using
                  (Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j))
              have hgj_le : (g.coeff j).natDegree ≤ degreeX g :=
                coeff_natDegree_le_degreeX g j
              have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
                have := Nat.add_lt_add_of_lt_of_le hfi_lt hgj_le
                simpa [deg] using this
              exact lt_of_le_of_lt hnat_le hsum_lt
    | inr hj_lt =>
        have hgj : (g.coeff j).natDegree < degreeX g ∨ g.coeff j = 0 :=
          hmmgx_max j hj_lt
        cases hgj with
        | inr hgj0 =>
            right
            simp [term, hgj0]
        | inl hgj_lt =>
            by_cases hfi0 : f.coeff i = 0
            · right
              simp [term, hfi0]
            · left
              have hnat_le :
                  (term (i, j)).natDegree ≤ (f.coeff i).natDegree + (g.coeff j).natDegree := by
                simpa [term] using
                  (Polynomial.natDegree_mul_le (p := f.coeff i) (q := g.coeff j))
              have hfi_le : (f.coeff i).natDegree ≤ degreeX f :=
                coeff_natDegree_le_degreeX f i
              have hsum_lt : (f.coeff i).natDegree + (g.coeff j).natDegree < deg := by
                have := Nat.add_lt_add_of_le_of_lt hfi_le hgj_lt
                simpa [deg] using this
              exact lt_of_le_of_lt hnat_le hsum_lt
  have hsum_nat : (∑ x ∈ Finset.antidiagonal N, term x).natDegree = deg := by
    exact natDegree_sum_eq_of_unique (mx := (mmfx, mmgx)) (hmx := hmx) hterm_mx hterm_other
  have hcoeff_nat : ((f * g).coeff N).natDegree = deg := by
    have hcoeff : (f * g).coeff N = ∑ x ∈ Finset.antidiagonal N, term x := by
      simpa [term] using (Polynomial.coeff_mul f g N)
    simpa [hcoeff] using hsum_nat
  have hle : deg ≤ degreeX (f * g) := by
    have hle' : ((f * g).coeff N).natDegree ≤ degreeX (f * g) :=
      coeff_natDegree_le_degreeX (f * g) N
    simpa [hcoeff_nat] using hle'
  simpa [deg] using hle

theorem degreeX_mul [IsDomain F] (f g : F[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    degreeX (f * g) = degreeX f + degreeX g := by
  exact le_antisymm (degreeX_mul_le f g) (degreeX_mul_ge f g hf hg)

/-- The evaluation at a point of a bivariate polynomial in the first variable `X`. -/
def evalX (a : F) (f : F[X][Y]) : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/-- The evaluation at a point of a bivariate polynomial in the second variable `Y`. -/
def evalY (a : F) (f : F[X][Y]) : Polynomial F :=
  Polynomial.eval (Polynomial.C a) f

end Semiring

section CommSemiring

variable [CommSemiring F]

lemma evalX_eq_map (x : F) (f : F[X][Y]) :
    Polynomial.Bivariate.evalX x f = f.map (Polynomial.evalRingHom x) := by
  classical
  ext n
  simp [Polynomial.Bivariate.evalX, Polynomial.toFinsupp_apply]

end CommSemiring

section CommRing

variable [CommRing F]

lemma degreeX_swap (f : F[X][Y]) :
    Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap f) =
      Polynomial.Bivariate.natDegreeY f := by
  classical
  have hcoeff :
      ∀ (g : F[X][Y]) (i j : ℕ),
        Polynomial.Bivariate.coeff (Polynomial.Bivariate.swap g) i j =
          Polynomial.Bivariate.coeff g j i := by
    intro g i j
    induction g using Polynomial.induction_on' with
    | add p q hp hq =>
        have hp' : ((Polynomial.Bivariate.swap p).coeff j).coeff i = (p.coeff i).coeff j := by
          exact hp
        have hq' : ((Polynomial.Bivariate.swap q).coeff j).coeff i = (q.coeff i).coeff j := by
          exact hq
        simp [Polynomial.Bivariate.coeff, -Polynomial.Bivariate.swap_apply, hp', hq']
    | monomial n a =>
        induction a using Polynomial.induction_on' with
        | add p q hp hq =>
            have hp' : ((Polynomial.Bivariate.swap ((monomial n) p)).coeff j).coeff i =
                (((monomial n) p).coeff i).coeff j := by exact hp
            have hq' : ((Polynomial.Bivariate.swap ((monomial n) q)).coeff j).coeff i =
                (((monomial n) q).coeff i).coeff j := by exact hq
            simp [Polynomial.Bivariate.coeff, map_add,
              -Polynomial.Bivariate.swap_apply, hp', hq']
        | monomial m r =>
            by_cases hi : n = i
            · subst hi
              by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  -Polynomial.Bivariate.swap_apply]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hj]
            · by_cases hj : m = j
              · subst hj
                simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hi]
              · simp [Polynomial.Bivariate.coeff, Polynomial.Bivariate.swap_monomial_monomial,
                  Polynomial.coeff_monomial, -Polynomial.Bivariate.swap_apply, hi, hj]

  unfold Polynomial.Bivariate.degreeX Polynomial.Bivariate.natDegreeY
  by_cases hf : f = 0
  · subst hf
    simp
  · apply le_antisymm
    · refine Finset.sup_le_iff.2 ?_
      intro n hn
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have hfm : f.coeff m = 0 := coeff_eq_zero_of_natDegree_lt hm
      have hmn : ((Polynomial.Bivariate.swap f).coeff n).coeff m = (f.coeff m).coeff n := by
        exact hcoeff f m n
      rw [hmn]
      simp [hfm]
    · have hNmem : natDegree f ∈ f.support :=
        Polynomial.natDegree_mem_support_of_nonzero hf
      have hcoeffN0 : f.coeff (natDegree f) ≠ 0 := by
        exact mem_support_iff.mp hNmem
      let n : ℕ := (f.coeff (natDegree f)).natDegree
      have hnmem : n ∈ (f.coeff (natDegree f)).support := by
        exact natDegree_mem_support_of_nonzero hcoeffN0
      have hcoeffn : (f.coeff (natDegree f)).coeff n ≠ 0 := by
        exact mem_support_iff.mp hnmem
      have hEq : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) =
          (f.coeff (natDegree f)).coeff n := by
        exact hcoeff f f.natDegree n
      have hswapCoeff : ((Polynomial.Bivariate.swap f).coeff n).coeff (natDegree f) ≠ 0 := by
        simpa [hEq, -Polynomial.Bivariate.swap_apply] using hcoeffn
      have hNle_natDeg : natDegree f ≤ ((Polynomial.Bivariate.swap f).coeff n).natDegree := by
        exact le_natDegree_of_ne_zero hswapCoeff
      have hcoeff_nonzero : (Polynomial.Bivariate.swap f).coeff n ≠ 0 := by
        intro hzero
        apply hswapCoeff
        rw [hzero]
        simp
      have hn_support : n ∈ (Polynomial.Bivariate.swap f).support := by
        exact mem_support_iff.mpr hcoeff_nonzero
      have hn_le_degX :
          ((Polynomial.Bivariate.swap f).coeff n).natDegree ≤
            (Polynomial.Bivariate.swap f).support.sup
              (fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) :=
        Finset.le_sup (f := fun k => ((Polynomial.Bivariate.swap f).coeff k).natDegree) hn_support
      exact le_trans hNle_natDeg hn_le_degX

lemma evalY_eq_evalX_swap (y : F) (f : F[X][Y]) :
    Polynomial.Bivariate.evalY y f =
      Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
  classical
  letI : Algebra F[X] F[X] := Polynomial.algebra (R := F) (A := F)
  have eval_eq_aeval : Polynomial.eval (Polynomial.C y) f = aeval (Polynomial.C y) f := by
    simp [Polynomial.aeval_def]
  have mapAlgHom_eq_map :
      Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f)
        = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
    exact rfl
  calc
    Polynomial.Bivariate.evalY y f
        = Polynomial.eval (Polynomial.C y) f := by
            rfl
    _ = aeval (Polynomial.C y) f := by
      exact eval_eq_aeval
    _ = Polynomial.mapAlgHom (aeval y : F[X] →ₐ[F] F) (Polynomial.Bivariate.swap f) := by
      exact aveal_eq_map_swap y f
    _ = (Polynomial.Bivariate.swap f).map (Polynomial.evalRingHom y) := by
      exact mapAlgHom_eq_map
    _ = Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap f) := by
      exact (evalX_eq_map y (Polynomial.Bivariate.swap f)).symm

lemma natDegreeY_swap (f : F[X][Y]) :
    Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
      Polynomial.Bivariate.degreeX f := by
  classical
  have h := degreeX_swap (F := F) (f := Polynomial.Bivariate.swap f)
  have hs : Polynomial.Bivariate.swap (R := F) (Polynomial.Bivariate.swap f) = f := by
    simpa using (Polynomial.Bivariate.swap (R := F)).left_inv f
  have h' :
      Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap f) =
        Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) := by
    simpa using h.symm
  have hdeg :
      Polynomial.Bivariate.degreeX (Polynomial.Bivariate.swap (Polynomial.Bivariate.swap f)) =
        Polynomial.Bivariate.degreeX f := by
    simpa using congrArg Polynomial.Bivariate.degreeX hs
  exact h'.trans hdeg

end CommRing

section Field

variable [Field F] [DecidableEq F]

lemma card_evalX_eq_zero_le_degreeX (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun x => evalX x A = 0)).card ≤ degreeX A := by
  classical
  obtain ⟨j0, hj0mem, hj0deg, _⟩ := exists_max_index_degreeX A hA
  have hc0 : A.coeff j0 ≠ 0 := mem_support_iff.mp hj0mem
  let S : Finset F := P.filter (fun x => evalX x A = 0)
  have hsub : S.val ⊆ (A.coeff j0).roots := by
    intro x hx
    have hxS : x ∈ S := by
      simpa [S] using hx
    have hxEval : evalX x A = 0 := (Finset.mem_filter.1 hxS).2
    have hxcoeff : (A.coeff j0).eval x = 0 := by
      have := congrArg (fun q : Polynomial F => q.coeff j0) hxEval
      simpa [evalX_eq_map, Polynomial.coeff_map] using this
    have hxroot : Polynomial.IsRoot (A.coeff j0) x := by
      simpa [Polynomial.IsRoot] using hxcoeff
    exact (Polynomial.mem_roots hc0).2 hxroot
  have hcard : S.card ≤ (A.coeff j0).natDegree := by
    simpa using (Polynomial.card_le_degree_of_subset_roots (p := A.coeff j0) (Z := S) hsub)
  simpa [S, hj0deg] using hcard

omit [DecidableEq F] in
lemma descend_evalX {A B G A1 B1 : F[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
    (x : F) (hx : evalX x G ≠ 0) (q : F[X]) (h : evalX x B = q * evalX x A) :
    evalX x B1 = q * evalX x A1 := by
  have hmap : B.map (Polynomial.evalRingHom x) = q * (A.map (Polynomial.evalRingHom x)) := by
    simpa [evalX_eq_map] using h
  have hmap' :
      ((G * B1).map (Polynomial.evalRingHom x)) =
        q * ((G * A1).map (Polynomial.evalRingHom x)) := by
    simpa [hB, hA] using hmap
  have hmap'' : (G.map (Polynomial.evalRingHom x)) * (B1.map (Polynomial.evalRingHom x))
      = q * ((G.map (Polynomial.evalRingHom x)) * (A1.map (Polynomial.evalRingHom x))) := by
    simpa [mul_assoc] using hmap'
  have hg' : (G.map (Polynomial.evalRingHom x)) ≠ 0 := by
    simpa [evalX_eq_map] using hx
  have hcancel : (B1.map (Polynomial.evalRingHom x)) = q * (A1.map (Polynomial.evalRingHom x)) := by
    apply mul_left_cancel₀ hg'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmap''
  simpa [evalX_eq_map] using hcancel

lemma exists_x_preserve_natDegreeY (B : F[X][Y]) (hB : B ≠ 0) (P : Finset F)
    (hcard : degreeX B < P.card) :
    ∃ x ∈ P, (evalX x B).natDegree = natDegreeY B := by
  classical
  let p : F[X] := leadingCoeffY B
  have hp0 : p ≠ 0 := by
    simpa [p] using (leadingCoeffY_ne_zero (f := B)).2 hB
  have hp_deg : p.natDegree ≤ degreeX B := by
    simpa [p, leadingCoeffY, natDegreeY] using
      (coeff_natDegree_le_degreeX B B.natDegree)
  have hlt : p.natDegree < P.card := lt_of_le_of_lt hp_deg hcard
  have hx : ∃ x ∈ P, p.eval x ≠ 0 := by
    by_contra h
    push_neg at h
    have hsub : P.val ⊆ p.roots := by
      intro x hxP
      have hxroot : Polynomial.IsRoot p x := by
        exact h x hxP
      exact (Polynomial.mem_roots hp0).2 hxroot
    have hle : P.card ≤ p.natDegree := by
      simpa using (Polynomial.card_le_degree_of_subset_roots (p := p) (Z := P) hsub)
    exact (not_lt_of_ge hle) hlt
  rcases hx with ⟨x, hxP, hxne⟩
  refine ⟨x, hxP, ?_⟩
  have hnat_le : (evalX x B).natDegree ≤ natDegreeY B := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hBN : B.coeff N = 0 := coeff_eq_zero_of_natDegree_lt hN
    simp [evalX_eq_map, Polynomial.coeff_map, hBN]
  have hcoeff : (evalX x B).coeff (natDegreeY B) ≠ 0 := by
    simpa [p, leadingCoeffY, natDegreeY, evalX_eq_map, Polynomial.coeff_map] using hxne
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hnat_le hcoeff

end Field

end
end Polynomial.Bivariate

namespace CompPoly
namespace CBivariate

theorem natWeightedDegree_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) (u v : ℕ) :
    Polynomial.Bivariate.natWeightedDegree (toPoly f) u v =
      CBivariate.natWeightedDegree (R := R) f u v := by
  unfold Polynomial.Bivariate.natWeightedDegree CBivariate.natWeightedDegree
  rw [support_toPoly_outer]
  refine Finset.sup_congr rfl ?_
  intro j hj
  rw [coeff_toPoly_Y]
  simpa using
    congrArg (fun n => u * n + v * j) (Eq.symm (CPolynomial.natDegree_toPoly (f.val.coeff j)))

end CBivariate
end CompPoly
