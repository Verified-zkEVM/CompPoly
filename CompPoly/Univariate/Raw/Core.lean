/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas

/-!
# Raw Computable Univariate Polynomials

Core definitions for array-backed computable univariate polynomials.
-/

open Polynomial

namespace CompPoly

/-- A type analogous to `Polynomial` that supports computable operations. This is defined to be a
  wrapper around `Array`.

  For example, the Array `#[1,2,3]` represents the polynomial `1 + 2x + 3x^2`.
  Two arrays may represent the same polynomial via zero-padding,
  for example `#[1,2,3] = #[1,2,3,0,0,0,...]`.
-/
@[reducible, inline, specialize]
def CPolynomial.Raw (R : Type*) := Array R

namespace CPolynomial.Raw

/-- Construct a `CPolynomial.Raw` from an array of coefficients. -/
@[reducible]
def mk {R : Type*} (coeffs : Array R) : CPolynomial.Raw R := coeffs

/-- Extract the underlying array of coefficients. -/
@[reducible]
def coeffs {R : Type*} (p : CPolynomial.Raw R) : Array R := p

variable {R : Type*}
variable {Q : Type*}

section Foundations

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff [Zero R] (p : CPolynomial.Raw R) (i : ℕ) : R := p.getD i 0

/-- The constant polynomial `C r`. -/
def C (r : R) : CPolynomial.Raw R := #[r]

/-- The variable `X`. -/
def X [Zero R] [One R] : CPolynomial.Raw R := #[0, 1]

/-- Construct a monomial `c * X^n` as a `CPolynomial.Raw R`.

  The result is an array with `n` zeros followed by `c`.
  For example, `monomial 2 3` = `#[0, 0, 3]` represents `3 * X^2`.

  Note: If `c = 0`, this returns `#[]` (the zero polynomial).
-/
def monomial [Zero R] [DecidableEq R] (n : ℕ) (c : R) : CPolynomial.Raw R :=
  if c = 0 then #[] else .mk (Array.replicate n 0 ++ #[c])

/-- Return the index of the last non-zero coefficient of a `CPolynomial.Raw` -/
def lastNonzero [Zero R] [BEq R] (p : CPolynomial.Raw R) : Option (Fin p.size) :=
  p.findIdxRev? (· != 0)

/-- Remove trailing zeroes from a `CPolynomial.Raw`.
Requires `BEq` to check if the coefficients are zero. -/
def trim [Zero R] [BEq R] (p : CPolynomial.Raw R) : CPolynomial.Raw R :=
  match p.lastNonzero with
  | none => #[]
  | some i => p.extract 0 (i.val + 1)

/-- Return the degree of a `CPolynomial.Raw`. -/
def degree [Zero R] [BEq R] (p : CPolynomial.Raw R) : WithBot ℕ :=
  match p.lastNonzero with
  | none => ⊥
  | some i => i.val

/-- Natural number degree of a `CPolynomial.Raw`.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree [Zero R] [BEq R] (p : CPolynomial.Raw R) : ℕ :=
  match p.lastNonzero with
  | none => 0
  | some i => i.val

/-- Return the leading coefficient of a `CPolynomial.Raw` as the last coefficient
of the trimmed array, or `0` if the trimmed array is empty. -/
def leadingCoeff [Zero R] [BEq R] (p : CPolynomial.Raw R) : R := p.trim.getLastD 0

/-- Semantic canonicality for raw coefficient arrays: a polynomial is canonical iff its
last stored coefficient, when present, is nonzero. This invariant is independent of any
particular `BEq` instance. -/
def IsCanonical [Zero R] (p : CPolynomial.Raw R) : Prop :=
  ∀ hp : p.size > 0, p.getLast hp ≠ 0

/-- A polynomial is canonical if it has no trailing zeros, i.e. `p.trim = p`. -/
def canonical [Zero R] [BEq R] (p : CPolynomial.Raw R) : Prop := p.trim = p

/- Lemmas about trimming and canonical forms.
  Central results: `trim_twice`, `canonical_iff`, `eq_of_equiv`, `canonical_ext`. -/
namespace Trim

/-- If all coefficients are zero, `lastNonzero` is `none`. -/
theorem lastNonzero_none [Zero R] [BEq R] [LawfulBEq R] {p : CPolynomial.Raw R} :
    (∀ i, (hi : i < p.size) → p[i] = 0) → p.lastNonzero = none := by
  intro h
  apply Array.findIdxRev?_eq_none
  intros
  rw [bne_iff_ne, ne_eq, not_not]
  apply_assumption

/-- If there is a non-zero coefficient, `lastNonzero` is `some`. -/
theorem lastNonzero_some [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} {i} (hi : i < p.size)
    (h : p[i] ≠ 0) : ∃ k, p.lastNonzero = some k :=
  Array.findIdxRev?_eq_some ⟨i, hi, bne_iff_ne.mpr h⟩

/-- `lastNonzero` returns the largest index with a non-zero coefficient. -/
theorem lastNonzero_spec [Zero R] [BEq R] [LawfulBEq R] {p : CPolynomial.Raw R} {k} :
    p.lastNonzero = some k
  → p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0) := by
  intro (h : p.lastNonzero = some k)
  constructor
  · by_contra
    have h : p[k] != 0 := Array.findIdxRev?_def h
    rwa [‹p[k] = 0›, bne_self_eq_false, Bool.false_eq_true] at h
  · intro j hj j_gt_k
    have h : ¬(p[j] != 0) := Array.findIdxRev?_maximal h ⟨ j, hj ⟩ j_gt_k
    rwa [bne_iff_ne, ne_eq, not_not] at h

/-- The property that an index is the last non-zero coefficient. -/
def lastNonzeroProp [Zero R] {p : CPolynomial.Raw R} (k : Fin p.size) : Prop :=
  p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)

/-- The last non-zero index is unique. -/
lemma lastNonzero_unique [Zero Q] {p : CPolynomial.Raw Q} {k k' : Fin p.size} :
    lastNonzeroProp k → lastNonzeroProp k' → k = k' := by
  suffices weaker : ∀ k k', lastNonzeroProp k → lastNonzeroProp k' → k ≤ k' by
    intro h h'
    exact Fin.le_antisymm (weaker k k' h h') (weaker k' k h' h)
  intro k k' ⟨ h_nonzero, h ⟩ ⟨ h_nonzero', h' ⟩
  by_contra k_not_le
  have : p[k] = 0 := h' k k.is_lt (Nat.lt_of_not_ge k_not_le)
  contradiction

/-- Characterization of `lastNonzero` via `lastNonzeroProp`. -/
theorem lastNonzero_some_iff [Zero R] [BEq R] [LawfulBEq R] {p : CPolynomial.Raw R} {k} :
    p.lastNonzero = some k ↔ (p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)) := by
  constructor
  · apply lastNonzero_spec
  intro h_prop
  have ⟨ k', h_some'⟩ := lastNonzero_some k.is_lt h_prop.left
  have k_is_k' := lastNonzero_unique (lastNonzero_spec h_some') h_prop
  rwa [← k_is_k']

/-- eliminator for `p.lastNonzero`, e.g. use with the induction tactic as follows:
  ```
  induction p using lastNonzero_induct with
  | case1 p h_none h_all_zero => ...
  | case2 p k h_some h_nonzero h_max => ...
  ```
-/
theorem lastNonzero_induct [Zero R] [BEq R] [LawfulBEq R] {motive : CPolynomial.Raw R → Prop}
    (case1 : ∀ p, p.lastNonzero = none → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : CPolynomial.Raw R, ∀ k : Fin p.size, p.lastNonzero = some k → p[k] ≠ 0 →
    (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : CPolynomial.Raw R) : motive p := by
  by_cases h : ∀ i, (hi : i < p.size) → p[i] = 0
  · exact case1 p (lastNonzero_none h) h
  · push Not at h; rcases h with ⟨ i, hi, h ⟩
    obtain ⟨ k, h_some ⟩ := lastNonzero_some hi h
    have ⟨ h_nonzero, h_max ⟩ := lastNonzero_spec h_some
    exact case2 p k h_some h_nonzero h_max

/-- eliminator for `p.trim`; use with the induction tactic as follows:
  ```
  induction p using induct with
  | case1 p h_empty h_all_zero => ...
  | case2 p k h_extract h_nonzero h_max => ...
  ```
-/
theorem induct [Zero R] [BEq R] [LawfulBEq R] {motive : CPolynomial.Raw R → Prop}
    (case1 : ∀ p, p.trim = #[] → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : CPolynomial.Raw R, ∀ k : Fin p.size, p.trim = p.extract 0 (k + 1)
    → p[k] ≠ 0 → (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : CPolynomial.Raw R) : motive p := by induction p using lastNonzero_induct with
  | case1 p h_none h_all_zero =>
    have h_empty : p.trim = #[] := by unfold trim; rw [h_none]
    exact case1 p h_empty h_all_zero
  | case2 p k h_some h_nonzero h_max =>
    have h_extract : p.trim = p.extract 0 (k + 1) := by unfold trim; rw [h_some]
    exact case2 p k h_extract h_nonzero h_max

/-- eliminator for `p.trim`; e.g. use for case distinction as follows:
  ```
  rcases (Trim.elim p) with ⟨ h_empty, h_all_zero ⟩ | ⟨ k, h_extract, h_nonzero, h_max ⟩
  ```
-/
theorem elim [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    (p.trim = #[] ∧  (∀ i, (hi : i < p.size) → p[i] = 0))
    ∨ (∃ k : Fin p.size,
        p.trim = p.extract 0 (k + 1)
      ∧ p[k] ≠ 0
      ∧ (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0)) := by induction p using induct with
  | case1 p h_empty h_all_zero => left; exact ⟨h_empty, h_all_zero⟩
  | case2 p k h_extract h_nonzero h_max => right; exact ⟨k, h_extract, h_nonzero, h_max⟩

theorem size_eq_degree_plus_one [Zero R] [BEq R]
    (p : CPolynomial.Raw R) (h_trim : p.trim ≠ (mk #[])) :
    p.trim.size = p.degree + 1 := by
  unfold trim degree
  match h : p.lastNonzero with
  | none => exfalso; unfold trim at h_trim; rw [h] at h_trim; contradiction
  | some i => simp [Fin.is_lt]

theorem size_eq_natDegree_plus_one [Zero R] [BEq R]
    (p : CPolynomial.Raw R) (h_trim : p.trim ≠ (mk #[])) :
    p.trim.size = p.natDegree + 1 := by
  unfold trim natDegree
  match h : p.lastNonzero with
  | none => exfalso; unfold trim at h_trim; rw [h] at h_trim; contradiction
  | some i => simp [Fin.is_lt]

theorem size_eq_natDegree_of_zero [Zero R] [BEq R]
    (p : CPolynomial.Raw R) (h_trim : p.trim = (mk #[])) :
    p.trim.size = p.natDegree := by
  unfold trim natDegree
  match h : p.lastNonzero with
  | none => simp
  | some i => exfalso
              unfold trim at h_trim
              rw [h] at h_trim; have h_size := congrArg Array.size h_trim
              simp [Array.size_extract, Nat.succ_le_of_lt i.is_lt] at h_size

theorem size_le_size [Zero R] [BEq R] (p : CPolynomial.Raw R) : p.trim.size ≤ p.size := by
  unfold trim
  match h : p.lastNonzero with
  | none => simp
  | some i => simp [Array.size_extract]

attribute [simp] Array.getElem?_eq_none

theorem coeff_eq_getElem_of_lt [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} {i} (hi : i < p.size) :
    p.trim.coeff i = p[i] := by
  induction p using induct with
  | case1 p h_empty h_all_zero =>
    specialize h_all_zero i hi
    simp [h_empty, h_all_zero]
  | case2 p k h_extract h_nonzero h_max =>
    simp [h_extract]
    have h_size : k + 1 = (p.extract 0 (k + 1)).size := by
      simp [Array.size_extract]
    rcases (Nat.lt_or_ge k i) with hik | hik
    · have hik' : i ≥ (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_none hik', Option.getD_none]
      exact h_max i hi hik |> Eq.symm
    · have hik' : i < (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_getElem hik', Option.getD_some, Array.getElem_extract]
      simp only [zero_add]

theorem coeff_eq_coeff [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial.Raw R) (i : ℕ) :
    p.trim.coeff i = p.coeff i := by
  rcases (Nat.lt_or_ge i p.size) with hi | hi
  · rw [coeff_eq_getElem_of_lt hi]
    simp [hi]
  · have hi' : i ≥ p.trim.size := by linarith [size_le_size p]
    simp [hi, hi']

lemma coeff_eq_getElem [Zero Q] {p : CPolynomial.Raw Q} {i} (hp : i < p.size) :
    p.coeff i = p[i] := by
  simp [hp]

/-- Equivalence relation: two polynomials are equivalent if all coefficients agree. -/
def equiv [Zero R] (p q : CPolynomial.Raw R) : Prop :=
  ∀ i, p.coeff i = q.coeff i

lemma coeff_eq_zero [Zero Q] {p : CPolynomial.Raw Q} :
    (∀ i, (hi : i < p.size) → p[i] = 0) ↔ ∀ i, p.coeff i = 0 := by
  constructor <;> intro h i
  · cases Nat.lt_or_ge i p.size <;> simp [*]
  · intro hi; specialize h i; simp [hi] at h; assumption

lemma eq_degree_of_equiv [Zero R] [BEq R] [LawfulBEq R] {p q : CPolynomial.Raw R} :
    equiv p q → p.degree = q.degree := by
  unfold equiv degree
  intro h_equiv
  induction p using lastNonzero_induct with
  | case1 p h_none_p h_all_zero =>
    have h_zero_p : ∀ i, p.coeff i = 0 := coeff_eq_zero.mp h_all_zero
    have h_zero_q : ∀ i, q.coeff i = 0 := by intro i; rw [← h_equiv, h_zero_p]
    have h_none_q : q.lastNonzero = none := lastNonzero_none (coeff_eq_zero.mpr h_zero_q)
    rw [h_none_p, h_none_q]
  | case2 p k h_some_p h_nonzero_p h_max_p =>
    have h_equiv_k := h_equiv k
    have k_lt_q : k < q.size := by
      by_contra h_not_lt
      have h_ge := Nat.le_of_not_lt h_not_lt
      simp [h_ge] at h_equiv_k
      contradiction
    simp [k_lt_q] at h_equiv_k
    have h_nonzero_q : q[k.val] ≠ 0 := by rwa [← h_equiv_k]
    have h_max_q : ∀ j, (hj : j < q.size) → j > k → q[j] = 0 := by
      intro j hj j_gt_k
      have h_eq := h_equiv j
      simp [hj] at h_eq
      rw [← h_eq]
      rcases Nat.lt_or_ge j p.size with hj | hj
      · simp [hj, h_max_p j hj j_gt_k]
      · simp [hj]
    have h_some_q : q.lastNonzero = some ⟨ k, k_lt_q ⟩ :=
      lastNonzero_some_iff.mpr ⟨ h_nonzero_q, h_max_q ⟩
    rw [h_some_p, h_some_q]

theorem eq_of_equiv [Zero R] [BEq R] [LawfulBEq R] {p q : CPolynomial.Raw R} :
    equiv p q → p.trim = q.trim := by
  unfold equiv
  intro h
  ext
  · have h_deg := eq_degree_of_equiv h
    unfold trim
    cases hp : p.lastNonzero with
    | none =>
      cases hq : q.lastNonzero with
      | none => rfl
      | some j => unfold degree at h_deg; simp [hp, hq] at h_deg
    | some i =>
      cases hq : q.lastNonzero with
      | none => unfold degree at h_deg; simp [hp, hq] at h_deg
      | some j =>
        unfold degree at h_deg
        simp only [hp, hq] at h_deg
        simp [Array.size_extract, Nat.succ_le_of_lt i.is_lt, Nat.succ_le_of_lt j.is_lt]
        exact_mod_cast h_deg
  · rw [← coeff_eq_getElem, ← coeff_eq_getElem]
    rw [coeff_eq_coeff, coeff_eq_coeff, h _]

theorem trim_equiv [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    equiv p.trim p := by
  apply coeff_eq_coeff

theorem trim_twice [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial.Raw R) :
    p.trim.trim = p.trim := by
  apply eq_of_equiv
  apply trim_equiv

theorem canonical_empty [Zero R] [BEq R] : (mk (R := R) #[]).trim = #[] := by
  have : (mk (R:=R) #[]).lastNonzero = none := by
    simp [lastNonzero]
    apply Array.findIdxRev?_empty_none
    rfl
  rw [trim, this]

theorem canonical_of_size_zero [Zero R] [BEq R] {p : CPolynomial.Raw R} :
    p.size = 0 → p.trim = p := by
  intro h
  suffices h_empty : p = #[] by rw [h_empty]; exact canonical_empty
  exact Array.eq_empty_of_size_eq_zero h

theorem canonical_nonempty_iff [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} (hp : p.size > 0) :
    p.trim = p ↔ p.lastNonzero = some ⟨ p.size - 1, Nat.pred_lt_self hp ⟩ := by
  unfold trim
  induction p using lastNonzero_induct with
  | case1 p h_none h_all_zero =>
    simp [h_none]
    by_contra h_empty
    subst h_empty
    contradiction
  | case2 p k h_some h_nonzero h_max =>
    simp [h_some]
    constructor
    · intro h
      ext
      have : p ≠ #[] := Array.ne_empty_of_size_pos hp
      simp [this] at h
      have : k + 1 ≤ p.size := Nat.succ_le_of_lt k.is_lt
      have : p.size = k + 1 := Nat.le_antisymm h this
      simp [this]
    · intro h
      have : k + 1 = p.size := by rw [h]; exact Nat.succ_pred_eq_of_pos hp
      rw [this]
      right
      exact le_refl _

theorem lastNonzero_last_iff [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} (hp : p.size > 0) :
    p.lastNonzero = some ⟨ p.size - 1, Nat.pred_lt_self hp ⟩ ↔ p.getLast hp ≠ 0 := by
  induction p using lastNonzero_induct with
  | case1 => simp [Array.getLast, *]
  | case2 p k h_some h_nonzero h_max =>
    simp only [h_some, Option.some_inj, Array.getLast]
    constructor
    · intro h
      have : k = p.size - 1 := by rw [h]
      conv => lhs; congr; case i => rw [← this]
      assumption
    · intro h
      rcases Nat.lt_trichotomy k (p.size - 1) with h_lt | h_eq | h_gt
      · specialize h_max (p.size - 1) (Nat.pred_lt_self hp) h_lt
        contradiction
      · ext; assumption
      · have : k < p.size := k.is_lt
        have : k ≥ p.size := Nat.le_of_pred_lt h_gt
        linarith

theorem canonical_iff [Zero R] [BEq R] [LawfulBEq R] {p : CPolynomial.Raw R} :
    p.trim = p ↔ IsCanonical p := by
  constructor
  · intro h hp
    rwa [← lastNonzero_last_iff hp, ← canonical_nonempty_iff hp]
  · rintro h
    rcases Nat.eq_zero_or_pos p.size with h_zero | hp
    · exact canonical_of_size_zero h_zero
    · rw [canonical_nonempty_iff hp, lastNonzero_last_iff hp]
      exact h hp

theorem isCanonical_empty [Zero R] : IsCanonical (mk (R := R) #[]) := by
  intro hp
  simp at hp

theorem isCanonical_of_size_zero [Zero R] {p : CPolynomial.Raw R} (hp : p.size = 0) :
    IsCanonical p := by
  intro hPos
  simp [hp] at hPos

/-- Canonicality bridge (semantic view to computational view). -/
theorem isCanonical_iff_trim_eq [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} :
    IsCanonical p ↔ p.trim = p :=
  canonical_iff.symm

/-- Non-dependent canonicality criterion using `getLastD`. -/
theorem isCanonical_iff_size_eq_zero_or_getLastD_ne_zero [Zero R]
    {p : CPolynomial.Raw R} :
    IsCanonical p ↔ p.size = 0 ∨ p.getLastD 0 ≠ 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos p.size with h0 | hp
    · exact Or.inl h0
    · exact Or.inr (by simpa [Array.getLastD, hp] using h hp)
  · intro h hp
    rcases h with h0 | hlast
    · exact (Nat.ne_of_gt hp h0).elim
    · simpa [Array.getLastD, hp] using hlast

/-- Computational canonicality criterion in non-dependent form. -/
theorem trim_eq_iff_size_eq_zero_or_getLastD_ne_zero [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} :
    p.trim = p ↔ p.size = 0 ∨ p.getLastD 0 ≠ 0 := by
  rw [canonical_iff, isCanonical_iff_size_eq_zero_or_getLastD_ne_zero]

theorem trim_eq_of_isCanonical [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} (hp : IsCanonical p) :
    p.trim = p :=
  canonical_iff.mpr hp

theorem isCanonical_of_trim_eq [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial.Raw R} (hp : p.trim = p) :
    IsCanonical p :=
  canonical_iff.mp hp

theorem isCanonical_trim [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial.Raw R) : IsCanonical p.trim :=
  isCanonical_of_trim_eq (trim_twice p)

@[grind =]
lemma push_trim [Zero R] [BEq R] [LawfulBEq R] (arr : Array R) (c : R) :
    ¬c = 0 → trim (arr.push c) = arr.push c := by
  rw [Trim.canonical_iff]
  intros h_c hp
  simp [Array.getLast]
  exact h_c

theorem non_zero_map [Zero R] [BEq R] [LawfulBEq R]
    (f : R → R) (hf : ∀ r, f r = 0 → r = 0) (p : CPolynomial.Raw R) :
    let fp := mk (p.map f);
  p.trim = p → fp.trim = fp := by
  intro fp p_canon
  by_cases hp : p.size > 0
  · apply canonical_iff.mpr
    intro hfp
    have h_nonzero := canonical_iff.mp p_canon hp
    have : fp.getLast hfp = f (p.getLast hp) := by simp [Array.getLast, fp]
    rw [this]
    by_contra h_zero
    specialize hf (p.getLast hp) h_zero
    contradiction
  have : p.size = 0 := by linarith
  have : fp.size = 0 := by simp [this, fp]
  apply canonical_of_size_zero this

/-- Canonical polynomials enjoy a stronger extensionality theorem:
  they just need to agree at all coefficients (without assuming equal sizes)
-/
theorem canonical_ext [Zero R] [BEq R] [LawfulBEq R]
    {p q : CPolynomial.Raw R} (hp : p.trim = p) (hq : q.trim = q) :
    equiv p q → p = q := by
  intro h_equiv
  rw [← hp, ← hq]
  exact eq_of_equiv h_equiv

theorem isCanonical_ext [Zero R] [BEq R] [LawfulBEq R] {p q : CPolynomial.Raw R}
    (hp : IsCanonical p) (hq : IsCanonical q) :
    equiv p q → p = q := by
  exact canonical_ext (trim_eq_of_isCanonical hp) (trim_eq_of_isCanonical hq)

end Trim

end Foundations

end CPolynomial.Raw

end CompPoly
