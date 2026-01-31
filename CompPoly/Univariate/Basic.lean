/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas

/-!
  # Computable Univariate Polynomials

  This file contains a computable datatype for univariate polynomial, `CPolynomial R`. This is
  internally represented as an array of coefficients.

  Note: this has been ported from ArkLib
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
def CPolynomial (R : Type*) := Array R

namespace CPolynomial

/-- Construct a `CPolynomial` from an array of coefficients. -/
@[reducible]
def mk {R : Type*} (coeffs : Array R) : CPolynomial R := coeffs

/-- Extract the underlying array of coefficients. -/
@[reducible]
def coeffs {R : Type*} (p : CPolynomial R) : Array R := p

variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff (p : CPolynomial Q) (i : ℕ) : Q := p.getD i 0

/-- The constant polynomial `C r`. -/
def C (r : R) : CPolynomial R := #[r]

/-- The variable `X`. -/
def X : CPolynomial R := #[0, 1]

/-- Construct a monomial `c * X^n` as a `CPolynomial R`.

  The result is an array with `n` zeros followed by `c`.
  For example, `monomial 2 3` = `#[0, 0, 3]` represents `3 * X^2`.

  Note: If `c = 0`, this returns `#[]` (the zero polynomial).
-/
def monomial [DecidableEq R] (n : ℕ) (c : R) : CPolynomial R :=
  if c = 0 then #[] else .mk (Array.replicate n 0 ++ #[c])

-- TODO: Prove basic properties of `monomial`, e.g.
-- TODO: `coeff (monomial n c) i = if i = n then c else 0`
-- TODO: `monomial n 0 = 0`
-- TODO: `monomial 0 c = C c`
-- TODO: `monomial n 1 = X^n` (where `X^n` is `X.pow n`)
-- TODO: `monomial n c = C c * X^n` (multiplicative property)
-- TODO: `monomial n c + monomial n d = monomial n (c + d)` (additive property)
-- TODO: `monomial m c * monomial n d = monomial (m + n) (c * d)` (multiplicative property)
-- TODO: `trim (monomial n c) = if c = 0 then #[] else monomial n c` (canonical property)

/-- Return the index of the last non-zero coefficient of a `CPolynomial` -/
def lastNonzero (p : CPolynomial R) : Option (Fin p.size) :=
  p.findIdxRev? (· != 0)

/-- Remove leading zeroes from a `CPolynomial`.
Requires `BEq` to check if the coefficients are zero. -/
def trim (p : CPolynomial R) : CPolynomial R :=
  match p.lastNonzero with
  | none => #[]
  | some i => p.extract 0 (i.val + 1)

/-- Return the degree of a `CPolynomial`. -/
def degree (p : CPolynomial R) : Nat :=
  match p.lastNonzero with
  | none => 0
  | some i => i.val + 1

/-- Natural number degree of a `CPolynomial`.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree (p : CPolynomial R) : ℕ :=
  sorry

/-- Return the leading coefficient of a `CPolynomial` as the last coefficient of the trimmed array,
or `0` if the trimmed array is empty. -/
def leadingCoeff (p : CPolynomial R) : R := p.trim.getLastD 0

namespace Trim

/-- If all coefficients are zero, `lastNonzero` is `none`. -/
theorem lastNonzero_none [LawfulBEq R] {p : CPolynomial R} :
    (∀ i, (hi : i < p.size) → p[i] = 0) → p.lastNonzero = none := by
  intro h
  apply Array.findIdxRev?_eq_none
  intros
  rw [bne_iff_ne, ne_eq, not_not]
  apply_assumption

/-- If there is a non-zero coefficient, `lastNonzero` is `some`. -/
theorem lastNonzero_some [LawfulBEq R] {p : CPolynomial R} {i} (hi : i < p.size) (h : p[i] ≠ 0) :
    ∃ k, p.lastNonzero = some k := Array.findIdxRev?_eq_some ⟨i, hi, bne_iff_ne.mpr h⟩

/-- `lastNonzero` returns the largest index with a non-zero coefficient. -/
theorem lastNonzero_spec [LawfulBEq R] {p : CPolynomial R} {k} :
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
def lastNonzeroProp {p : CPolynomial R} (k : Fin p.size) : Prop :=
  p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)

/-- The last non-zero index is unique. -/
lemma lastNonzero_unique {p : CPolynomial Q} {k k' : Fin p.size} :
    lastNonzeroProp k → lastNonzeroProp k' → k = k' := by
  suffices weaker : ∀ k k', lastNonzeroProp k → lastNonzeroProp k' → k ≤ k' by
    intro h h'
    exact Fin.le_antisymm (weaker k k' h h') (weaker k' k h' h)
  intro k k' ⟨ h_nonzero, h ⟩ ⟨ h_nonzero', h' ⟩
  by_contra k_not_le
  have : p[k] = 0 := h' k k.is_lt (Nat.lt_of_not_ge k_not_le)
  contradiction

/-- Characterization of `lastNonzero` via `lastNonzeroProp`. -/
theorem lastNonzero_some_iff [LawfulBEq R] {p : CPolynomial R} {k} :
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
theorem lastNonzero_induct [LawfulBEq R] {motive : CPolynomial R → Prop}
    (case1 : ∀ p, p.lastNonzero = none → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : CPolynomial R, ∀ k : Fin p.size, p.lastNonzero = some k → p[k] ≠ 0 →
    (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : CPolynomial R) : motive p := by
  by_cases h : ∀ i, (hi : i < p.size) → p[i] = 0
  · exact case1 p (lastNonzero_none h) h
  · push_neg at h; rcases h with ⟨ i, hi, h ⟩
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
theorem induct [LawfulBEq R] {motive : CPolynomial R → Prop}
    (case1 : ∀ p, p.trim = #[] → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : CPolynomial R, ∀ k : Fin p.size, p.trim = p.extract 0 (k + 1)
    → p[k] ≠ 0 → (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : CPolynomial R) : motive p := by induction p using lastNonzero_induct with
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
theorem elim [LawfulBEq R] (p : CPolynomial R) :
    (p.trim = #[] ∧  (∀ i, (hi : i < p.size) → p[i] = 0))
    ∨ (∃ k : Fin p.size,
        p.trim = p.extract 0 (k + 1)
      ∧ p[k] ≠ 0
      ∧ (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0)) := by induction p using induct with
  | case1 p h_empty h_all_zero => left; exact ⟨h_empty, h_all_zero⟩
  | case2 p k h_extract h_nonzero h_max => right; exact ⟨k, h_extract, h_nonzero, h_max⟩

theorem size_eq_degree (p : CPolynomial R) : p.trim.size = p.degree := by
  unfold trim degree
  match h : p.lastNonzero with
  | none => simp
  | some i => simp [Fin.is_lt, Nat.succ_le_of_lt]

theorem size_le_size (p : CPolynomial R) : p.trim.size ≤ p.size := by
  unfold trim
  match h : p.lastNonzero with
  | none => simp
  | some i => simp [Array.size_extract]

attribute [simp] Array.getElem?_eq_none

theorem coeff_eq_getElem_of_lt [LawfulBEq R] {p : CPolynomial R} {i} (hi : i < p.size) :
    p.trim.coeff i = p[i] := by
  induction p using induct with
  | case1 p h_empty h_all_zero =>
    specialize h_all_zero i hi
    simp [h_empty, h_all_zero]
  | case2 p k h_extract h_nonzero h_max =>
    simp [h_extract]
    -- split between i > k and i <= k
    have h_size : k + 1 = (p.extract 0 (k + 1)).size := by
      simp [Array.size_extract]
      exact Nat.succ_le_of_lt k.is_lt
    rcases (Nat.lt_or_ge k i) with hik | hik
    · have hik' : i ≥ (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_none hik', Option.getD_none]
      exact h_max i hi hik |> Eq.symm
    · have hik' : i < (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_getElem hik', Option.getD_some, Array.getElem_extract]
      simp only [zero_add]

theorem coeff_eq_coeff [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    p.trim.coeff i = p.coeff i := by
  rcases (Nat.lt_or_ge i p.size) with hi | hi
  · rw [coeff_eq_getElem_of_lt hi]
    simp [hi]
  · have hi' : i ≥ p.trim.size := by linarith [size_le_size p]
    simp [hi, hi']

lemma coeff_eq_getElem {p : CPolynomial Q} {i} (hp : i < p.size) :
    p.coeff i = p[i] := by
  simp [hp]

/-- Equivalence relation: two polynomials are equivalent if all coefficients agree. -/
def equiv (p q : CPolynomial R) : Prop :=
  ∀ i, p.coeff i = q.coeff i

lemma coeff_eq_zero {p : CPolynomial Q} :
    (∀ i, (hi : i < p.size) → p[i] = 0) ↔ ∀ i, p.coeff i = 0 := by
  constructor <;> intro h i
  · cases Nat.lt_or_ge i p.size <;> simp [*]
  · intro hi; specialize h i; simp [hi] at h; assumption

lemma eq_degree_of_equiv [LawfulBEq R] {p q : CPolynomial R} :
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

theorem eq_of_equiv [LawfulBEq R] {p q : CPolynomial R} : equiv p q → p.trim = q.trim := by
  unfold equiv
  intro h
  ext
  · rw [size_eq_degree, size_eq_degree]
    apply eq_degree_of_equiv h
  rw [← coeff_eq_getElem, ← coeff_eq_getElem]
  rw [coeff_eq_coeff, coeff_eq_coeff, h _]

theorem trim_equiv [LawfulBEq R] (p : CPolynomial R) : equiv p.trim p := by
  apply coeff_eq_coeff

theorem trim_twice [LawfulBEq R] (p : CPolynomial R) : p.trim.trim = p.trim := by
  apply eq_of_equiv
  apply trim_equiv

theorem canonical_empty : (CPolynomial.mk (R:=R) #[]).trim = #[] := by
  have : (CPolynomial.mk (R:=R) #[]).lastNonzero = none := by
    simp [lastNonzero]
    apply Array.findIdxRev?_empty_none
    rfl
  rw [trim, this]

theorem canonical_of_size_zero {p : CPolynomial R} : p.size = 0 → p.trim = p := by
  intro h
  suffices h_empty : p = #[] by rw [h_empty]; exact canonical_empty
  exact Array.eq_empty_of_size_eq_zero h

theorem canonical_nonempty_iff [LawfulBEq R] {p : CPolynomial R} (hp : p.size > 0) :
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

theorem lastNonzero_last_iff [LawfulBEq R] {p : CPolynomial R} (hp : p.size > 0) :
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

theorem canonical_iff [LawfulBEq R] {p : CPolynomial R} :
    p.trim = p ↔ ∀ hp : p.size > 0, p.getLast hp ≠ 0 := by
  constructor
  · intro h hp
    rwa [← lastNonzero_last_iff hp, ← canonical_nonempty_iff hp]
  · rintro h
    rcases Nat.eq_zero_or_pos p.size with h_zero | hp
    · exact canonical_of_size_zero h_zero
    · rw [canonical_nonempty_iff hp, lastNonzero_last_iff hp]
      exact h hp

theorem non_zero_map [LawfulBEq R] (f : R → R) (hf : ∀ r, f r = 0 → r = 0) (p : CPolynomial R) :
    let fp := CPolynomial.mk (p.map f);
  p.trim = p → fp.trim = fp := by
  intro fp p_canon
  by_cases hp : p.size > 0
  -- positive case
  · apply canonical_iff.mpr
    intro hfp
    have h_nonzero := canonical_iff.mp p_canon hp
    have : fp.getLast hfp = f (p.getLast hp) := by simp [Array.getLast, fp]
    rw [this]
    by_contra h_zero
    specialize hf (p.getLast hp) h_zero
    contradiction
  -- zero case
  have : p.size = 0 := by linarith
  have : fp.size = 0 := by simp [this, fp]
  apply canonical_of_size_zero this

/-- Canonical polynomials enjoy a stronger extensionality theorem:
  they just need to agree at all coefficients (without assuming equal sizes)
-/
theorem canonical_ext [LawfulBEq R] {p q : CPolynomial R} (hp : p.trim = p) (hq : q.trim = q) :
    equiv p q → p = q := by
  intro h_equiv
  rw [← hp, ← hq]
  exact eq_of_equiv h_equiv
end Trim

section Operations

variable {S : Type*}

-- p(x) = a_0 + a_1 x + a_2 x^2 + ... + a_n x^n

-- eval₂ f x p = f(a_0) + f(a_1) x + f(a_2) x^2 + ... + f(a_n) x^n

/-- Evaluates a `CPolynomial` at `x : S` using a ring homomorphism `f : R →+* S`.

  Computes `f(a₀) + f(a₁) * x + f(a₂) * x² + ...` where `aᵢ` are the coefficients.

  TODO: define an efficient version of this with caching -/
def eval₂ [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial R) : S :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `CPolynomial` at a given value -/
@[inline, specialize]
def eval (x : R) (p : CPolynomial R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Raw addition: pointwise sum of coefficient arrays (padded to equal length).

  The result may have trailing zeros and should be trimmed for canonical form. -/
@[inline, specialize]
def addRaw (p q : CPolynomial R) : CPolynomial R :=
  let ⟨p', q'⟩ := Array.matchSize p q 0
  .mk (Array.zipWith (· + ·) p' q' )

/-- Addition of two `CPolynomial`s, with result trimmed. -/
@[inline, specialize]
def add (p q : CPolynomial R) : CPolynomial R :=
  addRaw p q |> trim

/-- Scalar multiplication: multiplies each coefficient by `r`. -/
@[inline, specialize]
def smul (r : R) (p : CPolynomial R) : CPolynomial R :=
  .mk (Array.map (fun a => r * a) p)

/-- Raw scalar multiplication by a natural number (may have trailing zeros). -/
@[inline, specialize]
def nsmulRaw (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  .mk (Array.map (fun a => n * a) p)

/-- Scalar multiplication of `CPolynomial` by a natural number, with result trimmed. -/
@[inline, specialize]
def nsmul (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  nsmulRaw n p |> trim

/-- Negation of a `CPolynomial`. -/
@[inline, specialize]
def neg (p : CPolynomial R) : CPolynomial R := p.map (fun a => -a)

/-- Subtraction of two `CPolynomial`s. -/
@[inline, specialize]
def sub (p q : CPolynomial R) : CPolynomial R := p.add q.neg

/-- Multiplication by `X^i`: shifts coefficients right by `i` positions (prepends `i` zeros). -/
@[inline, specialize]
def mulPowX (i : Nat) (p : CPolynomial R) : CPolynomial R := .mk (Array.replicate i 0 ++ p)

/-- Multiplication of a `CPolynomial` by `X`, reduces to `mulPowX 1`. -/
@[inline, specialize]
def mulX (p : CPolynomial R) : CPolynomial R := p.mulPowX 1

/-- Multiplication using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`. -/
@[inline, specialize]
def mul (p q : CPolynomial R) : CPolynomial R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (mk #[])

/-- Exponentiation of a `CPolynomial` by a natural number `n` via repeated multiplication. -/
@[inline, specialize]
def pow (p : CPolynomial R) (n : Nat) : CPolynomial R := (mul p)^[n] (C 1)

-- TODO: define repeated squaring version of `pow`

instance : Zero (CPolynomial R) := ⟨#[]⟩
instance : One (CPolynomial R) := ⟨CPolynomial.C 1⟩
instance : Add (CPolynomial R) := ⟨CPolynomial.add⟩
instance : SMul R (CPolynomial R) := ⟨CPolynomial.smul⟩
instance : SMul ℕ (CPolynomial R) := ⟨nsmul⟩
instance : Neg (CPolynomial R) := ⟨CPolynomial.neg⟩
instance : Sub (CPolynomial R) := ⟨CPolynomial.sub⟩
instance : Mul (CPolynomial R) := ⟨CPolynomial.mul⟩
instance : Pow (CPolynomial R) Nat := ⟨CPolynomial.pow⟩
instance : NatCast (CPolynomial R) := ⟨fun n => CPolynomial.C (n : R)⟩
instance : IntCast (CPolynomial R) := ⟨fun n => CPolynomial.C (n : R)⟩

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound (p : CPolynomial R) : WithBot Nat :=
  match p.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : CPolynomial R) : Nat :=
  (degreeBound p).getD 0

/-- Check if a `CPolynomial` is monic, i.e. its leading coefficient is 1. -/
def monic (p : CPolynomial R) : Bool := p.leadingCoeff == 1

/-- Division with remainder by a monic polynomial using polynomial long division. -/
def divModByMonicAux [Field R] (p : CPolynomial R) (q : CPolynomial R) :
    CPolynomial R × CPolynomial R :=
  go (p.size - q.size) p q
where
  go : Nat → CPolynomial R → CPolynomial R → CPolynomial R × CPolynomial R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      let k := p.size - q.size -- k should equal n, this is technically unneeded
      let q' := C p.leadingCoeff * (q * X.pow k)
      let p' := (p - q').trim
      let (e, f) := go n p' q
      -- p' = q * e + f
      -- Thus p = p' + q' = q * e + f + p.leadingCoeff * q * X^n
      -- = q * (e + p.leadingCoeff * X^n) + f
      ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : CPolynomial R` by a monic `q : CPolynomial R`. -/
def divByMonic [Field R] (p : CPolynomial R) (q : CPolynomial R) :
    CPolynomial R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : CPolynomial R` by a monic `q : CPolynomial R`. -/
def modByMonic [Field R] (p : CPolynomial R) (q : CPolynomial R) :
    CPolynomial R :=
  (divModByMonicAux p q).2

/-- Division of two `CPolynomial`s. -/
def div [Field R] (p q : CPolynomial R) : CPolynomial R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `CPolynomial`s. -/
def mod [Field R] (p q : CPolynomial R) : CPolynomial R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (CPolynomial R) := ⟨div⟩
instance [Field R] : Mod (CPolynomial R) := ⟨mod⟩

/-- Pseudo-division by `X`: removes the constant term and shifts remaining coefficients left. -/
def divX (p : CPolynomial R) : CPolynomial R := p.extract 1 p.size

variable (p q r : CPolynomial R)

-- some helper lemmas to characterize p + q

lemma matchSize_size_eq {p q : CPolynomial Q} :
    let (p', q') := Array.matchSize p q 0
    p'.size = q'.size := by
  change (Array.rightpad _ _ _).size = (Array.rightpad _ _ _).size
  rw [Array.size_rightpad, Array.size_rightpad]
  omega

lemma matchSize_size {p q : CPolynomial Q} :
    let (p', _) := Array.matchSize p q 0
    p'.size = max p.size q.size := by
  change (Array.rightpad _ _ _).size = max (Array.size _) (Array.size _)
  rw [Array.size_rightpad]
  omega

lemma zipWith_size {R} {f : R → R → R} {a b : Array R} (h : a.size = b.size) :
    (Array.zipWith f a b).size = a.size := by
  simp; omega


-- TODO we could generalize the next few lemmas to matchSize + zipWith f for any f

theorem add_size {p q : CPolynomial Q} : (addRaw p q).size = max p.size q.size := by
  change (Array.zipWith _ _ _ ).size = max p.size q.size
  rw [zipWith_size matchSize_size_eq, matchSize_size]

-- coeff on list concatenations
omit [BEq R] in
lemma concat_coeff₁ (i : ℕ) : i < p.size →
    (p ++ q).coeff i = p.coeff i := by simp; grind

omit [BEq R] in
lemma concat_coeff₂ (i : ℕ) : i ≥ p.size →
    (p ++ q).coeff i = q.coeff (i - p.size) := by simp; grind

theorem add_coeff {p q : CPolynomial Q} {i : ℕ} (hi : i < (addRaw p q).size) :
    (addRaw p q)[i] = p.coeff i + q.coeff i := by
  simp [addRaw]
  by_cases hi' : i < p.size <;> by_cases hi'' : i < q.size <;> simp_all

theorem add_coeff? (p q : CPolynomial Q) (i : ℕ) :
    (addRaw p q).coeff i = p.coeff i + q.coeff i := by
  rcases (Nat.lt_or_ge i (addRaw p q).size) with h_lt | h_ge
  · rw [← add_coeff h_lt]; simp [h_lt]
  have h_lt' : i ≥ max p.size q.size := by rwa [← add_size]
  have h_p : i ≥ p.size := by omega
  have h_q : i ≥ q.size := by omega
  simp [h_ge, h_p, h_q]

lemma add_coeff_trimmed [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p + q).coeff i = p.coeff i + q.coeff i := by
      have h_add : p + q = (p.addRaw q).trim := by rfl
      have h_trim_coeff : ∀ (p : CPolynomial R) (i : ℕ), p.coeff i = p.trim.coeff i := by
          exact fun p i => Eq.symm (Trim.coeff_eq_coeff p i)
      convert h_trim_coeff ( p.addRaw q ) i using 1
      · rw[h_add, ←h_trim_coeff]
      · rw [← h_trim_coeff, add_coeff? ]

lemma add_equiv_raw [LawfulBEq R] (p q : CPolynomial R) :
    Trim.equiv (p.add q) (p.addRaw q) := by
  unfold Trim.equiv add
  exact Trim.coeff_eq_coeff (p.addRaw q)

omit [BEq R] in
lemma smul_equiv : ∀ (i : ℕ) (r : R),
    (smul r p).coeff i = r * (p.coeff i) := by
  intro i r
  unfold smul mk coeff
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma nsmulRaw_equiv [LawfulBEq R] : ∀ (n i : ℕ),
    (nsmulRaw n p).trim.coeff i = n * p.trim.coeff i := by
  intro n i
  unfold nsmulRaw
  repeat rw [Trim.coeff_eq_coeff]
  unfold mk
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma mul_pow_assoc : ∀ (p : CPolynomial R) (n : ℕ),
    ∀ (q : CPolynomial R) (m l : ℕ),
  l + m = n →
  p.mul^[n] q = p.mul^[m] (p.mul^[l] q) := by
  intro p n
  induction n with
  | zero =>
    intro q m l h_sizes
    rw [Nat.add_eq_zero_iff] at h_sizes
    obtain ⟨hl, hm⟩ := h_sizes
    rw [hl, hm]
    simp

  | succ n₀ ih =>
    intro q m l h_sizes
    cases l with
    | zero =>
      simp at h_sizes
      rw [h_sizes]
      simp

    | succ l₀ =>
      have h_sizes_simp : l₀ + m = n₀ := by linarith
      clear h_sizes
      simp

      rw [ih (p.mul q) m l₀ h_sizes_simp]

lemma mul_pow_succ (p q : CPolynomial R) (n : ℕ):
    p.mul^[n + 1] q = p.mul (p.mul^[n] q) := by
  rw [mul_pow_assoc p (n+1) q 1 n] <;> simp

omit [BEq R] in
lemma neg_coeff : ∀ (p : CPolynomial R) (i : ℕ), p.neg.coeff i = - p.coeff i := by
  intro p i
  unfold neg coeff
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma trim_add_trim [LawfulBEq R] (p q : CPolynomial R) : p.trim + q = p + q := by
  apply Trim.eq_of_equiv
  intro i
  rw [add_coeff?, add_coeff?, Trim.coeff_eq_coeff]

/-
CPolynomial does in general form a Ring or any other 'nice' structure,
but many properties necessary to be a ring are satisfied or close to satisifed,
as per the following theorems.
-/

-- Algebra theorems about addition.

omit [Ring Q] in
@[simp] theorem zero_def : (0 : CPolynomial Q) = #[] := rfl

theorem add_comm : p + q = q + p := by
  apply congrArg trim
  ext
  · simp only [add_size]; omega
  · simp only [add_coeff]
    apply _root_.add_comm

/-- A polynomial is canonical if it has no trailing zeros. -/
def canonical (p : CPolynomial R) := p.trim = p

theorem zero_canonical : (0 : CPolynomial R).trim = 0 := Trim.canonical_empty

theorem zero_add (hp : p.canonical) : 0 + p = p := by
  rw (occs := .pos [2]) [← hp]
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_zero (hp : p.canonical) : p + 0 = p := by
  rw [add_comm, zero_add p hp]

theorem zero_add_trim [LawfulBEq R] (p : CPolynomial R) : 0 + p = p.trim := by
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_zero_trim [LawfulBEq R] (p : CPolynomial R) : p + 0 = p.trim := by
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_assoc [LawfulBEq R] : p + q + r = p + (q + r) := by
  change (addRaw p q).trim + r = p + (addRaw q r).trim
  rw [trim_add_trim, add_comm p, trim_add_trim, add_comm _ p]
  apply congrArg trim
  ext i
  · simp only [add_size]; omega
  · simp only [add_coeff, add_coeff?]
    apply _root_.add_assoc

-- Lemmas about sums for proving facts about multiplication.

/-- Helper lemma for proving: mul_one_trim.
If the initial value is canonical and the step function preserves canonicality,
then `foldl` preserves canonicality.
-/
lemma foldl_preserves_canonical {α : Type*}
    (f : CPolynomial R → α → CPolynomial R)
    (z : CPolynomial R) (as : Array α)
    (hz : z.trim = z)
    (hf : ∀ acc x, (f acc x).trim = f acc x) :
    (as.foldl f z).trim = as.foldl f z := by
      induction' as using Array.recOn with a as ih
      induction a using List.reverseRecOn <;> aesop

/-- Helper lemma for proving: mul_one_trim
The coefficient of a sum (via foldl) is the sum of the coefficients. -/
lemma coeff_foldl_add [LawfulBEq R]
    (l : List α)
    (f : α → CPolynomial R)
    (z : CPolynomial R) (k : ℕ) :
    (l.foldl (fun acc x => acc + f x) z).coeff k
      = z.coeff k + (l.map (fun x => (f x).coeff k)).sum := by
      induction' l using List.reverseRecOn with l ih generalizing z
      · simp
      · simp +zetaDelta at *
        convert congr_arg₂ ( · + · ) ( ‹∀ z : CPolynomial R, (
          List.foldl ( fun ( acc : CPolynomial R ) ( x : α ) => acc + f x ) z l )[ k ]?.getD 0
            = z[k]?.getD 0 + ( List.map ( fun x => ( f x)[ k ]?.getD 0 ) l ).sum› z ) rfl using 1
        any_goals exact ( f ih )[ k ]?.getD 0
        · convert add_coeff_trimmed _ _ k
          rotate_left 3
          (expose_names; exact inst_1)
          (expose_names; exact inst_2)
          exact List.foldl ( fun acc x => acc + f x ) z l
          exact f ih
          · exact Eq.symm Array.getD_eq_getD_getElem?
          · exact Eq.symm Array.getD_eq_getD_getElem?
          · exact Eq.symm Array.getD_eq_getD_getElem?
        · module

omit [BEq R] in
/--
Helper lemma for mul_assoc.
Sum over list zipIdx equals sum over Finset.range for the relevant terms.
-/
lemma sum_zipIdx_eq_sum_range {α : Type*} [AddCommMonoid α] (p : CPolynomial R) (f : R → ℕ → α) :
    (p.zipIdx.toList.map (fun ⟨a, i⟩ => f a i)).sum =
    (Finset.range p.size).sum (fun i => f (p.coeff i) i) := by
      refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop

/--
Helper lemma for mul_assoc.
Computes double sum.
-/
theorem double_sum_eq [LawfulBEq R] (p q r : CPolynomial R) (n : ℕ) :
    (Finset.range (n + 1)).sum (fun j =>
      (Finset.range (j + 1)).sum (fun i =>
        p.coeff i * q.coeff (j - i) * r.coeff (n - j)))
    =
    (Finset.range (n + 1)).sum (fun i =>
      (Finset.range (n - i + 1)).sum (fun k =>
        p.coeff i * q.coeff k * r.coeff (n - i - k))) := by
          have h_interchange : ∑ j ∈ Finset.range (n + 1),
              ∑ i ∈ Finset.range (j + 1), p.coeff i * q.coeff (j - i) * r.coeff (n - j)
                  = ∑ i ∈ Finset.range (n + 1),
                      ∑ j ∈ Finset.Ico i (n + 1),
                          p.coeff i * q.coeff (j - i) * r.coeff (n - j) := by
            rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ]
          convert h_interchange using 2
          rw [ Finset.sum_Ico_eq_sum_range ]
          simp +decide [ Nat.sub_add_comm ( Finset.mem_range_succ_iff.mp ‹_› ) ]
          exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.sub_sub ]

omit [BEq R] in
/--
Helper lemma for mul_assoc.
Extend a sum from range p.size to range (k+1) by noting extra terms are 0.
-/
lemma sum_range_extend  (p q : CPolynomial R) (k : ℕ) :
    (Finset.range p.size).sum (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) := by
      by_cases h : p.size ≤ k + 1
      · rw [ ← Finset.sum_range_add_sum_Ico _ h ]
        rw [ Finset.sum_congr rfl fun i hi =>
            if_neg ( by linarith [ Finset.mem_range.mp hi ] ), Finset.sum_Ico_eq_sum_range ]
        simp +decide [ coeff ]
      · rw [ Finset.sum_ite ]
        rw [ show Finset.filter ( fun x => ¬k < x ) ( Finset.range ( Array.size p ) )
            = Finset.range ( k + 1 ) from ?_ ]
        · simp +zetaDelta at *
        · grind

/--
Helper lemma for mul_comm.
The convolution sum is symmetric under reversal of the range. -/
lemma sum_range_reverse [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun j => p.coeff (k - j) * q.coeff j) := by
  rw [← Finset.sum_range_reflect (fun j => p.coeff (k - j) * q.coeff j) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hj' : j ≤ k := Nat.lt_succ_iff.mp hj
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hj']

-- Algebra theorems about scalar multiplication.

theorem nsmul_zero [LawfulBEq R] (p : CPolynomial R) : nsmul 0 p = 0 := by
  suffices (nsmulRaw 0 p).lastNonzero = none by simp [nsmul, trim, *]
  apply Trim.lastNonzero_none
  intros; unfold nsmulRaw
  simp only [Nat.cast_zero, zero_mul, Array.getElem_map]

theorem nsmulRawSucc (n : ℕ) (p : CPolynomial Q) :
    nsmulRaw (n + 1) p = addRaw (nsmulRaw n p) p := by
  unfold nsmulRaw
  ext
  · simp [add_size]
  next i _ hi =>
    simp [add_size] at hi
    simp [add_coeff, hi]
    rw [_root_.add_mul (R:=Q) n 1 p[i], one_mul]

theorem nsmul_succ [LawfulBEq R] (n : ℕ) {p : CPolynomial R} :
    nsmul (n + 1) p = nsmul n p + p := by
  unfold nsmul
  rw [trim_add_trim]
  apply congrArg trim
  apply nsmulRawSucc

theorem neg_trim [LawfulBEq R] (p : CPolynomial R) : p.trim = p → (-p).trim = -p := by
  apply Trim.non_zero_map
  simp

theorem neg_add_cancel [LawfulBEq R] (p : CPolynomial R) : -p + p = 0 := by
  rw [← zero_canonical]
  apply Trim.eq_of_equiv; unfold Trim.equiv; intro i
  rw [add_coeff?]
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi, Neg.neg, neg]

/--
Helper lemma for mul_assoc.
Coefficient after smul.
-/
lemma smul_coeff [LawfulBEq R] (a : R) (p : CPolynomial R) (k : ℕ) :
    (smul a p).coeff k = a * p.coeff k := by
  exact smul_equiv p k a


lemma smul_addRaw_distrib [LawfulBEq R] :
    ∀ (a' : R) (q r : CPolynomial R), smul a' (q.addRaw r)
        = (smul a' q).addRaw (smul a' r) := by
          intros a' q r
          simp [smul, addRaw]
          refine' congr_arg _ ( Array.ext _ _ );
            simp [Array.size_zipWith]
          · intro i hi₁ hi₂
            rw [Array.getElem_zipWith, Array.getElem_zipWith ]
            simp +decide [mul_add ]
            by_cases hi₃ : i < q.size <;> by_cases hi₄ : i < r.size <;> simp_all +decide

lemma smul_distrib_trim [LawfulBEq R] :
    ∀ (a' : R) (q r : CPolynomial R), (smul a' (q + r)).trim
        = smul a' q + smul a' r := by
          intros a' q r
          have h_coeff : ∀ i, (smul a' (q + r)).coeff i
              = (smul a' q).coeff i
                  + (smul a' r).coeff i := by
            have h_smul : ∀ (a' : R) (q : CPolynomial R) (i : ℕ),
                (smul a' q).coeff i = a' * q.coeff i := by
              exact fun a' q i => smul_equiv q i a'
            have h_add : ∀ (q r : CPolynomial R) (i : ℕ), (q + r).coeff i
                = q.coeff i + r.coeff i := by
              exact fun q r i => add_coeff_trimmed q r i
            simp +decide [h_smul, h_add, mul_add ]
          have h_trim_eq : ∀ p q : CPolynomial R,
              (∀ i, p.coeff i = q.coeff i) → p.trim = q.trim := by
            exact fun p q a => Trim.eq_of_equiv a
          convert h_trim_eq _ _ _ using 1
          unfold addRaw; simp +decide [h_coeff ]
          grind

/-
Helper lemma for proving: left_distrib
Distributivity of scalar multiplication over polynomial addition at the coefficient level.
-/
lemma coeff_smul_add_distrib [LawfulBEq R] (a : R) (q r : CPolynomial R) (i : ℕ) :
    (smul a (q + r)).coeff i = (smul a q).coeff i + (smul a r).coeff i := by
      -- By definition of `smul` and `add`, we can expand both sides.
      have h_expand : (smul a (q + r)).coeff i = a * ((q + r).coeff i) ∧
                         ((smul a q).coeff i) + ((smul a r).coeff i) =
                            a * (q.coeff i) + a * (r.coeff i) := by
                           have h_expand : ∀ (p : CPolynomial R), (smul a p).coeff i
                              = a * p.coeff i := by
                             exact fun p => smul_equiv p i a
                           exact ⟨ h_expand _, by rw [ h_expand, h_expand ] ⟩
      convert h_expand.1 using 1
      rw [ h_expand.2 ]
      rw [ add_coeff_trimmed ]
      simp +decide [ mul_add ]

/--
Helper lemma for proving: right_distrib.
Distributivity of scalar multiplication one right at the coefficient level.
-/
lemma coeff_add_smul [LawfulBEq R]  (a b : R) (q : CPolynomial R) (k : ℕ) :
    (smul (a + b) q).coeff k = (smul a q).coeff k + (smul b q).coeff k := by
      have h_distrib : ∀ (a b : R) (q : CPolynomial R) (k : ℕ),
          (a + b) * q.coeff k = a * q.coeff k + b * q.coeff k := by
        exact fun a b q k => add_mul a b _
      convert h_distrib a b q k using 1
      · exact smul_equiv q k (a + b)
      · congr! 1
        · exact smul_equiv q k a
        · exact smul_equiv q k b


-- Algebra lemmas and theorems about mulPowX

omit [BEq R] in
/-- Helper lemma for proving: mul_one_trim
Computing `(p.zipIdx.map (fun ⟨a, i⟩ => ((smul a 1).mulPowX i).coeff k)).sum` -/
lemma coeff_sum : ∀ (p : CPolynomial R) (k : ℕ),
    (p.zipIdx.map (fun ⟨a, i⟩ => ((smul a 1).mulPowX i).coeff k)).sum = p.coeff k := by
  intro p k; induction' p with p ih generalizing k; simp +decide [ * ]
  induction' p using List.reverseRecOn with p ih generalizing k <;>
    simp +decide [ *, List.zipIdx_append ]
  by_cases hk : k < p.length <;> simp_all +decide [ List.getElem?_append_right ]
  · simp +decide [ hk, List.getElem?_append]
    rw [ mulPowX ]
    simp +decide [ Array.getElem?_append, hk ]
  · simp +decide [ mulPowX ]
    unfold smul; simp +decide [ Array.getElem?_append ]
    rw [ if_neg hk.not_gt ]; cases k - p.length <;> simp +decide
    · exact mul_one _
    · exact rfl

/--
Helper lemma for proving: left_distrib
The coefficient of `p * q` at index `k` is the sum of the coefficients of the terms
 `(a_i * q) * X^i`.
-/
lemma coeff_mul [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map (fun ⟨a, i⟩ =>
        ((smul a q).mulPowX i).coeff k)).sum := by
      convert coeff_foldl_add _ _ _ _ using 1
      rotate_left 2
      exact inferInstance
      exact inferInstance
      exact R × ℕ
      (expose_names; exact inst_2)
      exact ( Array.zipIdx p ).toList
      exact fun x => smul x.1 q |> fun y
          => mulPowX x.2 y
      exact mk #[]
      exact k
      · congr
        simp only [Array.toList_zipIdx]
        have h_mul_def : ∀ (p q : CPolynomial R), p * q
            = (p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a q).mulPowX i) (mk #[])) := by
          exact fun p q => rfl
        convert h_mul_def p q using 1
        conv => rw [ ← Array.toList_zipIdx ]
        rw [Array.foldl_toList]
      · cases k <;> simp +decide [ * ]

/-
Helper lemma for proving: left_distrib.
The coefficient of `p * X^i` at index `k` is `0` if `k < i`, and `p_{k-i}` otherwise.
This follows from `concat_coeff₁` and `concat_coeff₂` applied to `replicate i 0 ++ p`.
-/
lemma coeff_mulPowX [LawfulBEq R] (i : ℕ) (p : CPolynomial R) (k : ℕ) :
    (p.mulPowX i).coeff k = if k < i then 0 else p.coeff (k - i) := by
      split_ifs <;> simp_all +decide [ coeff, mulPowX ]
      · rw [ Array.getElem?_append ]; aesop
      · grind

/--
Helper lemma for mul_assoc.
Coefficient mutliplication by X, similar to coeff_mulPowX.
-/
lemma coeff_mulPowX' [LawfulBEq R] (p : CPolynomial R) (n i : ℕ) :
    (p.mulPowX n).coeff i = if i < n then 0 else p.coeff (i - n) := by
      unfold mulPowX
      split_ifs <;> simp_all +decide [ coeff ]
      · rw [ Array.getElem?_append ]
        aesop
      · simp only [Array.getElem?_append, Array.getElem?_replicate,Array.size_replicate]
        split_ifs
        · omega
        · rfl

/-- Helper lemma for mul_assoc.
Coefficient of mulPowX.
 -/
lemma mulPowX_coeff' [LawfulBEq R] (p : CPolynomial R) (n k : ℕ) :
    (p.mulPowX n).coeff k = if k < n then 0 else p.coeff (k - n) := by
  exact coeff_mulPowX' p n k

/-
Helper lemma for proving: right_distrib.
Distributivity of scalar multiplication over polynomial addition at the coefficient level
-/
lemma coeff_mulPowX_smul_add [LawfulBEq R] (i : ℕ) (a b : R) (q : CPolynomial R) (k : ℕ) :
    ((smul (a + b) q).mulPowX i).coeff k =
        ((smul a q).mulPowX i).coeff k + ((smul b q).mulPowX i).coeff k := by
  rw [coeff_mulPowX, coeff_mulPowX, coeff_mulPowX]
  split_ifs
  · simp
  · rw [coeff_add_smul]

-- Algebra lemmas and theorems about multiplication of general polynomials.

/-- Multiplying a polynomial by 1 does not change the coeffs-/
lemma equiv_mul_one [LawfulBEq R] (p : CPolynomial R) : Trim.equiv (p * 1) p := by
  have h_mul_one : ∀ (p : CPolynomial R), (p * 1).coeff = p.coeff := by
    intro p; funext i
    rw [ show p * 1 = p * 1 from rfl ]
    have mul_one_unwrap : ∀ (p : CPolynomial R), (p * 1).coeff = fun k =>
      (p.zipIdx.map (fun ⟨a, i⟩ => ((smul a 1).mulPowX i).coeff k)).sum := by
      intro p; funext k; exact (by
      convert coeff_foldl_add
          ( p.zipIdx.toList ) ( fun ⟨ a, i ⟩ => ( smul a 1 ).mulPowX i ) ( mk #[] ) k using 1
      · have h_mul_def : ∀ (p : CPolynomial R), p * 1 =
            (p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a 1).mulPowX i) (mk #[])) := by
          exact fun p => rfl
        rw [h_mul_def, Array.foldl_toList]
      · simp +decide
        conv => rw [ ← Array.toList_zipIdx ]
        conv => rw [ ← Array.toList_map ]
        exact Eq.symm Array.sum_eq_sum_toList)
    exact (by exact mul_one_unwrap p ▸ coeff_sum p i ▸ rfl)
  exact congrFun (h_mul_one p)

/-- The product of two polynomails is trimmed. -/
theorem mul_is_trimmed [LawfulBEq R] (p q : CPolynomial R) : (p * q).trim = p * q := by
  convert foldl_preserves_canonical _ _ _ _ _
  · exact Trim.canonical_empty
  · intros acc x
    simp [add, addRaw]
    exact Trim.trim_twice
      (mk (Array.zipWith (fun x1 x2 => x1 + x2)
        (acc ++ Array.replicate (Array.size (mulPowX x.2 (smul x.1 q)) - Array.size acc) 0)
          (mulPowX x.2 (smul x.1 q) ++
            Array.replicate (Array.size acc - Array.size (mulPowX x.2 (smul x.1 q))) 0)))

/-
Helper lemma for proving: right_distrib
Computing coefficents of `p * q` as a sum over monomialsin `q`.
-/
lemma coeff_mul_eq_sum_range [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) (n : ℕ) (h : p.size ≤ n) :
    (p * q).coeff k =
        List.sum ((List.range n).map (fun i => ((smul (p.coeff i) q).mulPowX i).coeff k)) := by
      have h_coeff : (p * q).coeff k =
          ((p.zipIdx.toList).map
              (fun (x : R × ℕ) => ((smul x.1 q).mulPowX x.2).coeff k)).sum := by
        convert coeff_mul p q k using 1
      have h_split : List.sum (List.map
          (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k) (List.range n)) =
        List.sum (List.map
            (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k) (List.range p.size)) +
                List.sum (List.map (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k)
                    (List.drop p.size (List.range n))) := by
          rw [ ← List.sum_append, ← List.take_append_drop ( Array.size p )
               ( List.range n ), List.map_append ]
          simp +decide [ h ]
      have h_drop_zero : List.sum (List.map
          (fun i => (mulPowX i (smul (p.coeff i) q)).coeff k)
              (List.drop p.size (List.range n))) = 0 := by
        have h_zero_sum : ∀ i ∈ List.drop p.size (List.range n),
            (mulPowX i (smul (p.coeff i) q)).coeff k = 0 := by
          intro i hi
          have h_zero_coeff : p.coeff i = 0 := by
            have := List.mem_iff_get.mp hi; aesop
          simp [h_zero_coeff]
          simp +decide [ mulPowX, smul ]
          grind
        exact List.sum_eq_zero fun x hx =>
            by obtain ⟨ i, hi, rfl ⟩ := List.mem_map.mp hx; exact h_zero_sum i hi
      simp_all +decide
      congr! 1
      refine' List.ext_get _ _ <;> aesop

/--
Helper lemma for mul_assoc.
Express mul as a foldl that adds terms.
-/
lemma mul_eq_foldl (p q : CPolynomial R) :
    p * q = p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a q).mulPowX i) (mk #[]) := by
  rfl

/--
Helper lemma for mul_assoc.
Combining smul and mulPowX for the multiplication formula.
-/
lemma smul_mulPowX_coeff [LawfulBEq R] (a : R) (q : CPolynomial R) (i k : ℕ) :
    ((smul a q).mulPowX i).coeff k = if k < i then 0 else a * q.coeff (k - i) := by
    convert mulPowX_coeff' (smul a q) i k using 1
    rw [ smul_coeff ]

/--
Helper lemma for mul_assoc.
The coefficient of `p * q` at index `k`, expressed as a sum over indices of p.
This is an intermediate form before converting to Finset.range.
-/
lemma mul_coeff_list [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map
      (fun ⟨a, i⟩ => if k < i then 0 else a * q.coeff (k - i))).sum := by
        convert coeff_foldl_add _ _ _ _ using 1
        case convert_4 => exact R × ℕ
        convert rfl
        rotate_left 2
        (expose_names; exact inst_1)
        (expose_names; exact inst_2)
        exact ( Array.zipIdx p ).toList
        exact fun x => ( smul x.1 q ).mulPowX x.2
        exact mk #[]
        · convert mul_eq_foldl p q |> Eq.symm
          grind
        · have h_mulPowX_coeff : ∀ x : R × ℕ, (mulPowX x.2 (smul x.1 q)).coeff k
              = if k < x.2 then 0 else x.1 * q.coeff (k - x.2) := by
             exact fun x => smul_mulPowX_coeff x.1 q x.2 k
          aesop

/--
Helper lemma for mul_assoc.
The coefficient of `p * q` at index `k`, as a sum over 0..p.size-1
 -/
lemma mul_coeff_range_size [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (Finset.range p.size).sum
      (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) := by
        have h_coeff_mul_ci : (p * q).coeff k = (p.zipIdx.toList.map (fun ⟨a, i⟩
            => if k < i then 0 else a * q.coeff (k - i))).sum := by
          exact mul_coeff_list p q k
        convert sum_zipIdx_eq_sum_range p ( fun a i =>
            if k < i then 0 else a * q.coeff ( k - i ) ) using 1

/--
Helper lemma for mul_assoc.
The coefficient of `p * q` at index `k` is the convolution sum `Σᵢ pᵢ * q_{k-i}`.
-/
lemma mul_coeff [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) := by
  rw [mul_coeff_range_size, sum_range_extend]


/--
Helper lemma for mul_assoc.
The coefficient of `p * (q * r)` at index `n`.
-/
lemma mul_assoc_coeff_rhs [LawfulBEq R] (p q r : CPolynomial R) (n : ℕ) :
    (p * (q * r)).coeff n =
      (Finset.range (n + 1)).sum (fun i =>
        (Finset.range (n - i + 1)).sum (fun j =>
          p.coeff i * q.coeff j * r.coeff (n - i - j))) := by
  rw [mul_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_coeff]
  simp only [Finset.mem_range] at hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  grind

/--
Helper lemma for mul_assoc.
The coefficient of `(p * q) * r` at index `n`.
-/
lemma mul_mul_coeff [LawfulBEq R] (p q r : CPolynomial R) (n : ℕ) :
    ((p * q) * r).coeff n =
      (Finset.range (n + 1)).sum (fun j =>
        (Finset.range (j + 1)).sum (fun i =>
          p.coeff i * q.coeff (j - i) * r.coeff (n - j))) := by
            convert mul_coeff _ _ _
            · rw [ mul_coeff, Finset.sum_mul _ _ _ ]
            · (expose_names; exact inst_2)
 /--
 Helper lemma for mul_assoc.
 Coefficients of `(p * q) * r` and `p * (q * r)` are equal.
 -/
lemma mul_assoc_coeff [LawfulBEq R] (p q r : CPolynomial R) (n : ℕ) :
    ((p * q) * r).coeff n = (p * (q * r)).coeff n := by
  rw [mul_mul_coeff, mul_assoc_coeff_rhs, double_sum_eq]

/--
Helper lemma for mul_assoc.
The two products are equivalent (have equal coefficients everywhere).
-/
lemma mul_assoc_equiv [LawfulBEq R] (p q r : CPolynomial R) :
    Trim.equiv ((p * q) * r) (p * (q * r)) := by
  intro i
  exact mul_assoc_coeff p q r i

-- Main theorems for typeclass instances

/-- Multiplication by 1 on the right trims the polynomial. -/
theorem mul_one_trim [LawfulBEq R] (p : CPolynomial R) : p * 1 = p.trim := by
  have h_equiv : Trim.equiv (p * 1) p := by
    exact equiv_mul_one p
  have h_trim : (p * 1).trim = p * 1 := by
    exact mul_is_trimmed p 1
  have h_trim_p : p.trim.trim = p.trim := by
    exact Trim.trim_twice p
  exact (by
  apply Trim.canonical_ext
  · exact h_trim
  · exact h_trim_p
  · exact fun i => by rw [ h_equiv i, Trim.coeff_eq_coeff .. ])

/-- Multiplication by 1 on the left trims the polynomial. -/
theorem one_mul_trim [LawfulBEq R] (p : CPolynomial R) : 1 * p = p.trim := by
  have h_mul_def : ∀ (a b : CPolynomial R),
      a.mul b = (a.zipIdx.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' b).mulPowX i)) (mk #[])) :=
        by exact fun a b => rfl
  have : 1 * p = (mk #[1] : CPolynomial R).mul p := by rfl
  rw [this, h_mul_def]
  show (mk #[1]).zipIdx.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' p).mulPowX i)) (mk #[])
      = p.trim
  conv_lhs => rw [show (mk #[1] : CPolynomial R).zipIdx = #[(1, 0)] by rfl]
  rw [show Array.foldl (fun acc ⟨a', i⟩ => acc.add ((smul a' p).mulPowX i)) (mk #[]) #[(1, 0)] =
           (mk #[] : CPolynomial R).add ((smul 1 p).mulPowX 0) by rfl]
  rw [show (smul (1 : R) p).mulPowX 0 = p by simp [smul, mulPowX, one_mul]]
  have : (mk #[]).add p = 0 + p := by rfl
  rw[this, zero_add_trim]

/-- Multiplication distributes on the left.-/
theorem left_distrib [LawfulBEq R] (p q r : CPolynomial R) :
    p * (q + r) = p * q + p * r := by
      have h_eq : p * (q + r) = p * q + p * r ↔ p * (q + r) = (p * q + p * r).trim := by
        have h_canonical : (p * q).trim = p * q ∧ (p * r).trim = p * r := by
          exact ⟨ mul_is_trimmed p q, mul_is_trimmed p r ⟩
        have h_add_trim : ∀ (p q : CPolynomial R), (p + q).trim = p.trim + q.trim := by
          intros p q
          have h_add_trim : ∀ (p q : CPolynomial R), (p + q).trim = p.trim + q.trim := by
            intros p q
            have h_add_trim : ∀ (p q : CPolynomial R), (p + q).coeff
                = (p.trim + q.trim).coeff := by
              intros p q
              ext k
              simp only [Array.getD_eq_getD_getElem?]
              convert add_coeff_trimmed p q k using 1
              ·exact Eq.symm Array.getD_eq_getD_getElem?
              · convert add_coeff_trimmed p.trim q.trim k using 1
                · exact Eq.symm Array.getD_eq_getD_getElem?
                · rw [ Trim.coeff_eq_coeff, Trim.coeff_eq_coeff ]
            apply Trim.canonical_ext
            · exact Trim.trim_twice (p + q)
            · apply Trim.trim_twice
            · exact fun i => by rw [ Trim.coeff_eq_coeff, h_add_trim ]
          exact h_add_trim p q
        rw [ h_add_trim, h_canonical.1, h_canonical.2 ]
      have h_equiv : (p * (q + r)).coeff = (p * q + p * r).coeff := by
        ext k
        rw [ coeff_mul, add_coeff_trimmed ]
        rw [ coeff_mul, coeff_mul ]
        rw [ ← List.sum_map_add ]
        congr! 2
        ext ⟨ a, i ⟩; by_cases hi : k < i <;> simp +decide
        · simp +decide [mulPowX]
          rw [ Array.getElem?_append, Array.getElem?_append, Array.getElem?_append ]; aesop
        · convert coeff_smul_add_distrib a q r ( k - i ) using 1
          · convert coeff_mulPowX i ( smul a ( q + r ) ) k using 1
            · exact Eq.symm Array.getD_eq_getD_getElem?
            · aesop
          · simp +decide [ mulPowX]
            grind
      have h_trim : (p * (q + r)).trim = (p * q + p * r).trim := by
        exact Trim.eq_of_equiv (congrFun h_equiv)
      convert h_eq.mpr _
      convert h_trim using 1
      exact Eq.symm (mul_is_trimmed p (q + r))

/-- Multiplication distributes on the right.-/
theorem right_distrib [LawfulBEq R] (p q r : CPolynomial R) :
    (p + q) * r = p * r + q * r := by
  have h_coeff : ∀ k, ((p + q) * r).coeff k = (p * r + q * r).coeff k := by
    intro k
    have h_sum : ((p + q) * r).coeff k =
        List.sum ((List.range (p.size + q.size)).map
            (fun i => ((smul ((p + q).coeff i) r).mulPowX i).coeff k)) := by
      convert coeff_mul_eq_sum_range ( p + q ) r k ( p.size + q.size ) _ using 1
      have h_size_sum : (p + q).size ≤ max p.size q.size := by
        convert Trim.size_le_size ( p.addRaw q ) using 1
        exact Eq.symm add_size
      exact le_trans h_size_sum ( max_le ( Nat.le_add_right _ _ ) ( Nat.le_add_left _ _ ) )
    have h_split : List.sum ((List.range (p.size + q.size)).map
        (fun i => ((smul ((p + q).coeff i) r).mulPowX i).coeff k)) =
      List.sum ((List.range (p.size + q.size)).map
          (fun i => ((smul (p.coeff i) r).mulPowX i).coeff k)) +
          List.sum ((List.range (p.size + q.size)).map
              (fun i => ((smul (q.coeff i) r).mulPowX i).coeff k)) := by
        have h_split : ∀ i ∈ List.range (p.size + q.size),
            ((smul ((p + q).coeff i) r).mulPowX i).coeff k =
              ((smul (p.coeff i) r).mulPowX i).coeff k +
                  ((smul (q.coeff i) r).mulPowX i).coeff k := by
            intro i hi
            have h_split : ((p + q).coeff i) = (p.coeff i) + (q.coeff i) := by
              exact add_coeff_trimmed p q i
            convert coeff_mulPowX_smul_add i ( p.coeff i ) ( q.coeff i ) r k using 1
            rw [ h_split ]
        rw [ ← List.sum_map_add, List.map_congr_left h_split ]
    have h_coeff_r : (p * r).coeff k + (q * r).coeff k =
        List.sum ((List.range (p.size + q.size)).map
            (fun i => ((smul (p.coeff i) r).mulPowX i).coeff k)) +
                List.sum ((List.range (p.size + q.size)).map
                    (fun i => ((smul (q.coeff i) r).mulPowX i).coeff k)) := by
      have h_coeff_r : (p * r).coeff k =
          List.sum ((List.range (p.size + q.size)).map
              (fun i => ((smul (p.coeff i) r).mulPowX i).coeff k))
                  ∧ (q * r).coeff k = List.sum
                      ((List.range (p.size + q.size)).map
                          (fun i => ((smul (q.coeff i) r).mulPowX i).coeff k)) := by
        apply And.intro
        · convert coeff_mul_eq_sum_range p r k ( p.size + q.size )
              ( by linarith ) using 1
        · convert coeff_mul_eq_sum_range q r k ( p.size + q.size )
              ( by linarith ) using 1
      rw [h_coeff_r.1, h_coeff_r.2 ]
    rw [ h_sum, h_split, ← h_coeff_r, add_coeff_trimmed ]
  convert Trim.canonical_ext _ _ ( h_coeff )
  · exact mul_is_trimmed (p + q) r
  · apply Trim.trim_twice


theorem mul_assoc [LawfulBEq R] (p q r : CPolynomial R) : p * q * r = p * (q * r) := by
  apply Trim.canonical_ext
  · exact mul_is_trimmed (p * q) r
  · exact mul_is_trimmed p (q * r)
  · exact mul_assoc_equiv p q r

section CommutativeRing

--Theorems about multiplication in the case where R is commutative

variable {R : Type*} [CommRing R] [BEq R]

/-- Using commutativity of R to swap the multiplication order.-/
lemma mul_coeff_comm [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => q.coeff i * p.coeff (k - i)) := by
  rw [sum_range_reverse]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf


/-- Coefficients of p * q and q * p are equal. -/
lemma mul_comm_coeff [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (q * p).coeff k := by
  rw [mul_coeff, mul_coeff]
  exact mul_coeff_comm p q k

/-- p * q and q * p are equivalent (have equal coefficients everywhere).-/
lemma mul_comm_equiv [LawfulBEq R] (p q : CPolynomial R) :
    Trim.equiv (p * q) (q * p) := by
  intro i
  exact mul_comm_coeff p q i

/-- Commutativity of multiplication for CPolynomial over a CommRing. -/
theorem mul_comm [LawfulBEq R] (p q : CPolynomial R) : p * q = q * p := by
  apply Trim.canonical_ext
  · exact mul_is_trimmed p q
  · exact mul_is_trimmed q p
  · exact mul_comm_equiv p q

end CommutativeRing

end Operations

section AddCommSemiroup

instance [LawfulBEq R] : AddCommSemigroup (CPolynomial R) where
  add_assoc := by intro _ _ _; rw [add_assoc]
  add_comm := add_comm

end AddCommSemiroup

end CPolynomial

end CompPoly
