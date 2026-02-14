/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Raw

/-!
  # Computable Univariate Polynomials

  This file defines `CPolynomial R`, the type of canonical (trimmed) univariate polynomials.
  A polynomial is canonical if it has no trailing zeros, i.e., `p.trim = p`.

  This provides a unique representation for each polynomial, enabling stronger extensionality
  properties compared to the raw `CPolynomial.Raw` type.
-/
namespace CompPoly

open CPolynomial.Raw

variable {R : Type*} [BEq R]

/-- Computable univariate polynomials are represented canonically with no trailing zeros.

  A polynomial `p : CPolynomial.Raw R` is canonical if `p.trim = p`, meaning the last coefficient
  is non-zero (or the polynomial is empty). This provides a unique representative for each
  polynomial equivalence class.

-/
def CPolynomial (R : Type*) [BEq R] [Semiring R] := { p : CPolynomial.Raw R // p.trim = p }

namespace CPolynomial

/-- Extensionality for canonical polynomials. -/
@[ext] theorem ext [Semiring R] {p q : CPolynomial R} (h : p.val = q.val) : p = q := by
  exact Subtype.ext h

/-- Canonical polynomials coerce to raw polynomials. -/
instance [Semiring R] : Coe (CPolynomial R) (CPolynomial.Raw R) where coe := Subtype.val

/-- The zero polynomial is canonical. -/
instance [Semiring R] : Inhabited (CPolynomial R) := ⟨#[], Trim.canonical_empty⟩

section Operations

variable [Semiring R] [LawfulBEq R]
variable (p q r : CPolynomial R)

/-- Addition of canonical polynomials (result is canonical). -/
instance : Add (CPolynomial R) where
  add p q := ⟨p.val + q.val, by apply Trim.trim_twice⟩

theorem add_comm : p + q = q + p := by
  apply CPolynomial.ext; apply Raw.add_comm

theorem add_assoc : p + q + r = p + (q + r) := by
  apply CPolynomial.ext; apply Raw.add_assoc

instance : Zero (CPolynomial R) := ⟨0, zero_canonical⟩

theorem zero_add : 0 + p = p := by
  apply CPolynomial.ext
  apply Raw.zero_add p.val p.prop

theorem add_zero : p + 0 = p := by
  apply CPolynomial.ext
  apply Raw.add_zero p.val p.prop

/-- Scalar multiplication by a natural number (result is canonical). -/
def nsmul (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  ⟨Raw.nsmul n p.val, by apply Trim.trim_twice⟩

theorem nsmul_zero : nsmul 0 p = 0 := by
  apply CPolynomial.ext; apply Raw.nsmul_zero

theorem nsmul_succ (n : ℕ) (p : CPolynomial R) : nsmul (n + 1) p = nsmul n p + p := by
  apply CPolynomial.ext; apply Raw.nsmul_succ

instance [LawfulBEq R] : AddCommSemigroup (CPolynomial R) where
  add_assoc := add_assoc
  add_comm := add_comm

/-- Multiplication of canonical polynomials.

  The product of two canonical polynomials is canonical because multiplication
  preserves the "no trailing zeros" property.
-/
instance : Mul (CPolynomial R) where
  mul p q :=
    ⟨p.val * q.val, by exact mul_is_trimmed p.val q.val⟩

lemma one_is_trimmed [Nontrivial R] : (1 : CPolynomial.Raw R).trim = 1 :=
  Trim.push_trim #[] 1 one_ne_zero

/-- The constant polynomial 1 is canonical, and is the Unit for multiplication.

  This is `#[1]`, which has no trailing zeros.

  This proof does not work without the assumption that R is non-trivial.
-/
instance [Nontrivial R] : One (CPolynomial R) where
  one := ⟨Raw.C 1, by exact one_is_trimmed⟩

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff (p : CPolynomial R) (i : ℕ) : R := p.val.coeff i

/-- The constant polynomial `C r`. -/
def C (r : R) : CPolynomial R := ⟨(Raw.C r).trim, by rw [Trim.trim_twice]⟩

/-- The variable `X`. -/
def X [Nontrivial R] : CPolynomial R := ⟨Raw.X, X_canonical⟩

/-- Construct a canonical monomial `c * X^n` as a `CPolynomial R`.

  The result is canonical (no trailing zeros) when `c ≠ 0`.
  For example, `monomial 2 3` represents `3 * X^2`.

  Note: If `c = 0`, this returns `0` (the zero polynomial).
-/
def monomial [DecidableEq R] (n : ℕ) (c : R) : CPolynomial R :=
  ⟨Raw.monomial n c, Raw.monomial_canonical n c⟩

/-- Return the degree of a `CPolynomial`. -/
def degree (p : CPolynomial R) : WithBot ℕ := p.val.degree

/-- Natural number degree of a canonical polynomial.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree (p : CPolynomial R) : ℕ := p.val.natDegree

/-- Return the leading coefficient of a `CPolynomial` as the last coefficient
of the trimmed array, or `0` if the trimmed array is empty. -/
def leadingCoeff (p : CPolynomial R) : R := p.val.leadingCoeff

/-- Evaluate a polynomial at a point. -/
def eval (x : R) (p : CPolynomial R) : R := p.val.eval x

/-- Evaluate at `x : S` via a ring hom
`f : R →+* S`; `eval₂ f x p = f(a₀) + f(a₁)*x + f(a₂)*x² + ...`. -/
def eval₂ {S : Type*} [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial R) : S := p.val.eval₂ f x

/-- The support of a polynomial: indices with nonzero coefficients. -/
def support (p : CPolynomial R) : Finset ℕ :=
  (Finset.range p.val.size).filter (fun i => p.val.coeff i != 0)

/-- Number of coefficients (length of the underlying array). -/
def size (p : CPolynomial R) : ℕ := p.val.size

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound (p : CPolynomial R) : WithBot Nat := p.val.degreeBound

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : CPolynomial R) : Nat := p.val.natDegreeBound

/-- Check if a `CPolynomial` is monic, i.e. its leading coefficient is 1. -/
def monic (p : CPolynomial R) : Bool := p.val.monic

/-- The polynomial with the constant term removed; `coeff (divX p) i = coeff p (i + 1)`. -/
def divX (p : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divX p.val).trim, by
    simpa using (Trim.trim_twice (p.val.extract 1 p.val.size))⟩

/-- Coefficient of the constant polynomial `C r`. -/
lemma coeff_C (r : R) (i : ℕ) : coeff (C r) i = if i = 0 then r else 0 := by
  unfold C; simp only [coeff]
  rw [Trim.coeff_eq_coeff, Raw.coeff_C]

omit [BEq R] [Semiring R] [LawfulBEq R] in
/-- Coefficient of the variable `X`. -/
lemma coeff_X [Nontrivial R] (i : ℕ) : coeff X i = if i = 1 then 1 else 0 := by
  simp only [X, coeff]; rw [Raw.coeff_X]

omit [LawfulBEq R] in
/-- Coefficient of the zero polynomial. -/
@[simp]
lemma coeff_zero (i : ℕ) : coeff (0 : CPolynomial R) i = 0 := by
  simp; rfl

/-- Coefficient of the constant polynomial `1`. -/
lemma coeff_one [Nontrivial R] (i : ℕ) :
    coeff (1 : CPolynomial R) i = if i = 0 then 1 else 0 := by
  simp only [coeff]
  change Raw.coeff 1 i = if i = 0 then 1 else 0
  rw [Raw.coeff_one]

/-- Coefficient of a sum. -/
lemma coeff_add (p q : CPolynomial R) (i : ℕ) : coeff (p + q) i = coeff p i + coeff q i := by
  unfold coeff; exact Raw.add_coeff_trimmed p.val q.val i

/-- Coefficient of a monomial. -/
lemma coeff_monomial [DecidableEq R] (n i : ℕ) (c : R) :
    coeff (monomial n c) i = if i = n then c else 0 := by
  unfold coeff monomial; rw [Raw.coeff_monomial]; simp only [eq_comm]

/-- Coefficient of a product (convolution sum). -/
lemma coeff_mul (p q : CPolynomial R) (k : ℕ) :
    coeff (p * q) k = (Finset.range (k + 1)).sum (fun i => coeff p i * coeff q (k - i)) := by
  unfold coeff; exact Raw.mul_coeff p.val q.val k

/-- Two polynomials are equal iff they have the same coefficients. -/
theorem eq_iff_coeff {p q : CPolynomial R} :
    p = q ↔ ∀ i, coeff p i = coeff q i := by
  constructor
  · intro h i; rw [h]
  · intro h; apply ext; exact Trim.canonical_ext p.prop q.prop (fun i => h i)

/-- Zero characterization: `p = 0` iff all coefficients are zero. -/
theorem eq_zero_iff_coeff_zero {p : CPolynomial R} : p = 0 ↔ ∀ i, coeff p i = 0 := by
  rw [eq_iff_coeff]; simp only [coeff_zero]

/-- An index is in the support iff the coefficient there is nonzero. -/
lemma mem_support_iff (p : CPolynomial R) (i : ℕ) : i ∈ p.support ↔ coeff p i ≠ 0 := by
  unfold support coeff
  rw [Finset.mem_filter]
  constructor
  · intro ⟨hi, h⟩; rwa [bne_iff_ne] at h
  · intro h; constructor
    · by_contra hle
      have hge : p.val.size ≤ i := by rwa [Finset.mem_range, not_lt] at hle
      rw [Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge, Option.getD_none]
        at h
      exact h rfl
    · exact bne_iff_ne.mpr h

/-- The support is empty iff the polynomial is zero. -/
theorem support_empty_iff (p : CPolynomial R) : p.support = ∅ ↔ p = 0 := by
  rw [eq_zero_iff_coeff_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h i; by_contra hne; exact h i ((mem_support_iff p i).mpr hne)
  · intro h i; rw [mem_support_iff, h]; simp

/-- Lemmas on coefficients and multiplication by `X`. -/
lemma coeff_X_mul_succ [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    coeff (X * p) (n + 1) = coeff p n := by
  unfold coeff
  change ((X.val * p.val).coeff (n + 1) = p.val.coeff n)
  rw [Raw.mul_coeff]
  simp only [X]
  have hmem : (1 : ℕ) ∈ Finset.range (n + 1 + 1) := by simp
  have hsum :
      (Finset.range (n + 1 + 1)).sum (fun i => Raw.X.coeff i * p.val.coeff (n + 1 - i)) =
        Raw.X.coeff 1 * p.val.coeff (n + 1 - 1) := by
    refine Finset.sum_eq_single_of_mem (a := 1) hmem ?_
    intro i hi hne
    rw [Raw.coeff_X (R := R) i]
    simp [hne]
  rw [hsum]
  have hn : n + 1 - 1 = n := by omega
  rw [hn, Raw.coeff_X (R := R) 1]
  simp

lemma coeff_X_mul_zero [Nontrivial R] (p : CPolynomial R) : coeff (X * p) 0 = 0 := by
  unfold coeff
  change ((Raw.X * p.val) : Raw R).coeff 0 = 0
  rw [Raw.mul_coeff]
  -- (Finset.range 1).sum ... reduces to the single term at 0
  simp [Raw.X]

theorem coeff_mul_X_succ [Nontrivial R] (p : CPolynomial R) (n : ℕ) :
    coeff (p * X) (n + 1) = coeff p n := by
  unfold coeff
  change ((p.val * X.val).coeff (n + 1) = p.val.coeff n)
  rw [Raw.mul_coeff]
  simp only [X]
  have hmem : n ∈ Finset.range (n + 1 + 1) := by
    simp [Finset.mem_range]
    omega
  have hsum :
      (Finset.range (n + 1 + 1)).sum (fun i => p.val.coeff i * Raw.X.coeff (n + 1 - i)) =
        p.val.coeff n * Raw.X.coeff (n + 1 - n) := by
    refine Finset.sum_eq_single_of_mem (a := n) hmem ?_
    intro i hi hne
    have hsub : n + 1 - i ≠ 1 := by
      intro h
      have : i = n := by
        omega
      exact hne this
    rw [Raw.coeff_X (R := R) (n + 1 - i)]
    simp [hsub]
  rw [hsum]
  have hn : n + 1 - n = 1 := by
    omega
  rw [hn, Raw.coeff_X (R := R) 1]
  simp

theorem coeff_mul_X_zero [Nontrivial R] (p : CPolynomial R) : coeff (p * X) 0 = 0 := by
  rw [coeff_mul]
  simp [X, Raw.X]

omit [BEq R] [LawfulBEq R] in
lemma coeff_extract_succ (a : CPolynomial.Raw R) (i : ℕ) :
    Raw.coeff (a.extract 1 a.size) i = Raw.coeff a (i + 1) := by
  simp [Raw.coeff, Array.getElem?_extract]
  by_cases h : i < a.size - 1
  · have h1 : 1 + i = i + 1 := by omega
    simp [h, h1]
  · have hge : a.size ≤ i + 1 := by omega
    simp [h, Array.getElem?_eq_none (xs := a) (i := i + 1) hge]

lemma coeff_divX (p : CPolynomial R) (i : ℕ) : coeff (divX p) i = coeff p (i + 1) := by
  -- LHS: coeff of divX = coeff of trimmed extract
  unfold divX
  -- turn coefficients of CPolynomial into raw coefficients
  simp only [CPolynomial.coeff]
  -- remove the trim on coefficients
  have htrim :=
    (Trim.coeff_eq_coeff
      (p := ((↑p : CPolynomial.Raw R).extract 1 (↑p : CPolynomial.Raw R).size)) (i := i))
  -- shift the extract
  exact htrim.trans (coeff_extract_succ (a := (↑p : CPolynomial.Raw R)) (i := i))

lemma X_mul_divX_add [Nontrivial R] (p : CPolynomial R) : p = X * divX p + C (coeff p 0) := by
  apply CPolynomial.ext
  rw [add_comm]
  refine Trim.canonical_ext (p := p.val)
      (q := (C (coeff p 0) + X * divX p).val) ?_ ?_ ?_
  · exact p.property
  · exact (C (coeff p 0) + X * divX p).property
  · intro k
    change coeff p k = coeff (C (coeff p 0) + X * divX p) k
    cases k with
    | zero =>
        rw [coeff_add (p := C (coeff p 0)) (q := X * divX p) (i := 0)]
        have hC0 : coeff (C (coeff p 0)) 0 = coeff p 0 := by
          simpa using (coeff_C (R := R) (r := coeff p 0) (i := 0))
        have hX0 : coeff (X * divX p) 0 = 0 := by
          simpa using (coeff_X_mul_zero (R := R) (p := divX p))
        rw [hC0, hX0]
        simp only [_root_.add_zero]
    | succ n =>
        rw [coeff_add (p := C (coeff p 0)) (q := X * divX p) (i := n + 1)]
        have hCsucc : coeff (C (coeff p 0)) (n + 1) = 0 := by
          simpa [Nat.succ_ne_zero n] using
            (coeff_C (R := R) (r := coeff p 0) (i := n + 1))
        have hXsucc : coeff (X * divX p) (n + 1) = coeff (divX p) n := by
          simpa using (coeff_X_mul_succ (R := R) (p := divX p) (n := n))
        have hdivX : coeff (divX p) n = coeff p (n + 1) := by
          simpa using (coeff_divX (p := p) (i := n))
        rw [hCsucc, hXsucc, hdivX]
        simp only [_root_.zero_add]

theorem divX_mul_X_add [Nontrivial R] (p : CPolynomial R) : divX p * X + C (p.coeff 0) = p := by
  classical
  rw [eq_iff_coeff]
  intro k
  cases k with
  | zero =>
      rw [coeff_add (p := divX p * X) (q := C (p.coeff 0)) (i := 0)]
      rw [coeff_mul_X_zero (p := divX p)]
      rw [coeff_C (R := R) (r := p.coeff 0) (i := 0)]
      simp
  | succ n =>
      rw [coeff_add (p := divX p * X) (q := C (p.coeff 0)) (i := n + 1)]
      rw [coeff_mul_X_succ (p := divX p) (n := n)]
      rw [coeff_C (R := R) (r := p.coeff 0) (i := n + 1)]
      have hne : n + 1 ≠ 0 := by
        exact Nat.succ_ne_zero n
      simp only [Array.getD_eq_getD_getElem?, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, _root_.add_zero]
      simpa using (coeff_divX (p := p) (i := n))

lemma divX_size_lt (p : CPolynomial R) (hp : p.val.size > 0) :
    (divX p).val.size < p.val.size := by
  unfold divX
  have hle : (Raw.trim (p.val.extract 1 p.val.size)).size
      ≤ (p.val.extract 1 p.val.size).size := by
    simpa using (Trim.size_le_size (p := p.val.extract 1 p.val.size))
  have hextract : (p.val.extract 1 p.val.size).size = p.val.size - 1 := by
    simp only [Array.size_extract, min_self]
  have hle' : (Raw.trim (p.val.extract 1 p.val.size)).size ≤ p.val.size - 1 := by
    simpa [hextract] using hle
  exact lt_of_le_of_lt hle' (Nat.pred_lt_self hp)

/-- Induction principle for polynomials (mirrors mathlib's `Polynomial.induction_on`). -/
theorem induction_on [Nontrivial R] {P : CPolynomial R → Prop} (p : CPolynomial R)
    (h0 : P 0) (hC : ∀ a, P (C a)) (hadd : ∀ p q, P p → P q → P (p + q))
    (hX : ∀ p, P p → P (X * p)) : P p := by
  -- Strong induction on the size of the underlying coefficient array
  refine
    (Nat.strong_induction_on
        (p := fun n : ℕ => ∀ p : CPolynomial R, p.val.size = n → P p)
        (p.val.size) ?_) p rfl
  intro n ih p hn
  cases n with
  | zero =>
      have hval : p.val = (#[] : CPolynomial.Raw R) := by
        exact Array.eq_empty_of_size_eq_zero (by simpa using hn)
      have hp0 : p = (0 : CPolynomial R) := by
        apply CPolynomial.ext
        simpa using hval
      simpa [hp0] using h0
  | succ n =>
      have hp_pos : p.val.size > 0 := by
        simp [hn]
      have hdivX_lt : (divX p).val.size < Nat.succ n := by
        have ht := divX_size_lt (p := p) hp_pos
        simpa [hn] using ht
      have hdivX : P (divX p) := ih (divX p).val.size hdivX_lt (divX p) rfl
      have hXt : P (X * divX p) := hX (divX p) hdivX
      have hC0 : P (C (coeff p 0)) := hC (coeff p 0)
      have hsum : P (C (coeff p 0) + X * divX p) := hadd _ _ hC0 hXt
      -- Rewrite using Horner decomposition
      rw [X_mul_divX_add (p := p), add_comm]
      exact hsum

omit [LawfulBEq R] in
/- Auxiliary lemmas for `degree_eq_support_max`: relating `degree`, `support`, and `lastNonzero`. -/
/-- Lemma for `degree_eq_support_max`: degree in terms of `lastNonzero`. -/
lemma degree_eq_support_max_aux_degree (p : CPolynomial R) {k : Fin p.val.size}
    (hk : p.val.lastNonzero = some k) : p.degree = k.val := by
  unfold CPolynomial.degree
  unfold Raw.degree
  simp [hk]

omit [LawfulBEq R] in
lemma degree_eq_support_max_aux_lastNonzero (p : CPolynomial R) (hp : p ≠ 0) :
    ∃ k : Fin p.val.size, p.val.lastNonzero = some k := by
  cases hln : p.val.lastNonzero with
  | some k =>
      exact ⟨k, rfl⟩
  | none =>
      have htrim : p.val.trim = (#[] : CPolynomial.Raw R) := by
        simp [Raw.trim, hln]
      have hval : p.val = (#[] : CPolynomial.Raw R) := by
        have htrim' := htrim
        rw [p.prop] at htrim'
        exact htrim'
      have hp0 : p = 0 := by
        apply Subtype.ext
        simpa using hval
      exact (hp hp0).elim

lemma degree_eq_support_max_aux_mem_support (p : CPolynomial R) {k : Fin p.val.size}
    (hk : p.val.lastNonzero = some k) : k.val ∈ p.support := by
  unfold CPolynomial.support
  rcases k with ⟨k, hklt⟩
  refine (Finset.mem_filter).2 ?_
  refine ⟨?_, ?_⟩
  · exact Finset.mem_range.2 hklt
  · have hnonzeroFin : p.val[(⟨k, hklt⟩ : Fin p.val.size)] ≠ (0 : R) :=
      (Trim.lastNonzero_spec (p := p.val) (k := ⟨k, hklt⟩) hk).1
    have hnonzero : p.val[k]'hklt ≠ (0 : R) := by
      simpa using hnonzeroFin
    have hcoeff_ne : p.val.coeff k ≠ (0 : R) := by
      have hcoeff : p.val.coeff k = p.val[k]'hklt := by
        simpa using (Trim.coeff_eq_getElem (p := p.val) (i := k) hklt)
      simpa [hcoeff] using hnonzero
    exact bne_iff_ne.mpr hcoeff_ne

/-- Degree equals the maximum of the support when the polynomial is non-zero.
  Here `p.degree = some n` where `n` is the maximum index in `p.support`. -/
theorem degree_eq_support_max (p : CPolynomial R) (hp : p ≠ 0) :
    ∃ n, n ∈ p.support ∧ p.degree = n := by
  obtain ⟨k, hk⟩ := degree_eq_support_max_aux_lastNonzero (p := p) hp
  refine ⟨k.val, ?_⟩
  constructor
  · exact degree_eq_support_max_aux_mem_support (p := p) hk
  · exact degree_eq_support_max_aux_degree (p := p) hk

omit [LawfulBEq R] in
/-- When `p ≠ 0`, `degree p` equals `natDegree p` (as `WithBot ℕ`). -/
theorem degree_eq_natDegree (p : CPolynomial R) (hp : p ≠ 0) :
    p.degree = p.natDegree := by
  obtain ⟨k, hk⟩ := degree_eq_support_max_aux_lastNonzero (p := p) hp
  rw [degree_eq_support_max_aux_degree (p := p) hk]
  unfold natDegree Raw.natDegree
  rw [hk]

end Operations

section Semiring

variable [Semiring R] [LawfulBEq R]
variable (p q r : CPolynomial R)

lemma one_mul [Nontrivial R] (p : CPolynomial R) : 1 * p = p := by
  apply Subtype.ext
  have : (1 * p : CPolynomial R) = (1: CPolynomial.Raw R) * p.val := rfl
  rw[this, one_mul_trim]
  exact p.prop

lemma mul_one [Nontrivial R] (p : CPolynomial R) : p * 1 = p := by
  apply Subtype.ext
  have : (p * 1 : CPolynomial R) = p.val * (1: CPolynomial.Raw R) := rfl
  rw[this, mul_one_trim]
  exact p.prop

lemma mul_assoc (p q r : CPolynomial R) : (p * q) * r = p * (q * r) := by
  apply Subtype.ext
  exact Raw.mul_assoc p.val q.val r.val

lemma zero_mul (p : CPolynomial R) : 0 * p = 0 := by
  apply Subtype.ext
  exact Raw.zero_mul p.val

lemma mul_zero (p : CPolynomial R) : p * 0 = 0 := by
  apply Subtype.ext
  exact Raw.mul_zero p.val

lemma mul_add (p q r : CPolynomial R) : p * (q + r) = p * q + p * r := by
  apply Subtype.ext
  exact Raw.mul_add p.val q.val r.val

lemma add_mul (p q r : CPolynomial R) : (p + q) * r = p * r + q * r := by
  apply Subtype.ext
  exact Raw.add_mul p.val q.val r.val

lemma pow_is_trimmed [Nontrivial R]
    (p : CPolynomial.Raw R) (n : ℕ) : (p ^ n).trim = p ^ n := by
      induction' n with n ih generalizing p;
      · convert one_is_trimmed
        · infer_instance
        · infer_instance
      · have h_exp : p ^ (n + 1) = p * p ^ n := by
          exact pow_succ p n
        rw [h_exp]
        convert mul_is_trimmed p ( p ^ n ) using 1

lemma pow_succ_right [Nontrivial R]
    (p : CPolynomial.Raw R) (n : ℕ) : p ^ (n + 1) = p ^ n * p := by
      convert pow_succ p n using 1;
      induction' n with n ih;
      · have h_pow_zero : p ^ 0 = 1 := by
          exact rfl
        rw [h_pow_zero, mul_one_trim, one_mul_trim];
      · simp_all +decide [Raw.pow_succ];
        convert Raw.mul_assoc p ( p ^ n ) p using 1;
        grind

/--
`CPolynomial R` forms a commutative monoid when `R` is a semiring.
-/
instance : AddCommMonoid (CPolynomial R) where
  zero_add := zero_add
  add_zero := by intro p; exact add_zero p
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ

/-- `CPolynomial R` forms a semiring when `R` is a semiring.

  The semiring structure extends the `AddCommGroup` structure with multiplication.
  All operations preserve the canonical property (no trailing zeros).
-/
instance [LawfulBEq R] [Nontrivial R] : Semiring (CPolynomial R) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := by intro p; exact add_zero p
  add_comm := add_comm
  zero_mul := by intro p; exact zero_mul p
  mul_zero := by intro p; exact mul_zero p
  mul_assoc := by intro p q r; exact mul_assoc p q r
  one_mul := by intro p; exact one_mul p
  mul_one := by intro p; exact mul_one p
  left_distrib := by intro p q r; exact mul_add p q r
  right_distrib := by  intro p q r; exact add_mul p q r
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  npow n p := ⟨p.val ^ n, by apply CPolynomial.pow_is_trimmed⟩
  npow_zero := by intro x; apply Subtype.ext; rfl
  npow_succ := by intro n p; apply Subtype.ext; exact
      (CPolynomial.pow_succ_right p.val n)
  natCast_zero := by rfl
  natCast_succ := by intro n; rfl

/-- `C r * X^n = monomial n r` as canonical polynomials. -/
lemma C_mul_X_pow_eq_monomial [LawfulBEq R] [DecidableEq R] [Nontrivial R] (r : R) (n : ℕ) :
    (C r : CPolynomial R) * (X ^ n) = monomial n r := by
  by_cases hr : r = 0
  · convert Subtype.ext ?_
    convert zero_mul _
    rotate_left
    exact R
    all_goals try infer_instance
    exact 0
    simp +decide [hr, C, X, monomial]
    -- Since multiplying by 0 gives the zero polynomial, the left-hand side simplifies to 0.
    have h_lhs : (Raw.C 0).trim *
        (Raw.X : CPolynomial.Raw R) ^ n = 0 := by
      convert Raw.zero_mul _ using 1
      convert rfl
      · exact Eq.symm ( Raw.trim_replicate_zero 1 )
      · infer_instance
    convert h_lhs using 1
    exact Eq.symm (by induction n <;> simp +decide [*, Raw.monomial])
  · convert Subtype.ext ?_
    have h_trim : (Raw.mk #[r]).trim = Raw.C r := by
      exact Trim.canonical_iff.mpr fun hp => hr
    generalize_proofs at *
    convert Raw.C_mul_eq_smul_trim r (Raw.X ^ n) using 1
    · exact h_trim.symm ▸ rfl
    · convert Raw.smul_monomial_one_trim n r |> Eq.symm using 1
      rw [Raw.X_pow_eq_monomial_one]

end Semiring

section CommSemiring

variable [CommSemiring R] [LawfulBEq R]
variable (p q : CPolynomial R)

lemma mul_comm (p q : CPolynomial R) : p * q = q * p := by
  apply Subtype.ext
  have dist_lhs : (p * q : CPolynomial R) = (p.val * q.val : CPolynomial.Raw R) := rfl
  have dist_rhs : (q * p : CPolynomial R) = (q.val * p.val : CPolynomial.Raw R) := rfl
  rw [dist_lhs, dist_rhs]
  exact Raw.mul_comm p.val q.val

/-- `CPolynomial R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommSemiring R] [Nontrivial R] : CommSemiring (CPolynomial R) where
  mul_comm := by intro p q; exact mul_comm p q

end CommSemiring

section Ring

variable [Ring R] [LawfulBEq R]
variable (p q : CPolynomial R)

instance : Neg (CPolynomial R) where
  neg p := ⟨-p.val, neg_trim p.val p.prop⟩

instance : Sub (CPolynomial R) where
  sub p q := p + -q

lemma erase_canonical [DecidableEq R] (n : ℕ) (p : CPolynomial R) :
    let e := p.val - Raw.monomial n (p.val.coeff n)
    e.trim = e := by
  simp; apply Trim.trim_twice

/-- Erase the coefficient at index `n` (same as `p` except `coeff n = 0`, then trimmed). -/
def erase [DecidableEq R] (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  let e := p.val - Raw.monomial n (p.val.coeff n)
  ⟨e, by rw [erase_canonical]⟩

/-- Coefficient of `erase n p`: zero at `n`, otherwise `coeff p i`. -/
lemma coeff_erase [DecidableEq R] (n i : ℕ) (p : CPolynomial R) :
    coeff (erase n p) i = if i = n then 0 else coeff p i := by
  unfold erase coeff
  rw [Raw.sub_coeff, Raw.coeff_monomial]
  by_cases h : n = i <;> simp [h]
  intro h'; rw [h'] at h
  contradiction

/-- Leading coefficient equals the coefficient at `natDegree`. -/
lemma leadingCoeff_eq_coeff_natDegree [Semiring R] [DecidableEq R] (p : CPolynomial R) :
    p.leadingCoeff = p.coeff p.natDegree := by
      -- If empty, both leadingCoeff and coeff at natDegree are zero.
      by_cases h_empty : p.val.size = 0;
      · simp +decide [h_empty, CPolynomial.leadingCoeff, CPolynomial.coeff,
          CPolynomial.natDegree]
        unfold Raw.leadingCoeff
        unfold Raw.trim; aesop
      · -- Since `p` is canonical, `p.val.getLastD 0` is the last element of `p.val`.
        have h_last : p.val.getLastD 0 = p.val.coeff (p.val.size - 1) := by
          simp +decide [Array.getLastD, Raw.coeff]
          cases h : (p : CPolynomial.Raw R)[(p : CPolynomial.Raw R).size - 1]? <;>
            aesop
        have h_natDegree : p.val.lastNonzero =
            some ⟨p.val.size - 1, Nat.pred_lt_self (Nat.pos_of_ne_zero h_empty)⟩ := by
          convert Trim.lastNonzero_last_iff (show p.val.size > 0 from Nat.pos_of_ne_zero h_empty)
            |>.2 _
          convert Trim.canonical_iff.mp p.prop using 1
          generalize_proofs at *
          exact ⟨fun h hp => h, fun h => h ‹_›⟩
        -- natDegree is the index of the last non-zero coefficient: p.natDegree = p.val.size - 1.
        have h_natDegree_eq : p.natDegree = p.val.size - 1 := by
          have h_natDegree_eq : p.natDegree = p.val.natDegree := by rfl
          unfold Raw.natDegree at *; aesop
        convert h_last using 1
        · rw [leadingCoeff, Raw.leadingCoeff, p.prop]
          exact id (Eq.symm h_last)
        · exact h_natDegree_eq ▸ rfl

/-- A polynomial equals its leading monomial plus the rest (`erase` at `natDegree`). -/
lemma monomial_add_erase [DecidableEq R] (p : CPolynomial R) :
    p = monomial p.natDegree p.leadingCoeff + erase p.natDegree p := by
  apply CPolynomial.ext
  refine' Eq.symm ( Trim.canonical_ext _ _ _ )
  · exact Trim.trim_twice _
  · exact p.2
  · intro i; simp
    convert Raw.add_coeff_trimmed _ _ i using 1
    rotate_left
    rotate_left
    (expose_names; exact inst_1.toSemiring)
    (expose_names; exact inst)
    (expose_names; exact inst_2)
    exact Raw.monomial p.natDegree p.leadingCoeff;
    exact p.val - Raw.monomial p.natDegree ( p.val.coeff p.natDegree );
    · exact Eq.symm Array.getD_eq_getD_getElem?
    · convert Eq.symm ( add_sub_cancel _ _ ) using 1;
      congr! 1;
      convert Raw.sub_coeff _ _ _ using 1;
      · congr! 1;
        · exact Eq.symm Array.getD_eq_getD_getElem?
        · congr! 1
          congr! 1
          exact leadingCoeff_eq_coeff_natDegree p
      · grind

lemma coeff_neg (p : CPolynomial R) (i : ℕ) : coeff (-p) i = -coeff p i := by
  unfold coeff; exact Raw.neg_coeff p.val i

lemma coeff_sub (p q : CPolynomial R) (i : ℕ) : coeff (p - q) i = coeff p i - coeff q i := by
  unfold coeff; exact Raw.sub_coeff p.val q.val i

theorem neg_add_cancel : -p + p = 0 := by
  apply Subtype.ext
  have dist_lhs : (-p + p).val  = ((-p).val + p.val) := rfl
  rw [dist_lhs]
  exact Raw.neg_add_cancel p.val

instance : AddCommGroup (CPolynomial R) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := by intro a; exact neg_add_cancel a
  nsmul := nsmul -- TODO do we actually need this custom implementation?
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  zsmul := zsmulRec -- TODO do we want a custom efficient implementation?

/-- `CPolynomial R` forms a ring when `R` is a ring.

  The ring structure extends the semiring structure with negation and subtraction.
  Most of the structure is already provided by the `Semiring` instance.
-/
instance [LawfulBEq R] [Nontrivial R] : Ring (CPolynomial R) where
  sub_eq_add_neg := by intro a b; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro p; apply Subtype.ext; rfl
  zsmul_succ' := by intro n p; apply Subtype.ext; rfl
  zsmul_neg' := by intro n p; apply Subtype.ext; rfl
  intCast_ofNat := by intro n; apply Subtype.ext; rfl
  intCast_negSucc := by intro n; apply Subtype.ext; rfl
  neg_add_cancel := by intro p; exact neg_add_cancel p

end Ring

section CommRing

variable [CommRing R] [LawfulBEq R]

/-- `CPolynomial R` forms a commutative ring when `R` is a commutative ring.

  This combines the `CommSemiring` and `Ring` structures.
-/
instance [Nontrivial R] : CommRing (CPolynomial R) where
  -- All structure inherited from `CommSemiring` and `Ring` instances

end CommRing

section Division

variable [Field R] [LawfulBEq R]
variable (p q : CPolynomial R)

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def divByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, by simpa using Trim.trim_twice (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def modByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, by simpa using Trim.trim_twice (Raw.modByMonic p.val q.val)⟩

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.div p.val q.val).trim, by simpa using Trim.trim_twice (Raw.div p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.mod p.val q.val).trim, by simpa using Trim.trim_twice (Raw.mod p.val q.val)⟩

instance : Div (CPolynomial R) := ⟨div⟩
instance : Mod (CPolynomial R) := ⟨mod⟩

end Division

section ModuleTheory

-- The assumptions are requried for `CPolynomial R` to be a module and s0 are necessary downsteam.
variable [Semiring R] [LawfulBEq R]

/-- Scalar multiplication for canonical polynomials: multiply each coefficient by `r`,
then trim to restore canonicity. -/
instance smul : SMul R (CPolynomial R) where
  smul r p := ⟨(Raw.smul r p.val).trim, Trim.trim_twice _⟩

/-- Coefficient of a scalar multiple. -/
lemma coeff_smul (r : R) (p : CPolynomial R) (i : ℕ) :
    coeff (r • p) i = r * coeff p i := by
  show (Raw.smul r p.val).trim.coeff i = r * p.val.coeff i
  rw [Trim.coeff_eq_coeff, Raw.smul_equiv]

lemma smul_zero' (r : R) : r • (0 : CPolynomial R) = 0 := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, coeff_zero]; simp

lemma smul_eq_of_coeff_eq {p q : CPolynomial R}
    (h : Trim.equiv p.val q.val) : p = q := by
  apply CPolynomial.ext
  exact Trim.canonical_ext p.prop q.prop h

lemma smul_add' (r : R) (p q : CPolynomial R) :
    r • (p + q) = r • p + r • q := by
  apply smul_eq_of_coeff_eq; intro i
  show (Raw.smul r (p.val + q.val)).trim.coeff i =
    ((Raw.smul r p.val).trim + (Raw.smul r q.val).trim).coeff i
  rw [Trim.coeff_eq_coeff, smul_equiv, add_coeff_trimmed,
      add_coeff_trimmed, Trim.coeff_eq_coeff, Trim.coeff_eq_coeff,
      smul_equiv, smul_equiv]
  exact Distrib.left_distrib r (p.val.coeff i) (q.val.coeff i)

lemma add_smul' (r s : R) (p : CPolynomial R) :
    (r + s) • p = r • p + s • p := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, coeff_add, coeff_smul, coeff_smul]; grind

lemma zero_smul' (p : CPolynomial R) : (0 : R) • p = 0 := by
  apply smul_eq_of_coeff_eq; intro i
  show (Raw.smul 0 p.val).trim.coeff i = (0 : Raw R).coeff i
  rw [Trim.coeff_eq_coeff, smul_equiv]
  exact MulZeroClass.zero_mul (p.val.coeff i)

lemma one_smul' (p : CPolynomial R) : (1 : R) • p = p := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, _root_.one_mul]

lemma mul_smul' (r s : R) (p : CPolynomial R) :
    (r * s) • p = r • (s • p) := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, coeff_smul, coeff_smul, _root_.mul_assoc]

/-- `CPolynomail` forms a module when R is a semiring. -/
instance : Module R (CPolynomial R) where
  smul:= SMul.smul
  mul_smul := mul_smul'
  one_smul := one_smul'
  smul_zero := smul_zero'
  smul_add := smul_add'
  add_smul := add_smul'
  zero_smul := zero_smul'

/-- This is an R-linear function that returns the cofficient of X^n. -/
def lcoeff (n : ℕ) : (CPolynomial R) →ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

/-- The `R`-submodule of `CPolynomial R` consisting of polynomials of degree ≤ `n`. -/
def degreeLE (n : WithBot ℕ) : Submodule R (CPolynomial R) :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff k)

/-- The `R`-submodule of `CPolynomial R` consisting of polynomials of degree < `n`. -/
def degreeLT (n : ℕ) : Submodule R (CPolynomial R) :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff k)

end ModuleTheory

end CPolynomial

end CompPoly
