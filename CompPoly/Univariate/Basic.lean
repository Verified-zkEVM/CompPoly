/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
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

variable [Semiring R] [LawfulBEq R] [Nontrivial R]
variable (p q r : CPolynomial R)

/-- Addition of canonical polynomials (result is canonical). -/
instance : Add (CPolynomial R) where
  add p q := ⟨p.val + q.val, by apply Trim.trim_twice⟩

omit [Nontrivial R] in
theorem add_comm : p + q = q + p := by
  apply CPolynomial.ext; apply CPolynomial.Raw.add_comm

omit [Nontrivial R] in
theorem add_assoc : p + q + r = p + (q + r) := by
  apply CPolynomial.ext; apply CPolynomial.Raw.add_assoc

instance : Zero (CPolynomial R) := ⟨0, zero_canonical⟩

omit [Nontrivial R] in
theorem zero_add : 0 + p = p := by
  apply CPolynomial.ext
  apply CPolynomial.Raw.zero_add p.val p.prop

omit [Nontrivial R] in
theorem add_zero : p + 0 = p := by
  apply CPolynomial.ext
  apply CPolynomial.Raw.add_zero p.val p.prop

/-- Scalar multiplication by a natural number (result is canonical). -/
def nsmul (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  ⟨CPolynomial.Raw.nsmul n p.val, by apply Trim.trim_twice⟩

omit [Nontrivial R] in
theorem nsmul_zero : nsmul 0 p = 0 := by
  apply CPolynomial.ext; apply CPolynomial.Raw.nsmul_zero

omit [Nontrivial R] in
theorem nsmul_succ (n : ℕ) (p : CPolynomial R) : nsmul (n + 1) p = nsmul n p + p := by
  apply CPolynomial.ext; apply CPolynomial.Raw.nsmul_succ

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

omit [Nontrivial R] in
lemma one_is_trimmed [Nontrivial R] : (1 : CompPoly.CPolynomial.Raw R).trim = 1 :=
  Trim.push_trim #[] 1 one_ne_zero

/-- The constant polynomial 1 is canonical, and is the Unit for multiplication.

  This is `#[1]`, which has no trailing zeros.

  This proof does not work without the assumption that R is non-trivial.
-/
instance [Nontrivial R] : One (CPolynomial R) where
  one := ⟨CPolynomial.Raw.C 1, by exact one_is_trimmed
  ⟩


/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff (p : CPolynomial R) (i : ℕ) : R := p.val.coeff i

/-- The constant polynomial `C r`. -/
def C (r : R) : CPolynomial R := ⟨(Raw.C r).trim, by rw [Trim.trim_twice]⟩

/-- The variable `X`. -/
def X : CPolynomial R := ⟨Raw.X, X_canonical⟩

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

/-- The support of a polynomial: indices with nonzero coefficients. -/
def support (p : CPolynomial R) : Finset ℕ :=
  (Finset.range p.val.size).filter (fun i => p.val.coeff i != 0)

omit [Nontrivial R] in
/-- Coefficient of the constant polynomial `C r`. -/
lemma coeff_C (r : R) (i : ℕ) : coeff (C r) i = if i = 0 then r else 0 := by
  unfold C; simp only [coeff]
  rw [Trim.coeff_eq_coeff, Raw.coeff_C]

/-- Coefficient of the variable `X`. -/
lemma coeff_X (i : ℕ) : coeff X i = if i = 1 then 1 else 0 := by
  simp only [X, coeff]; rw [Raw.coeff_X]

omit [LawfulBEq R] [Nontrivial R] in
/-- Coefficient of the zero polynomial. -/
@[simp]
lemma coeff_zero (i : ℕ) : coeff (0 : CPolynomial R) i = 0 := by
  simp; rfl

/-- Coefficient of the constant polynomial `1`. -/
lemma coeff_one (i : ℕ) :
    coeff (1 : CPolynomial R) i = if i = 0 then 1 else 0 := by
  simp only [coeff]
  change Raw.coeff 1 i = if i = 0 then 1 else 0
  rw [Raw.coeff_one]

theorem coeff_X_mul_succ (p : CPolynomial R) (n : ℕ) : coeff (X * p) (n + 1) = coeff p n := by
  classical
  unfold coeff
  change ((X.val * p.val).coeff (n + 1) = p.val.coeff n)
  rw [Raw.mul_coeff (p := X.val) (q := p.val) (k := n + 1)]
  simp only [X]
  have hmem : (1 : ℕ) ∈ Finset.range (n + 1 + 1) := by
    simp [Finset.mem_range]
  have hsum :
      (Finset.range (n + 1 + 1)).sum (fun i => Raw.X.coeff i * p.val.coeff (n + 1 - i)) =
        Raw.X.coeff 1 * p.val.coeff (n + 1 - 1) := by
    refine Finset.sum_eq_single_of_mem (a := 1) hmem ?_
    intro i hi hne
    rw [Raw.coeff_X (R := R) i]
    simp [hne]
  rw [hsum]
  have hn : n + 1 - 1 = n := by
    omega
  rw [hn]
  rw [Raw.coeff_X (R := R) 1]
  simp

theorem coeff_X_mul_zero (p : CPolynomial R) : coeff (X * p) 0 = 0 := by
  unfold CPolynomial.coeff
  change ((Raw.X * p.val) : Raw R).coeff 0 = 0
  rw [Raw.mul_coeff]
  -- (Finset.range 1).sum ... reduces to the single term at 0
  simp [Raw.X]

theorem coeff_extract_succ (a : CPolynomial.Raw R) (i : ℕ) : CPolynomial.Raw.coeff (a.extract 1 a.size) i = CPolynomial.Raw.coeff a (i + 1) := by
  simp [CPolynomial.Raw.coeff, Array.getElem?_extract]
  by_cases h : i < a.size - 1
  · have h1 : 1 + i = i + 1 := by omega
    simp [h, h1]
  · have hge : a.size ≤ i + 1 := by omega
    simp [h, Array.getElem?_eq_none (xs := a) (i := i + 1) hge]

def tail (p : CPolynomial R) : CPolynomial R :=
  ⟨CPolynomial.Raw.trim (p.val.extract 1 p.val.size), by
    simpa using (CPolynomial.Raw.Trim.trim_twice (p.val.extract 1 p.val.size))⟩

theorem coeff_tail (p : CPolynomial R) (i : ℕ) : coeff (tail p) i = coeff p (i + 1) := by
  -- LHS: coeff of tail = coeff of trimmed extract
  unfold tail
  -- turn coefficients of CPolynomial into raw coefficients
  simp only [CPolynomial.coeff]
  -- remove the trim on coefficients
  have htrim :=
    (CPolynomial.Raw.Trim.coeff_eq_coeff
      (p := ((↑p : CPolynomial.Raw R).extract 1 (↑p : CPolynomial.Raw R).size)) (i := i))
  -- shift the extract
  exact htrim.trans (coeff_extract_succ (a := (↑p : CPolynomial.Raw R)) (i := i))


theorem eq_C_add_X_mul_tail (p : CPolynomial R) : p = C (coeff p 0) + X * tail p := by
  classical
  apply CPolynomial.ext
  refine CPolynomial.Raw.Trim.canonical_ext (p := p.val)
      (q := (C (coeff p 0) + X * tail p).val) ?_ ?_ ?_
  · exact p.property
  · exact (C (coeff p 0) + X * tail p).property
  · intro k
    change coeff p k = coeff (C (coeff p 0) + X * tail p) k

    have coeff_add (a b : CPolynomial R) (i : ℕ) :
        coeff (a + b) i = coeff a i + coeff b i := by
      unfold coeff
      change ((a.val + b.val).coeff i) = a.val.coeff i + b.val.coeff i
      simpa using
        (CPolynomial.Raw.add_coeff_trimmed (p := a.val) (q := b.val) (i := i))

    cases k with
    | zero =>
        rw [coeff_add (a := C (coeff p 0)) (b := X * tail p) (i := 0)]
        have hC0 : coeff (C (coeff p 0)) 0 = coeff p 0 := by
          simpa using (coeff_C (R := R) (r := coeff p 0) (i := 0))
        have hX0 : coeff (X * tail p) 0 = 0 := by
          simpa using (coeff_X_mul_zero (R := R) (p := tail p))
        rw [hC0, hX0]
        simp only [_root_.add_zero]
    | succ n =>
        rw [coeff_add (a := C (coeff p 0)) (b := X * tail p) (i := n + 1)]
        have hCsucc : coeff (C (coeff p 0)) (n + 1) = 0 := by
          simpa [Nat.succ_ne_zero n] using
            (coeff_C (R := R) (r := coeff p 0) (i := n + 1))
        have hXsucc : coeff (X * tail p) (n + 1) = coeff (tail p) n := by
          simpa using (coeff_X_mul_succ (R := R) (p := tail p) (n := n))
        have htail : coeff (tail p) n = coeff p (n + 1) := by
          simpa using (coeff_tail (p := p) (i := n))
        rw [hCsucc, hXsucc, htail]
        simp only [_root_.zero_add]

theorem tail_size_lt (p : CPolynomial R) (hp : p.val.size > 0) : (tail p).val.size < p.val.size := by
  unfold tail
  have hle : (CPolynomial.Raw.trim (p.val.extract 1 p.val.size)).size
      ≤ (p.val.extract 1 p.val.size).size := by
    simpa using (CPolynomial.Raw.Trim.size_le_size (p := p.val.extract 1 p.val.size))
  have hextract : (p.val.extract 1 p.val.size).size = p.val.size - 1 := by
    simpa [Array.size_extract, Nat.succ_le_of_lt hp]
  have hle' : (CPolynomial.Raw.trim (p.val.extract 1 p.val.size)).size ≤ p.val.size - 1 := by
    simpa [hextract] using hle
  exact lt_of_le_of_lt hle' (Nat.pred_lt_self hp)

theorem induction_on {P : CPolynomial R → Prop} (p : CPolynomial R)
    (h0 : P 0) (hC : ∀ a, P (C a)) (hadd : ∀ p q, P p → P q → P (p + q))
    (hX : ∀ p, P p → P (X * p)) : P p := by
  classical
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
        apply CompPoly.CPolynomial.ext
        simpa using hval
      simpa [hp0] using h0
  | succ n =>
      have hp_pos : p.val.size > 0 := by
        simpa [hn] using Nat.succ_pos n
      have htail_lt : (tail p).val.size < Nat.succ n := by
        have ht := tail_size_lt (p := p) hp_pos
        simpa [hn] using ht
      have htail : P (tail p) := ih (tail p).val.size htail_lt (tail p) rfl
      have hXt : P (X * tail p) := hX (tail p) htail
      have hC0 : P (C (coeff p 0)) := hC (coeff p 0)
      have hsum : P (C (coeff p 0) + X * tail p) := hadd _ _ hC0 hXt
      -- Rewrite using Horner decomposition
      rw [eq_C_add_X_mul_tail (p := p)]
      exact hsum


/-- Degree equals the maximum of the support when the polynomial is non-zero.
  Here `p.degree = some n` where `n` is the maximum index in `p.support`. -/
lemma degree_eq_support_max (p : CPolynomial R) (hp : p ≠ 0) :
    ∃ n, n ∈ p.support ∧ p.degree = n := by
  sorry

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
  exact CPolynomial.Raw.mul_assoc p.val q.val r.val

lemma zero_mul (p : CPolynomial R) : 0 * p = 0 := by
  apply Subtype.ext
  exact CPolynomial.Raw.zero_mul p.val

lemma mul_zero (p : CPolynomial R) : p * 0 = 0 := by
  apply Subtype.ext
  exact CPolynomial.Raw.mul_zero p.val

lemma left_distrib (p q r : CPolynomial R) : p * (q + r) = p * q + p * r := by
  apply Subtype.ext
  exact CPolynomial.Raw.left_distrib p.val q.val r.val

lemma right_distrib (p q r : CPolynomial R) : (p + q) * r = p * r + q * r := by
  apply Subtype.ext
  exact CPolynomial.Raw.right_distrib p.val q.val r.val

omit [LawfulBEq R] in
lemma pow_zero (p : CompPoly.CPolynomial.Raw R) :
    p ^ 0 = CompPoly.CPolynomial.Raw.C 1 := by
      exact rfl

omit [LawfulBEq R]
lemma pow_succ (p : CompPoly.CPolynomial.Raw R) (n : ℕ) :
    p ^ (n + 1) = p * (p ^ n) := by
      convert ( Function.iterate_succ_apply' ( mul p ) n ( CompPoly.CPolynomial.Raw.C 1 ) )
           using 1

lemma pow_is_trimmed [LawfulBEq R] [Nontrivial R]
    (p : CompPoly.CPolynomial.Raw R) (n : ℕ) : (p ^ n).trim = p ^ n := by
      induction' n with n ih generalizing p;
      · convert one_is_trimmed
        · infer_instance
        · infer_instance
      · have h_exp : p ^ (n + 1) = p * p ^ n := by
          exact pow_succ p n
        rw [h_exp]
        convert mul_is_trimmed p ( p ^ n ) using 1

lemma pow_succ_right [LawfulBEq R] [Nontrivial R]
    (p : CompPoly.CPolynomial.Raw R) (n : ℕ) : p ^ (n + 1) = p ^ n * p := by
      convert pow_succ p n using 1;
      induction' n with n ih;
      · have h_pow_zero : p ^ 0 = 1 := by
          exact rfl
        rw [ h_pow_zero, mul_one_trim, one_mul_trim ];
      · simp_all +decide [ pow_succ ];
        convert CPolynomial.Raw.mul_assoc p ( p ^ n ) p using 1;
        grind

/-- `CPolynomial R` forms a semiring when `R` is a semiring.

  The semiring structure extends the `AddCommGroup` structure with multiplication.
  All operations preserve the canonical property (no trailing zeros).

  TODO: Complete all the required proofs for the semiring axioms.
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
  left_distrib := by intro p q r; exact left_distrib p q r
  right_distrib := by  intro p q r; exact right_distrib p q r
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  npow n p := ⟨p.val ^ n, by apply CompPoly.CPolynomial.pow_is_trimmed⟩
  npow_zero := by intro x; apply Subtype.ext; rfl
  npow_succ := by intro n p; apply Subtype.ext; exact
      (CompPoly.CPolynomial.pow_succ_right p.val n)
  natCast_zero := by rfl
  natCast_succ := by intro n; rfl

/-- `C r * X^n = monomial n r` as canonical polynomials. -/
lemma C_mul_X_pow_eq_monomial [LawfulBEq R] [DecidableEq R] [Nontrivial R] (r : R) (n : ℕ) :
    (C r : CPolynomial R) * (X ^ n) = monomial n r := by sorry

end Semiring

section CommSemiring

variable [CommSemiring R] [LawfulBEq R]
variable (p q : CPolynomial R)

lemma mul_comm (p q : CPolynomial R) : p * q = q * p := by
  apply Subtype.ext
  have dist_lhs : (p * q : CPolynomial R) = (p.val * q.val : CPolynomial.Raw R) := rfl
  have dist_rhs : (q * p : CPolynomial R) = (q.val * p.val : CPolynomial.Raw R) := rfl
  rw [dist_lhs, dist_rhs]
  exact CPolynomial.Raw.mul_comm p.val q.val

/-- `CPolynomial R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommSemiring R] [Nontrivial R] : CommSemiring (CPolynomial R) where
  mul_comm := by intro p q; exact mul_comm p q

end CommSemiring

section Ring

variable [Ring R] [LawfulBEq R] [Nontrivial R]
variable (p q : CPolynomial R)

instance : Neg (CPolynomial R) where
  neg p := ⟨-p.val, neg_trim p.val p.prop⟩

instance : Sub (CPolynomial R) where
  sub p q := p + -q

 omit [Nontrivial R] in
lemma erase_canonical [DecidableEq R] (n : ℕ) (p : CPolynomial R) :
    let e := p.val - CPolynomial.Raw.monomial n (p.val.coeff n)
    e.trim = e := by
  simp; apply Trim.trim_twice

/-- Erase the coefficient at index `n` (same as `p` except `coeff n = 0`, then trimmed). -/
def erase [DecidableEq R] (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  let e := p.val - CPolynomial.Raw.monomial n (p.val.coeff n)
  ⟨e, by rw [erase_canonical]⟩

/-- A polynomial equals its leading monomial plus the rest (`erase` at `natDegree`). -/
lemma monomial_add_erase [DecidableEq R] (p : CPolynomial R) :
    p = monomial p.natDegree p.leadingCoeff + erase p.natDegree p := by
  apply CPolynomial.ext

  sorry

omit [Nontrivial R] in
theorem neg_add_cancel : -p + p = 0 := by
  apply Subtype.ext
  let R' : Ring R := ‹Ring R›
  have dist_lhs : (-p + p).val  = ((-p).val + p.val) := rfl
  rw [dist_lhs]
  exact CPolynomial.Raw.neg_add_cancel p.val

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

end CPolynomial

end CompPoly
