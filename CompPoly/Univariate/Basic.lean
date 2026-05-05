/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Desmond Coles
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Raw.Proofs
import CompPoly.Univariate.Raw.Division

/-!
  # Computable Univariate Polynomials

  This file defines `CPolynomial R`, the type of canonical univariate polynomials.
  Canonicality is tracked semantically by requiring the last stored coefficient, when present,
  to be nonzero.

  This provides a unique representation for each polynomial, enabling stronger extensionality
  properties compared to the raw `CPolynomial.Raw` type.
-/
namespace CompPoly

open CPolynomial.Raw

variable {R : Type*}

/-- Computable univariate polynomials are represented canonically with no trailing zeros.

  A polynomial `p : CPolynomial.Raw R` is canonical if its last stored coefficient is nonzero
  whenever the underlying array is nonempty. This gives an instance-stable carrier while keeping
  the raw normalization algorithms available separately.

  TODO optimizations may be had by trimming only at the end of iterative operations
-/
def CPolynomial (R : Type*) [Zero R] := { p : CPolynomial.Raw R // IsCanonical p }

namespace CPolynomial

section ZeroOnly

/-- Extensionality for canonical polynomials. -/
@[ext] theorem ext [Zero R] {p q : CPolynomial R} (h : p.val = q.val) : p = q := by
  exact Subtype.ext h

/-- Canonical polynomials coerce to raw polynomials. -/
instance [Zero R] : Coe (CPolynomial R) (CPolynomial.Raw R) where coe := Subtype.val

/-- The zero polynomial is canonical without any normalization assumptions. -/
instance [Zero R] : Zero (CPolynomial R) := ⟨⟨#[], Trim.isCanonical_empty⟩⟩

/-- The zero polynomial provides the inhabited instance. -/
instance [Zero R] : Inhabited (CPolynomial R) := ⟨0⟩

/-- `CPolynomial R` has `BEq` when `R` does, comparing the underlying coefficient arrays. -/
instance (R : Type*) [Zero R] [BEq R] : BEq (CPolynomial R) where
  beq p q := p.val == q.val

/-- `CPolynomial R` has `LawfulBEq` when `R` does: `p == q` iff `p = q`. -/
instance (R : Type*) [Zero R] [BEq R] [LawfulBEq R] : LawfulBEq (CPolynomial R) where
  rfl := by
    have h_raw : ∀ (a : CPolynomial.Raw R), a == a ↔ a = a := by
      aesop
    convert h_raw _
    swap
    exact #[]
    simp +decide [ BEq.beq ]
  eq_of_beq h := Subtype.ext (LawfulBEq.eq_of_beq h)

/-- `CPolynomial R` has `DecidableEq` when `R` does, via the underlying `Array R` representation. -/
instance (R : Type*) [Zero R] [DecidableEq R] : DecidableEq (CPolynomial R) :=
  @Subtype.instDecidableEq
    (CPolynomial.Raw R)
    (fun p => IsCanonical p)
    inferInstance

end ZeroOnly

section Operations

/-- Canonical computable polynomials are trim-stable. -/
@[simp] theorem trim_eq [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p.val.trim = p.val :=
  Trim.trim_eq_of_isCanonical p.property

/-- Addition of canonical polynomials (result is canonical). -/
instance [Semiring R] [BEq R] [LawfulBEq R] : Add (CPolynomial R) where
  add p q := ⟨p.val + q.val,
    Trim.isCanonical_of_trim_eq (by
      simpa [Raw.add] using Trim.trim_twice (Raw.addRaw p.val q.val))⟩

theorem add_comm [Semiring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : p + q = q + p := by
  apply CPolynomial.ext
  simpa using (Raw.add_comm p.val q.val)

theorem add_assoc [Semiring R] [BEq R] [LawfulBEq R]
    (p q r : CPolynomial R) : p + q + r = p + (q + r) := by
  apply CPolynomial.ext
  simpa using (Raw.add_assoc p.val q.val r.val)

theorem zero_add [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : 0 + p = p := by
  apply CPolynomial.ext
  simpa using (Raw.zero_add p.val (trim_eq p))

theorem add_zero [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p + 0 = p := by
  apply CPolynomial.ext
  simpa using (Raw.add_zero p.val (trim_eq p))

/-- Scalar multiplication by a natural number (result is canonical). -/
def nsmul [Semiring R] [BEq R] [LawfulBEq R] (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  ⟨Raw.nsmul n p.val,
    Trim.isCanonical_of_trim_eq (by
      simpa [Raw.nsmul] using Trim.trim_twice (Raw.nsmulRaw n p.val))⟩

theorem nsmul_zero [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : nsmul 0 p = 0 := by
  apply CPolynomial.ext
  simpa using (Raw.nsmul_zero p.val)

theorem nsmul_succ [Semiring R] [BEq R] [LawfulBEq R]
    (n : ℕ) (p : CPolynomial R) : nsmul (n + 1) p = nsmul n p + p := by
  apply CPolynomial.ext
  simpa using (Raw.nsmul_succ n (p := p.val))

instance [Semiring R] [BEq R] [LawfulBEq R] : AddCommSemigroup (CPolynomial R) where
  add_assoc := add_assoc
  add_comm := add_comm

/-- Multiplication of canonical polynomials.

  The product of two canonical polynomials is canonical because multiplication
  preserves the "no trailing zeros" property.
-/
instance [Semiring R] [BEq R] [LawfulBEq R] : Mul (CPolynomial R) where
  mul p q :=
    ⟨p.val * q.val, Trim.isCanonical_of_trim_eq (mul_is_trimmed p.val q.val)⟩

lemma one_is_trimmed [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial.Raw R).trim = 1 :=
  Trim.push_trim #[] 1 one_ne_zero

/-- The constant polynomial 1 is canonical, and is the Unit for multiplication.

  This is `#[1]`, which has no trailing zeros.

  This proof does not work without the assumption that R is non-trivial.
-/
instance [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : One (CPolynomial R) where
  one := ⟨Raw.C 1, Trim.isCanonical_of_trim_eq one_is_trimmed⟩

instance [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : Nontrivial (CPolynomial R) where
  exists_pair_ne := ⟨0, 1, by
    intro h
    have := congr_arg (fun p : CPolynomial R => p.val.size) h
    simp at this
    exact Nat.zero_ne_one this⟩

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff [Zero R] (p : CPolynomial R) (i : ℕ) : R := p.val.coeff i

/-- The constant polynomial `C r`. -/
def C [Zero R] [BEq R] [LawfulBEq R] (r : R) : CPolynomial R :=
  ⟨(Raw.C r).trim, Trim.isCanonical_trim (Raw.C r)⟩

/-- The variable `X`. -/
def X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : CPolynomial R :=
  ⟨Raw.X, Trim.isCanonical_of_trim_eq X_canonical⟩

/-- Construct a canonical monomial `c * X^n` as a `CPolynomial R`.

  The result is canonical (no trailing zeros) when `c ≠ 0`.
  For example, `monomial 2 3` represents `3 * X^2`.

  Note: If `c = 0`, this returns `0` (the zero polynomial).
-/
def monomial [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (c : R) : CPolynomial R :=
  ⟨Raw.monomial n c, Trim.isCanonical_of_trim_eq (Raw.monomial_canonical n c)⟩

/-- Return the degree of a `CPolynomial`. -/
def degree [Zero R] (p : CPolynomial R) : WithBot ℕ :=
  match p.val.size with
  | 0 => ⊥
  | .succ n => n

/-- Natural number degree of a canonical polynomial.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree [Zero R] (p : CPolynomial R) : ℕ :=
  match p.val.size with
  | 0 => 0
  | .succ n => n

/-- Return the leading coefficient of a `CPolynomial` as the last coefficient
of the trimmed array, or `0` if the trimmed array is empty. -/
def leadingCoeff [Zero R] (p : CPolynomial R) : R := p.val.getLastD 0

/-- Evaluate a polynomial at a point. -/
def eval [Semiring R] (x : R) (p : CPolynomial R) : R :=
  p.val.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + a * x ^ i) 0

/-- Evaluate at `x : S` via a ring hom
`f : R →+* S`; `eval₂ f x p = f(a₀) + f(a₁)*x + f(a₂)*x² + ...`. -/
def eval₂ {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) : S :=
  p.val.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluate at `x : S` via a ring hom using Horner's method. -/
@[inline, specialize]
def eval₂Horner {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) : S :=
  p.val.eval₂Horner f x

/-- Evaluate a polynomial at a point using Horner's method. -/
@[inline, specialize]
def evalHorner [Semiring R] (x : R) (p : CPolynomial R) : R :=
  p.eval₂Horner (RingHom.id R) x

/-- Horner evaluation agrees with the sum-of-powers evaluation. -/
theorem eval₂_eq_eval₂_horner {S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂ f x p = eval₂Horner f x p :=
  CPolynomial.Raw.eval₂_eq_eval₂Horner f x p.val

/-- Horner evaluation agrees with the sum-of-powers evaluation. -/
theorem eval_eq_eval_horner [Semiring R] (x : R) (p : CPolynomial R) :
    eval x p = evalHorner x p := by
  simpa [eval, evalHorner, eval₂, eval₂Horner] using
    (eval₂_eq_eval₂_horner (f := RingHom.id R) (x := x) (p := p))

/-- Horner evaluation agrees with the sum-of-powers evaluation. -/
theorem eval_horner_eq_eval [Semiring R] (x : R) (p : CPolynomial R) :
    evalHorner x p = eval x p :=
  (eval_eq_eval_horner x p).symm

/-- The support of a polynomial: indices with nonzero coefficients. -/
def support [Zero R] [BEq R] (p : CPolynomial R) : Finset ℕ :=
  (Finset.range p.val.size).filter (fun i => p.val.coeff i != 0)

/-- Number of coefficients (length of the underlying array). -/
def size [Zero R] (p : CPolynomial R) : ℕ := p.val.size

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound [Zero R] (p : CPolynomial R) : WithBot Nat := p.degree

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound [Zero R] (p : CPolynomial R) : Nat := p.natDegree

/-- Check if a `CPolynomial` is monic, i.e. its leading coefficient is 1. -/
def monic [Zero R] [One R] [BEq R] (p : CPolynomial R) : Bool := p.leadingCoeff == 1

/-- The polynomial with the constant term removed; `coeff (divX p) i = coeff p (i + 1)`. -/
def divX [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : CPolynomial R :=
  let q : CPolynomial.Raw R := p.val.extract 1 p.val.size
  ⟨q.trim, Trim.isCanonical_trim q⟩

/-- Coefficient of the constant polynomial `C r`. -/
lemma coeff_C [Zero R] [BEq R] [LawfulBEq R] (r : R) (i : ℕ) :
    coeff (C r) i = if i = 0 then r else 0 := by
  unfold coeff C
  rw [Trim.coeff_eq_coeff]
  unfold Raw.C Raw.coeff
  split_ifs with h <;> simp [h]

/-- Coefficient of the variable `X`. -/
lemma coeff_X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (i : ℕ) :
    coeff X i = if i = 1 then 1 else 0 := by
  unfold coeff X Raw.X Raw.coeff
  rcases i with (_ | _ | i) <;> rfl

/-- Coefficient of the zero polynomial. -/
@[simp]
lemma coeff_zero [Zero R] (i : ℕ) : coeff (0 : CPolynomial R) i = 0 := by
  change (#[].getD i 0) = 0
  simp

/-- Coefficient of the constant polynomial `1`. -/
lemma coeff_one [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (i : ℕ) :
    coeff (1 : CPolynomial R) i = if i = 0 then 1 else 0 := by
  simpa [coeff] using (Raw.coeff_one (R := R) i)

/-- Coefficient of a sum. -/
lemma coeff_add [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (i : ℕ) : coeff (p + q) i = coeff p i + coeff q i := by
  unfold coeff; exact Raw.add_coeff_trimmed p.val q.val i

/-- Coefficient of a monomial. -/
lemma coeff_monomial [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n i : ℕ) (c : R) :
    coeff (monomial n c) i = if i = n then c else 0 := by
  unfold coeff monomial; rw [Raw.coeff_monomial]; simp only [eq_comm]

/-- Coefficient of a product (convolution sum). -/
lemma coeff_mul [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (k : ℕ) :
    coeff (p * q) k = (Finset.range (k + 1)).sum (fun i => coeff p i * coeff q (k - i)) := by
  unfold coeff; exact Raw.mul_coeff p.val q.val k

/-- Two polynomials are equal iff they have the same coefficients. -/
theorem eq_iff_coeff [Zero R] [BEq R] [LawfulBEq R] {p q : CPolynomial R} :
    p = q ↔ ∀ i, coeff p i = coeff q i := by
  constructor
  · intro h i; rw [h]
  · intro h; apply ext; exact Trim.isCanonical_ext p.property q.property (fun i => h i)

/-- Monomials are additive in their coefficient. -/
theorem monomial_add [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (a b : R) :
    monomial n (a + b) = monomial n a + monomial n b := by
  apply (eq_iff_coeff).2
  intro i
  rw [coeff_monomial, coeff_add, coeff_monomial, coeff_monomial]
  split_ifs <;> simp_all

/-- Zero characterization: `p = 0` iff all coefficients are zero. -/
theorem eq_zero_iff_coeff_zero [Zero R] [BEq R] [LawfulBEq R] {p : CPolynomial R} :
    p = 0 ↔ ∀ i, coeff p i = 0 := by
  rw [eq_iff_coeff]; simp only [coeff_zero]

/-- An index is in the support iff the coefficient there is nonzero. -/
lemma mem_support_iff [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    i ∈ p.support ↔ coeff p i ≠ 0 := by
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
theorem support_empty_iff [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.support = ∅ ↔ p = 0 := by
  rw [eq_zero_iff_coeff_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h i; by_contra hne; exact h i ((mem_support_iff p i).mpr hne)
  · intro h i; rw [mem_support_iff, h]; simp

/-- Evaluation equals the sum over support of coefficients times powers. -/
theorem eval_eq_sum_support [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) (x : R) :
    p.eval x = p.support.sum (fun i => p.coeff i * x ^ i) := by
  have h_eval_def : p.eval x =
      (p.val.zipIdx.toList.map (fun ⟨a, i⟩ => a * x ^ i)).sum := by
    unfold CPolynomial.eval
    simp +decide
    induction p.val
    simp +decide [ * ]
    induction' ‹List R› using List.reverseRecOn with a l ih <;>
      simp +decide [ *, List.zipIdx_append ]
  have h_sum_range : (p.val.zipIdx.toList.map (fun ⟨a, i⟩ => a * x ^ i)).sum =
      (Finset.range p.val.size).sum (fun i => p.val.coeff i * x ^ i) := by
    convert CPolynomial.Raw.sum_zipIdx_eq_sum_range p.val (fun a i => a * x ^ i)
      using 1
  convert h_eval_def.trans h_sum_range using 1
  refine' Finset.sum_subset _ _ <;> intro i hi <;>
    simp_all +decide [ CPolynomial.Raw.coeff ]
  · exact Finset.mem_range.mp (Finset.mem_filter.mp hi |>.1)
  · unfold CPolynomial.support
    aesop

/--
Evaluation via a ring hom equals the sum over support of mapped coefficients times powers.
-/
theorem eval₂_eq_sum_support {S : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Semiring S]
    (f : R →+* S) (p : CPolynomial R) (x : S) :
    p.eval₂ f x = p.support.sum (fun i => f (p.coeff i) * x ^ i) := by
  have h_eval_def : p.eval₂ f x =
      (p.val.zipIdx.toList.map (fun ⟨a, i⟩ => f a * x ^ i)).sum := by
    unfold CPolynomial.eval₂
    simp +decide
    induction p.val
    simp +decide [*]
    induction' ‹List R› using List.reverseRecOn with a l ih <;>
      simp +decide [*, List.zipIdx_append]
  have h_sum_range : (p.val.zipIdx.toList.map (fun ⟨a, i⟩ => f a * x ^ i)).sum =
      (Finset.range p.val.size).sum (fun i => f (p.val.coeff i) * x ^ i) := by
    convert CPolynomial.Raw.sum_zipIdx_eq_sum_range p.val (fun a i => f a * x ^ i)
      using 1
  convert h_eval_def.trans h_sum_range using 1
  refine' Finset.sum_subset _ _ <;> intro i hi <;>
    simp_all +decide [CPolynomial.Raw.coeff]
  · exact Finset.mem_range.mp (Finset.mem_filter.mp hi |>.1)
  · unfold CPolynomial.support
    aesop

lemma coeff_C_mul [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (c : R) :
    ∀ i, coeff ((C c) * p) i = c * (coeff p i) := by
  intros i
  rw [coeff_mul, Finset.sum_eq_single 0]
  · simp only [coeff_C, ↓reduceIte, tsub_zero]
  · intros b _ h
    simp only [coeff_C, ↓reduceIte, h, NonUnitalNonAssocSemiring.zero_mul]
  · simp

/-- Lemmas on coefficients and multiplication by `X`. -/
lemma coeff_X_mul_succ [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (n : ℕ) :
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

lemma coeff_X_mul_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : coeff (X * p) 0 = 0 := by
  unfold coeff
  change ((Raw.X * p.val) : Raw R).coeff 0 = 0
  rw [Raw.mul_coeff]
  -- (Finset.range 1).sum ... reduces to the single term at 0
  simp [Raw.X]

theorem coeff_mul_X_succ [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (n : ℕ) :
    coeff (p * X) (n + 1) = coeff p n := by
  unfold coeff
  change ((p.val * X.val).coeff (n + 1) = p.val.coeff n)
  rw [Raw.mul_coeff]
  simp only [X]
  have hmem : n ∈ Finset.range (n + 1 + 1) := by
    simp [Finset.mem_range]
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

theorem coeff_mul_X_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : coeff (p * X) 0 = 0 := by
  rw [coeff_mul]
  simp [X, Raw.X]

lemma coeff_extract_succ [Zero R] (a : CPolynomial.Raw R) (i : ℕ) :
    Raw.coeff (a.extract 1 a.size) i = Raw.coeff a (i + 1) := by
  simp [Raw.coeff, Array.getElem?_extract]
  by_cases h : i < a.size - 1
  · have h1 : 1 + i = i + 1 := by omega
    simp [h, h1]
  · have hge : a.size ≤ i + 1 := by omega
    simp [h, Array.getElem?_eq_none (xs := a) (i := i + 1) hge]

lemma coeff_divX [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    coeff (divX p) i = coeff p (i + 1) := by
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

lemma X_mul_divX_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : p = X * divX p + C (coeff p 0) := by
  apply CPolynomial.ext
  rw [add_comm]
  refine Trim.isCanonical_ext (p := p.val)
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
        rw [_root_.add_zero]
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
        rw [_root_.zero_add]

theorem divX_mul_X_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : divX p * X + C (p.coeff 0) = p := by
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
        and_false, ↓reduceIte]
      rw [_root_.add_zero]
      simpa using (coeff_divX (p := p) (i := n))

lemma divX_size_lt [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) (hp : p.val.size > 0) :
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
theorem induction_on [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {P : CPolynomial R → Prop} (p : CPolynomial R)
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

/- Auxiliary lemmas for `degree_eq_support_max`: relating `degree`, `support`, and `lastNonzero`. -/
/-- Lemma for `degree_eq_support_max`: degree in terms of `lastNonzero`. -/
lemma degree_eq_support_max_aux_degree [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) {k : Fin p.val.size}
    (hk : p.val.lastNonzero = some k) : p.degree = k.val := by
  have hp : p.val.size > 0 := by
    exact lt_of_lt_of_le (Nat.succ_pos _) (Nat.succ_le_of_lt k.is_lt)
  have hlast :
      p.val.lastNonzero = some ⟨p.val.size - 1, Nat.pred_lt_self hp⟩ := by
    exact (Trim.canonical_nonempty_iff (p := p.val) hp).mp (trim_eq p)
  have hkEq : k = ⟨p.val.size - 1, Nat.pred_lt_self hp⟩ := by
    apply Option.some.inj
    exact hk.symm.trans hlast
  have hkVal : k.val = p.val.size - 1 := by
    simpa using congrArg Fin.val hkEq
  have hs : p.val.size = k.val + 1 := by omega
  simp [CPolynomial.degree, hs]

lemma degree_eq_support_max_aux_lastNonzero [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (hp : p ≠ 0) :
    ∃ k : Fin p.val.size, p.val.lastNonzero = some k := by
  cases hln : p.val.lastNonzero with
  | some k =>
      exact ⟨k, rfl⟩
  | none =>
      have htrim : p.val.trim = (#[] : CPolynomial.Raw R) := by
        simp [Raw.trim, hln]
      have hval : p.val = (#[] : CPolynomial.Raw R) := by
        have htrim' := htrim
        rw [trim_eq p] at htrim'
        exact htrim'
      have hp0 : p = 0 := by
        apply Subtype.ext
        simpa using hval
      exact (hp hp0).elim

lemma degree_eq_support_max_aux_mem_support [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) {k : Fin p.val.size}
    (hk : p.val.lastNonzero = some k) : k.val ∈ p.support := by
  unfold CPolynomial.support
  rcases k with ⟨k, hklt⟩
  refine (Finset.mem_filter).2 ?_
  refine ⟨?_, ?_⟩
  · exact Finset.mem_range.2 hklt
  · have hnonzeroFin : p.val[(⟨k, hklt⟩ : Fin p.val.size)] ≠ (0 : R) := by
        simpa using (Trim.lastNonzero_spec (p := p.val) (k := ⟨k, hklt⟩) hk).1
    have hnonzero : p.val[k]'hklt ≠ (0 : R) := by
      simpa using hnonzeroFin
    have hcoeff_ne : p.val.coeff k ≠ (0 : R) := by
      have hcoeff : p.val.coeff k = p.val[k]'hklt := by
        simpa using (Trim.coeff_eq_getElem (p := p.val) (i := k) hklt)
      simpa [hcoeff] using hnonzero
    exact bne_iff_ne.mpr hcoeff_ne

/-- Degree equals the maximum of the support when the polynomial is non-zero.
  Here `p.degree = some n` where `n` is the maximum index in `p.support`. -/
theorem degree_eq_support_max [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (hp : p ≠ 0) :
    ∃ n, n ∈ p.support ∧ p.degree = n := by
  obtain ⟨k, hk⟩ := degree_eq_support_max_aux_lastNonzero (p := p) hp
  refine ⟨k.val, ?_⟩
  constructor
  · exact degree_eq_support_max_aux_mem_support (p := p) hk
  · exact degree_eq_support_max_aux_degree (p := p) hk

/-- When `p ≠ 0`, `degree p` equals `natDegree p` (as `WithBot ℕ`). -/
theorem degree_eq_natDegree [Zero R] (p : CPolynomial R) (hp : p ≠ 0) :
    p.degree = p.natDegree := by
  cases hs : p.val.size with
  | zero =>
      have hval : p.val = (#[] : CPolynomial.Raw R) := Array.eq_empty_of_size_eq_zero hs
      apply (hp ?_).elim
      apply CPolynomial.ext
      simpa using hval
  | succ n =>
      have hdeg : p.degree = n := by simp [CPolynomial.degree, hs]
      have hnat : p.natDegree = n := by simp [CPolynomial.natDegree, hs]
      rw [hdeg, hnat]

/-- Lemma for computing the degree of 0 in proofs. -/
lemma degree_zero [Zero R] : degree (0 : CPolynomial R) = ⊥ := by
  rfl

/-- The natural degree is the maximum element of the support. -/
theorem natDegree_eq_support_sup [Zero R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.natDegree = p.support.sup (fun n => n) := by
  cases hs : p.val.size with
  | zero =>
      have hval : p.val = (#[] : CPolynomial.Raw R) := Array.eq_empty_of_size_eq_zero hs
      rw [CPolynomial.natDegree, CPolynomial.support, hval]
      rfl
  | succ n =>
      have hp : p.val.size > 0 := by simp [hs]
      have hp' : n < p.val.size := by
        simp [hs]
      have hnat : p.natDegree = n := by
        simp [CPolynomial.natDegree, hs]
      have hlast :
          p.val.lastNonzero = some ⟨n, hp'⟩ := by
        simpa [hs] using (Trim.canonical_nonempty_iff (p := p.val) hp).mp (trim_eq p)
      have hspec := Trim.lastNonzero_spec (p := p.val) (k := ⟨n, hp'⟩) hlast
      have hn_mem : n ∈ p.support := by
        exact degree_eq_support_max_aux_mem_support (p := p) hlast
      have hle : ∀ m, m ∈ p.support → m ≤ n := by
        intro m hm
        have hm_lt : m < p.val.size := (Finset.mem_filter.mp hm).1 |> Finset.mem_range.mp
        by_cases hmn : m ≤ n
        · exact hmn
        · have hm_gt : m > n := Nat.lt_of_not_ge hmn
          have hm_zero : p.val[m] = 0 := hspec.2 m hm_lt hm_gt
          have hm_nonzero : p.val.coeff m ≠ 0 := (CPolynomial.mem_support_iff p m).mp hm
          have hcoeff : p.val.coeff m = p.val[m] := by
            simpa using (Trim.coeff_eq_getElem (p := p.val) (i := m) hm_lt)
          exact (hm_nonzero (hcoeff.trans hm_zero)).elim
      rw [hnat]
      apply le_antisymm
      · simpa using (Finset.le_sup (f := fun m => m) hn_mem)
      · exact Finset.sup_le fun m hm => hle m hm

section Division

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def divByMonic [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, Trim.isCanonical_trim (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def modByMonic [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, Trim.isCanonical_trim (Raw.modByMonic p.val q.val)⟩

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.div p.val q.val).trim, Trim.isCanonical_trim (Raw.div p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.mod p.val q.val).trim, Trim.isCanonical_trim (Raw.mod p.val q.val)⟩

instance [Field R] [BEq R] [LawfulBEq R] : Div (CPolynomial R) := ⟨div⟩
instance [Field R] [BEq R] [LawfulBEq R] : Mod (CPolynomial R) := ⟨mod⟩

end Division

end Operations

section Semiring

lemma one_mul [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : 1 * p = p := by
  apply Subtype.ext
  have : (1 * p : CPolynomial R) = (1: CPolynomial.Raw R) * p.val := rfl
  rw[this, one_mul_trim]
  exact trim_eq p

lemma mul_one [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) : p * 1 = p := by
  apply Subtype.ext
  have : (p * 1 : CPolynomial R) = p.val * (1: CPolynomial.Raw R) := rfl
  rw[this, mul_one_trim]
  exact trim_eq p

lemma mul_assoc [Semiring R] [BEq R] [LawfulBEq R]
    (p q r : CPolynomial R) : (p * q) * r = p * (q * r) := by
  apply Subtype.ext
  exact Raw.mul_assoc p.val q.val r.val

lemma zero_mul [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : 0 * p = 0 := by
  apply Subtype.ext
  exact Raw.zero_mul p.val

lemma mul_zero [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : p * 0 = 0 := by
  apply Subtype.ext
  exact Raw.mul_zero p.val

lemma mul_add [Semiring R] [BEq R] [LawfulBEq R]
    (p q r : CPolynomial R) : p * (q + r) = p * q + p * r := by
  apply Subtype.ext
  exact Raw.mul_add p.val q.val r.val

lemma add_mul [Semiring R] [BEq R] [LawfulBEq R]
    (p q r : CPolynomial R) : (p + q) * r = p * r + q * r := by
  apply Subtype.ext
  exact Raw.add_mul p.val q.val r.val

lemma pow_is_trimmed [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial.Raw R) (n : ℕ) : (p ^ n).trim = p ^ n := by
      induction' n with n ih generalizing p;
      · convert one_is_trimmed
        · infer_instance
        · infer_instance
      · have h_exp : p ^ (n + 1) = p * p ^ n := by
          exact pow_succ p n
        rw [h_exp]
        convert mul_is_trimmed p ( p ^ n ) using 1

lemma pow_succ_right [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
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
instance [Semiring R] [BEq R] [LawfulBEq R] : AddCommMonoid (CPolynomial R) where
  zero := 0
  add := (· + ·)
  add_assoc := CPolynomial.add_assoc
  add_comm := CPolynomial.add_comm
  zero_add := CPolynomial.zero_add
  add_zero := by intro p; exact CPolynomial.add_zero p
  nsmul := CPolynomial.nsmul
  nsmul_zero := CPolynomial.nsmul_zero
  nsmul_succ := CPolynomial.nsmul_succ

/-- `CPolynomial R` forms a semiring when `R` is a semiring.

  The semiring structure extends the `AddCommGroup` structure with multiplication.
  All operations preserve the canonical property (no trailing zeros).
-/
instance [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : Semiring (CPolynomial R) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := CPolynomial.add_assoc
  zero_add := CPolynomial.zero_add
  add_zero := by intro p; exact CPolynomial.add_zero p
  add_comm := CPolynomial.add_comm
  zero_mul := by intro p; exact CPolynomial.zero_mul p
  mul_zero := by intro p; exact CPolynomial.mul_zero p
  mul_assoc := by intro p q r; exact CPolynomial.mul_assoc p q r
  one_mul := by intro p; exact CPolynomial.one_mul p
  mul_one := by intro p; exact CPolynomial.mul_one p
  left_distrib := by intro p q r; exact CPolynomial.mul_add p q r
  right_distrib := by intro p q r; exact CPolynomial.add_mul p q r
  nsmul := CPolynomial.nsmul
  nsmul_zero := CPolynomial.nsmul_zero
  nsmul_succ := CPolynomial.nsmul_succ
  npow n p := ⟨Raw.powBySq p.val n, by
    rw [Raw.powBySq_eq_pow]
    exact Trim.isCanonical_of_trim_eq
      (CPolynomial.pow_is_trimmed p.val n)⟩
  npow_zero := by
    intro x; apply Subtype.ext
    show Raw.powBySq x.val 0 = Raw.C 1
    rw [Raw.powBySq_eq_pow]; rfl
  npow_succ := by
    intro n p; apply Subtype.ext
    show Raw.powBySq p.val (n + 1) = (⟨Raw.powBySq p.val n, _⟩ * p).val
    simp only [Raw.powBySq_eq_pow]
    exact CPolynomial.pow_succ_right p.val n
  natCast_zero := by rfl
  natCast_succ := by intro n; rfl

/-- The underlying `Raw` value of `p ^ n` equals `p.val ^ n`
(using the Raw `Pow` instance). This bridges the optimized
`powBySq` used in the `Semiring` instance with the spec
`pow`. -/
lemma val_pow [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (n : ℕ) : (p ^ n).val = p.val ^ n :=
  Raw.powBySq_eq_pow p.val n

/-- `C r * X^n = monomial n r` as canonical polynomials. -/
lemma C_mul_X_pow_eq_monomial [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R] [Nontrivial R]
    (r : R) (n : ℕ) :
    (C r : CPolynomial R) * X ^ n = monomial n r := by
  apply Subtype.ext
  -- Reduce to Raw-level equality via val_pow
  have hval : (C r * X ^ n : CPolynomial R).val =
      (Raw.C r).trim * (Raw.X : CPolynomial.Raw R) ^ n := by
    show (C r).val * (X ^ n : CPolynomial R).val = _
    rw [val_pow]; rfl
  rw [hval]
  show (Raw.C r).trim * Raw.X ^ n = Raw.monomial n r
  by_cases hr : r = 0
  · subst hr
    rw [show (Raw.C (0 : R)).trim = (0 : CPolynomial.Raw R) from Raw.trim_replicate_zero 1,
        Raw.zero_mul]
    simp [Raw.monomial]
  · rw [show (Raw.C r).trim = Raw.C r from Trim.canonical_iff.mpr fun hp ↦ hr,
        Raw.C_mul_eq_smul_trim, Raw.X_pow_eq_monomial_one]
    exact Raw.smul_monomial_one_trim n r

end Semiring

section CommSemiring

lemma mul_comm [CommSemiring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) : p * q = q * p := by
  apply Subtype.ext
  have dist_lhs : (p * q : CPolynomial R) = (p.val * q.val : CPolynomial.Raw R) := rfl
  have dist_rhs : (q * p : CPolynomial R) = (q.val * p.val : CPolynomial.Raw R) := rfl
  rw [dist_lhs, dist_rhs]
  exact Raw.mul_comm p.val q.val

/-- `CPolynomial R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : CommSemiring (CPolynomial R) where
  __ := (inferInstance : Semiring (CPolynomial R))
  mul_comm := by intro p q; exact mul_comm p q

end CommSemiring

section Ring

instance [Ring R] [BEq R] [LawfulBEq R] : Neg (CPolynomial R) where
  neg p := ⟨-p.val, Trim.isCanonical_of_trim_eq (neg_trim p.val (trim_eq p))⟩

instance [Ring R] [BEq R] [LawfulBEq R] : Sub (CPolynomial R) where
  sub p q := p + -q

lemma erase_canonical [Ring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (p : CPolynomial R) :
    let e := p.val - Raw.monomial n (p.val.coeff n)
    e.trim = e := by
  simp; apply Trim.trim_twice

/-- Erase the coefficient at index `n` (same as `p` except `coeff n = 0`, then trimmed). -/
def erase [Ring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  let e := p.val - Raw.monomial n (p.val.coeff n)
  ⟨e, Trim.isCanonical_of_trim_eq (by rw [erase_canonical])⟩

/-- Coefficient of `erase n p`: zero at `n`, otherwise `coeff p i`. -/
lemma coeff_erase [Ring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n i : ℕ) (p : CPolynomial R) :
    coeff (erase n p) i = if i = n then 0 else coeff p i := by
  unfold erase coeff
  rw [Raw.sub_coeff, Raw.coeff_monomial]
  by_cases h : n = i <;> simp [h]
  intro h'; rw [h'] at h
  contradiction

/-- Leading coefficient equals the coefficient at `natDegree`. -/
lemma leadingCoeff_eq_coeff_natDegree [Zero R] (p : CPolynomial R) :
    p.leadingCoeff = p.coeff p.natDegree := by
  cases hs : p.val.size with
  | zero =>
      have hval : p.val = (#[] : CPolynomial.Raw R) := Array.eq_empty_of_size_eq_zero hs
      have hp0 : p = 0 := by
        apply CPolynomial.ext
        simpa using hval
      cases hp0
      rfl
  | succ n =>
      have hnat : p.natDegree = n := by simp [CPolynomial.natDegree, hs]
      rw [hnat]
      simp [CPolynomial.leadingCoeff, CPolynomial.coeff, Raw.coeff, Array.getLastD, hs]

/-- A polynomial equals its leading monomial plus the rest (`erase` at `natDegree`). -/
lemma monomial_add_erase [Ring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (p : CPolynomial R) :
    p = monomial p.natDegree p.leadingCoeff + erase p.natDegree p := by
  apply (eq_iff_coeff).2
  intro i
  rw [coeff_add, coeff_monomial, coeff_erase]
  by_cases hi : i = p.natDegree
  · subst hi
    rw [if_pos rfl, if_pos rfl, leadingCoeff_eq_coeff_natDegree]
    simp
  · rw [if_neg hi, if_neg hi]
    simp

lemma coeff_neg [Ring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (i : ℕ) : coeff (-p) i = -coeff p i := by
  unfold coeff; exact Raw.neg_coeff p.val i

lemma coeff_sub [Ring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (i : ℕ) : coeff (p - q) i = coeff p i - coeff q i := by
  unfold coeff; exact Raw.sub_coeff p.val q.val i

theorem neg_add_cancel [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : -p + p = 0 := by
  apply Subtype.ext
  have dist_lhs : (-p + p).val  = ((-p).val + p.val) := rfl
  rw [dist_lhs]
  exact Raw.neg_add_cancel p.val

instance [Ring R] [BEq R] [LawfulBEq R] : AddCommGroup (CPolynomial R) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := HSub.hSub
  add_assoc := CPolynomial.add_assoc
  zero_add := CPolynomial.zero_add
  add_zero := CPolynomial.add_zero
  add_comm := CPolynomial.add_comm
  neg_add_cancel := by intro a; exact CPolynomial.neg_add_cancel (p := a)
  nsmul := CPolynomial.nsmul
  nsmul_zero := CPolynomial.nsmul_zero
  nsmul_succ := CPolynomial.nsmul_succ
  sub_eq_add_neg := by intro a b; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro p; apply Subtype.ext; rfl
  zsmul_succ' := by intro n p; apply Subtype.ext; rfl
  zsmul_neg' := by intro n p; apply Subtype.ext; rfl

/-- `CPolynomial R` forms a ring when `R` is a ring.

  The ring structure extends the semiring structure with negation and subtraction.
  Most of the structure is already provided by the `Semiring` instance.
-/
instance [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R] : Ring (CPolynomial R) where
  __ := (inferInstance : Semiring (CPolynomial R))
  __ := (inferInstance : AddCommGroup (CPolynomial R))
  intCast_ofNat := by intro n; apply Subtype.ext; rfl
  intCast_negSucc := by intro n; apply Subtype.ext; rfl

end Ring

section CommRing

/-- `CPolynomial R` forms a commutative ring when `R` is a commutative ring.

  This combines the `CommSemiring` and `Ring` structures.
-/
instance [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] : CommRing (CPolynomial R) where
  __ := (inferInstance : Ring (CPolynomial R))
  __ := (inferInstance : CommSemiring (CPolynomial R))

end CommRing

section Module

-- The assumptions are required for `CPolynomial R` to be a module and are necessary downstream.

/-- Scalar multiplication for canonical polynomials: multiply each coefficient by `r`,
then trim to restore canonicity. -/
instance smul [Semiring R] [BEq R] [LawfulBEq R] : SMul R (CPolynomial R) where
  smul r p := ⟨(Raw.smul r p.val).trim, Trim.isCanonical_trim (Raw.smul r p.val)⟩

/-- Coefficient of a scalar multiple. -/
lemma coeff_smul [Semiring R] [BEq R] [LawfulBEq R]
    (r : R) (p : CPolynomial R) (i : ℕ) :
    coeff (r • p) i = r * coeff p i := by
  show (Raw.smul r p.val).trim.coeff i = r * p.val.coeff i
  rw [Trim.coeff_eq_coeff, Raw.smul_equiv]

/-- Scalar multiplication on 0 gives 0. -/
lemma smul_zero [Semiring R] [BEq R] [LawfulBEq R] (r : R) : r • (0 : CPolynomial R) = 0 := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, coeff_zero]; simp

/-- Helper lemma: Two CPolynomials are equal if
    the underlying Raw CPolynomials are trim equivalent. -/
lemma smul_eq_of_coeff_eq [Zero R] [BEq R] [LawfulBEq R] {p q : CPolynomial R}
    (h : Trim.equiv p.val q.val) : p = q := by
  apply CPolynomial.ext
  exact Trim.isCanonical_ext p.property q.property h

/-- Scalar multiplication distributes. -/
lemma smul_add [Semiring R] [BEq R] [LawfulBEq R]
    (r : R) (p q : CPolynomial R) :
    r • (p + q) = r • p + r • q := by
  apply smul_eq_of_coeff_eq; intro i
  show (Raw.smul r (p.val + q.val)).trim.coeff i =
    ((Raw.smul r p.val).trim + (Raw.smul r q.val).trim).coeff i
  rw [Trim.coeff_eq_coeff, smul_equiv, add_coeff_trimmed,
      add_coeff_trimmed, Trim.coeff_eq_coeff, Trim.coeff_eq_coeff,
      smul_equiv, smul_equiv]
  exact Distrib.left_distrib r (p.val.coeff i) (q.val.coeff i)

/-- Scalar multiplication distributes across scalar addition. -/
lemma add_smul [Semiring R] [BEq R] [LawfulBEq R]
    (r s : R) (p : CPolynomial R) :
    (r + s) • p = r • p + s • p := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, coeff_add, coeff_smul, coeff_smul]; grind

/-- Scalar multiplication by 0 gives 0. -/
lemma zero_smul [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : (0 : R) • p = 0 := by
  apply smul_eq_of_coeff_eq; intro i
  show (Raw.smul 0 p.val).trim.coeff i = (0 : Raw R).coeff i
  rw [Trim.coeff_eq_coeff, smul_equiv]
  exact MulZeroClass.zero_mul (p.val.coeff i)

/-- Scalar multiplication on p by 1 gives p. -/
lemma one_smul [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) : (1 : R) • p = p := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, _root_.one_mul]

/-- Scalar multiplication is associative. -/
lemma mul_smul [Semiring R] [BEq R] [LawfulBEq R]
    (r s : R) (p : CPolynomial R) :
    (r * s) • p = r • (s • p) := by
  rw [eq_iff_coeff]; intro i
  rw [coeff_smul, coeff_smul, coeff_smul, _root_.mul_assoc]

/-- `CPolynomial` forms a module when R is a semiring. -/
instance [Semiring R] [BEq R] [LawfulBEq R] : Module R (CPolynomial R) where
  smul:= SMul.smul
  mul_smul := mul_smul
  one_smul := one_smul
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul
  zero_smul := zero_smul

end Module

end CPolynomial

end CompPoly
