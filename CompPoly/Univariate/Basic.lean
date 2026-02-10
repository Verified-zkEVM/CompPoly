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

variable {R : Type*} [Semiring R] [BEq R]
variable {Q : Type*} [Semiring Q]

/-- Computable univariate polynomials are represented canonically with no trailing zeros.

  A polynomial `p : CPolynomial.Raw R` is canonical if `p.trim = p`, meaning the last coefficient
  is non-zero (or the polynomial is empty). This provides a unique representative for each
  polynomial equivalence class.

-/
def CPolynomial (R : Type*) [BEq R] [Semiring R] := { p : CPolynomial.Raw R // p.trim = p }

namespace CPolynomial

/-- Extensionality for canonical polynomials. -/
@[ext] theorem ext {p q : CPolynomial R} (h : p.val = q.val) : p = q := by
  exact Subtype.ext h

/-- Canonical polynomials coerce to raw polynomials. -/
instance : Coe (CPolynomial R) (CPolynomial.Raw R) where coe := Subtype.val

/-- The zero polynomial is canonical. -/
instance : Inhabited (CPolynomial R) := ⟨#[], Trim.canonical_empty⟩

-- TODO namespace organization may have to change for ergonomics, etc
--      especially wrt the typeclass instances below
section Operations

variable {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
variable (p q r : CPolynomial R)

/-- Addition of canonical polynomials (result is canonical). -/
instance : Add (CPolynomial R) where
  add p q := ⟨p.val + q.val, by apply Trim.trim_twice⟩

theorem add_comm : p + q = q + p := by
  apply CPolynomial.ext; apply CPolynomial.Raw.add_comm

theorem add_assoc : p + q + r = p + (q + r) := by
  apply CPolynomial.ext; apply CPolynomial.Raw.add_assoc

instance : Zero (CPolynomial R) := ⟨0, zero_canonical⟩

theorem zero_add : 0 + p = p := by
  apply CPolynomial.ext
  apply CPolynomial.Raw.zero_add p.val p.prop

theorem add_zero : p + 0 = p := by
  apply CPolynomial.ext
  apply CPolynomial.Raw.add_zero p.val p.prop

/-- Scalar multiplication by a natural number (result is canonical). -/
def nsmul (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  ⟨CPolynomial.Raw.nsmul n p.val, by apply Trim.trim_twice⟩

theorem nsmul_zero : nsmul 0 p = 0 := by
  apply CPolynomial.ext; apply CPolynomial.Raw.nsmul_zero

theorem nsmul_succ (n : ℕ) (p : CPolynomial R) : nsmul (n + 1) p = nsmul n p + p := by
  apply CPolynomial.ext; apply CPolynomial.Raw.nsmul_succ

instance [LawfulBEq R] : AddCommSemigroup (CPolynomial R) where
  add_assoc := add_assoc
  add_comm := add_comm

section MulOne

variable [Nontrivial R]

/-- Multiplication of canonical polynomials.

  The product of two canonical polynomials is canonical because multiplication
  preserves the "no trailing zeros" property.
-/
instance : Mul (CPolynomial R) where
  mul p q :=
    ⟨p.val * q.val, by exact mul_is_trimmed p.val q.val⟩

/-- The constant polynomial 1 is canonical, and is the Unit for multiplication.

  This is `#[1]`, which has no trailing zeros.

  This proof does not work without the assumption that R is non-trivial.
-/
instance : One (CPolynomial R) where
  one := ⟨CPolynomial.Raw.C 1, by
  unfold C trim
  have nonzero : #[(1 : R)].size = 1 := by aesop
  have : lastNonzero #[(1 : R)] = some ⟨0, by simp⟩ := by
    unfold lastNonzero Array.findIdxRev? Array.findIdxRev?.find
    simp; aesop
  rw[this]
  grind
  ⟩

/-- Construct a canonical monomial `c * X^n` as a `CPolynomial R`.

  The result is canonical (no trailing zeros) when `c ≠ 0`.
  For example, `monomial 2 3` represents `3 * X^2`.

  Note: If `c = 0`, this returns `0` (the zero polynomial).
-/
def monomial [DecidableEq R] (n : ℕ) (c : R) : CPolynomial R :=
  ⟨Raw.monomial n c, Raw.monomial_canonical n c⟩

/-- Natural number degree of a canonical polynomial.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree (p : CPolynomial R) : ℕ := p.val.natDegree

-- Lemmas for typeclass instances

lemma one_mul (p : CPolynomial R) : 1 * p = p := by
  apply Subtype.ext
  have : (1 * p : CPolynomial R) = (1: CPolynomial.Raw R) * p.val := rfl
  rw[this, one_mul_trim]
  exact p.prop

lemma mul_one (p : CPolynomial R) : p * 1 = p := by
  apply Subtype.ext
  have : (p * 1 : CPolynomial R) = p.val * (1: CPolynomial.Raw R) := rfl
  rw[this, mul_one_trim]
  exact p.prop

omit [Nontrivial R] in
lemma mul_assoc (p q r : CPolynomial R) : (p * q) * r = p * (q * r) := by
  apply Subtype.ext
  exact CPolynomial.Raw.mul_assoc p.val q.val r.val

omit [Nontrivial R] in
lemma zero_mul (p : CPolynomial R) : 0 * p = 0 := by
  apply Subtype.ext
  exact CPolynomial.Raw.zero_mul p.val

omit [Nontrivial R] in
lemma mul_zero (p : CPolynomial R) : p * 0 = 0 := by
  apply Subtype.ext
  exact CPolynomial.Raw.mul_zero p.val

omit [Nontrivial R] in
lemma left_distrib (p q r : CPolynomial R) : p * (q + r) = p * q + p * r := by
  apply Subtype.ext
  exact CPolynomial.Raw.left_distrib p.val q.val r.val

omit [Nontrivial R] in
lemma right_distrib (p q r : CPolynomial R) : (p + q) * r = p * r + q * r := by
  apply Subtype.ext
  exact CPolynomial.Raw.right_distrib p.val q.val r.val

end MulOne

section Semiring

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
  npow n p := ⟨p.val ^ n, by sorry⟩
  npow_zero := by intro x; apply Subtype.ext; rfl
  npow_succ := by sorry
  natCast_zero := by rfl
  natCast_succ := by intro n; rfl

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R] [BEq R]
variable (p q : CPolynomial R)

lemma mul_comm [LawfulBEq R] (p q : CPolynomial R) : p * q = q * p := by
  apply Subtype.ext
  have dist_lhs : (p * q : CPolynomial R) = (p.val * q.val : CPolynomial.Raw R) := rfl
  have dist_rhs : (q * p : CPolynomial R) = (q.val * p.val : CPolynomial.Raw R) := rfl
  rw [dist_lhs, dist_rhs]
  exact CPolynomial.Raw.mul_comm p.val q.val

/-- `CPolynomial R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommSemiring R] [LawfulBEq R] [Nontrivial R] : CommSemiring (CPolynomial R) where
  mul_comm := by intro p q; exact mul_comm p q

end CommSemiring

section Ring

variable {R : Type*} [Ring R] [BEq R]
variable (p q: CPolynomial R)

instance [LawfulBEq R] : Neg (CPolynomial R) where
  neg p := ⟨-p.val, neg_trim p.val p.prop⟩

instance [LawfulBEq R] : Sub (CPolynomial R) where
  sub p q := p + -q

theorem neg_add_cancel [LawfulBEq R] : -p + p = 0 := by
  apply Subtype.ext
  let R' : Ring R := ‹Ring R›
  have dist_lhs : (-p + p).val  = ((-p).val + p.val) := rfl
  rw [dist_lhs]
  exact CPolynomial.Raw.neg_add_cancel p.val

instance [LawfulBEq R] : AddCommGroup (CPolynomial R) where
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

variable {R : Type*} [CommRing R] [BEq R]

/-- `CPolynomial R` forms a commutative ring when `R` is a commutative ring.

  This combines the `CommSemiring` and `Ring` structures.
-/
instance [LawfulBEq R] [Nontrivial R] : CommRing (CPolynomial R) where
  -- All structure inherited from `CommSemiring` and `Ring` instances

end CommRing

end Operations

-- TODO: Ring equivalence between canonical polynomials and the quotient.
-- This establishes that `CPolynomial R` and `QuotientCPolynomial R` are isomorphic
-- as rings. The canonical polynomials serve as unique representatives of each
-- equivalence class in the quotient.
--
-- TODO: Construct this ring equivalence after proving:
-- 1. Operations on quotient correspond to operations on canonical representatives
-- 2. `trim` gives a unique representative for each equivalence class
--
-- The equivalence should map canonical polynomials to their quotient classes
-- and back, preserving all ring operations.
-- TODO: Implement `ringEquivQuotient : CPolynomial R ≃+* QuotientCPolynomial R`

end CPolynomial

end CompPoly
