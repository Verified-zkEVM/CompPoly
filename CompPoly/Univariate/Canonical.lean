/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Basic
import CompPoly.Univariate.Quotient

/-!
  # Canonical Univariate Polynomials

  This file defines `CPolynomialC R`, the type of canonical (trimmed) univariate polynomials.
  A polynomial is canonical if it has no trailing zeros, i.e., `p.trim = p`.

  This provides a unique representation for each polynomial, enabling stronger extensionality
  properties compared to the raw `CPolynomial` type.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

/-- Canonical univariate polynomials: those with no trailing zeros.

  A polynomial `p : CPolynomial R` is canonical if `p.trim = p`, meaning the last coefficient
  is non-zero (or the polynomial is empty). This provides a unique representative for each
  polynomial equivalence class.

  TODO: make THIS the `CPolynomial`, rename current `CPolynomial` to `CPolynomial.Raw` or something,
  changing this file to Basic.lean? -/
def CPolynomialC (R : Type*) [BEq R] [Ring R] := { p : CPolynomial R // p.trim = p }

/-- Extensionality for canonical polynomials. -/
@[ext] theorem CPolynomialC.ext {p q : CPolynomialC R} (h : p.val = q.val) : p = q := Subtype.eq h

/-- Canonical polynomials coerce to raw polynomials. -/
instance : Coe (CPolynomialC R) (CPolynomial R) where coe := Subtype.val

/-- The zero polynomial is canonical. -/
instance : Inhabited (CPolynomialC R) := ⟨#[], Trim.canonical_empty⟩

-- TODO namespace organization may have to change for ergonomics, etc
--      especially wrt the typeclass instances below
namespace OperationsC

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
variable (p q r : CPolynomialC R)

/-- Addition of canonical polynomials (result is canonical). -/
instance : Add (CPolynomialC R) where
  add p q := ⟨p.val + q.val, by apply Trim.trim_twice⟩

theorem add_comm : p + q = q + p := by
  apply CPolynomialC.ext; apply CPolynomial.add_comm

theorem add_assoc : p + q + r = p + (q + r) := by
  apply CPolynomialC.ext; apply CPolynomial.add_assoc

instance : Zero (CPolynomialC R) := ⟨0, zero_canonical⟩

theorem zero_add : 0 + p = p := by
  apply CPolynomialC.ext
  apply CPolynomial.zero_add p.val p.prop

theorem add_zero : p + 0 = p := by
  apply CPolynomialC.ext
  apply CPolynomial.add_zero p.val p.prop

/-- Scalar multiplication by a natural number (result is canonical). -/
def nsmul (n : ℕ) (p : CPolynomialC R) : CPolynomialC R :=
  ⟨CPolynomial.nsmul n p.val, by apply Trim.trim_twice⟩

theorem nsmul_zero : nsmul 0 p = 0 := by
  apply CPolynomialC.ext; apply CPolynomial.nsmul_zero

theorem nsmul_succ (n : ℕ) (p : CPolynomialC R) : nsmul (n + 1) p = nsmul n p + p := by
  apply CPolynomialC.ext; apply CPolynomial.nsmul_succ

instance : Neg (CPolynomialC R) where
  neg p := ⟨-p.val, neg_trim p.val p.prop⟩

instance : Sub (CPolynomialC R) where
  sub p q := p + -q

theorem neg_add_cancel : -p + p = 0 := by
  apply CPolynomialC.ext
  apply CPolynomial.neg_add_cancel

instance [LawfulBEq R] : AddCommGroup (CPolynomialC R) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  nsmul := nsmul -- TODO do we actually need this custom implementation?
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  zsmul := zsmulRec -- TODO do we want a custom efficient implementation?

section MulOne

/-- Multiplication of canonical polynomials (result is canonical).

  The product of two canonical polynomials is canonical because multiplication
  preserves the "no trailing zeros" property.
-/
instance : Mul (CPolynomialC R) where
  mul p q :=
    ⟨p.val * q.val, by sorry⟩

/-- The constant polynomial 1 is canonical.

  This is `#[1]`, which has no trailing zeros.
-/
instance : One (CPolynomialC R) where
  one := ⟨CPolynomial.C 1, by sorry⟩

-- TODO: Prove multiplicative properties, e.g.
-- lemma one_mul (p : CPolynomialC R) : 1 * p = p := by sorry
-- lemma mul_one (p : CPolynomialC R) : p * 1 = p := by sorry
-- lemma mul_assoc (p q r : CPolynomialC R) : (p * q) * r = p * (q * r) := by sorry
-- lemma zero_mul (p : CPolynomialC R) : 0 * p = 0 := by sorry
-- lemma mul_zero (p : CPolynomialC R) : p * 0 = 0 := by sorry
-- lemma left_distrib (p q r : CPolynomialC R) : p * (q + r) = p * q + p * r := by sorry
-- lemma right_distrib (p q r : CPolynomialC R) : (p + q) * r = p * r + q * r := by sorry

end MulOne

section Semiring

/-- `CPolynomialC R` forms a semiring when `R` is a semiring.

  The semiring structure extends the `AddCommGroup` structure with multiplication.
  All operations preserve the canonical property (no trailing zeros).

  TODO: Complete all the required proofs for the semiring axioms.
-/
instance [Semiring R] [LawfulBEq R] : Semiring (CPolynomialC R) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  left_distrib := by sorry
  right_distrib := by sorry
  nsmul := nsmul
  nsmul_zero := nsmul_zero
  nsmul_succ := nsmul_succ
  npow n p := ⟨p.val ^ n, by sorry⟩
  npow_zero := by sorry
  npow_succ := by sorry
  natCast_zero := by sorry
  natCast_succ := by sorry

end Semiring

section CommSemiring

/-- `CPolynomialC R` forms a commutative semiring when `R` is a commutative semiring.

  Commutativity follows from the commutativity of multiplication in the base ring.
-/
instance [CommSemiring R] [LawfulBEq R] : CommSemiring (CPolynomialC R) where
  mul_comm := by sorry

end CommSemiring

section Ring

/-- `CPolynomialC R` forms a ring when `R` is a ring.

  The ring structure extends the semiring structure with negation and subtraction.
  Most of the structure is already provided by the `Semiring` instance.
-/
instance [Ring R] [LawfulBEq R] : Ring (CPolynomialC R) where
  sub_eq_add_neg := by intro a b; rfl
  zsmul := zsmulRec
  zsmul_zero' := by sorry
  zsmul_succ' := by sorry
  zsmul_neg' := by sorry
  intCast_ofNat := by sorry
  intCast_negSucc := by sorry
  neg_add_cancel := by sorry

end Ring

section CommRing

/-- `CPolynomialC R` forms a commutative ring when `R` is a commutative ring.

  This combines the `CommSemiring` and `Ring` structures.
-/
instance [CommRing R] [LawfulBEq R] : CommRing (CPolynomialC R) where
  -- All structure inherited from `CommSemiring` and `Ring` instances

end CommRing

end OperationsC

-- TODO: Ring equivalence between canonical polynomials and the quotient.
-- This establishes that `CPolynomialC R` and `QuotientCPolynomial R` are isomorphic
-- as rings. The canonical polynomials serve as unique representatives of each
-- equivalence class in the quotient.
--
-- TODO: Construct this ring equivalence after proving:
-- 1. Operations on quotient correspond to operations on canonical representatives
-- 2. `trim` gives a unique representative for each equivalence class
--
-- The equivalence should map canonical polynomials to their quotient classes
-- and back, preserving all ring operations.
-- TODO: Implement `ringEquivQuotient : CPolynomialC R ≃+* QuotientCPolynomial R`

end CPolynomial

end CompPoly
