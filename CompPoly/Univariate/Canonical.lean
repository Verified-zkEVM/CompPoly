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

-- TODO: define `SemiRing`, `CommSemiRing` structure on `CPolynomialC`

end OperationsC

-- TODO: ring isomorphism with `QuotientCPolynomial`

end CPolynomial

end CompPoly
