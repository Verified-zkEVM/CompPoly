/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Basic

namespace CompPoly
namespace CPolynomial
variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

/-- canonical version of CPolynomial

TODO: make THIS the `CPolynomial, rename current `CPolynomial` to `CPolynomial.Raw` or something -/
def CPolynomialC (R : Type*) [BEq R] [Ring R] := { p : CPolynomial R // p.trim = p }

@[ext] theorem CPolynomialC.ext {p q : CPolynomialC R} (h : p.val = q.val) : p = q := Subtype.eq h

instance : Coe (CPolynomialC R) (CPolynomial R) where coe := Subtype.val

instance : Inhabited (CPolynomialC R) := ⟨#[], Trim.canonical_empty⟩


namespace OperationsC
-- additive group on CPolynomialC
variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]
variable (p q r : CPolynomialC R)

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

-- TODO: define `SemiRing` structure on `CPolynomialC`

end OperationsC

end CPolynomial
end CompPoly
