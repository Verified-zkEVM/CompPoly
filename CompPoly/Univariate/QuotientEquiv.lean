/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/
import CompPoly.Univariate.Quotient
import CompPoly.Univariate.ToPoly

/-!
# QuotientCPolynomial <-> Polynomial Isomorphism

This file establishes the ring equivalence between `QuotientCPolynomial R`
(the quotient of `CPolynomial.Raw R` by coefficient-wise equivalence) and
mathlib's `Polynomial R`.

## Main declarations

* `QuotientCPolynomial.toPoly` - quotient -> Polynomial via `Quotient.lift` on `Raw.toPoly`
* `QuotientCPolynomial.ofPoly` - Polynomial -> quotient via `Quotient.mk` on `Polynomial.toImpl`
* `QuotientCPolynomial.toPoly_ofPoly` - round-trip identity `toPoly ∘ ofPoly = id`
* `QuotientCPolynomial.ofPoly_toPoly` - round-trip identity `ofPoly ∘ toPoly = id`
* `QuotientCPolynomial.ringEquiv` - the ring equivalence `QuotientCPolynomial R ≃+* Polynomial R`
-/

namespace CompPoly

namespace CPolynomial

namespace QuotientCPolynomial

open Raw Trim

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

omit [BEq R] [LawfulBEq R] in
/-- Well-definedness: equivalent raw polynomials map to the same `Polynomial`. -/
private theorem toPoly_resp (p q : CPolynomial.Raw R) (h : p ≈ q) :
    p.toPoly = q.toPoly := by
  ext n
  rw [Raw.coeff_toPoly, Raw.coeff_toPoly]
  exact h n

/-- Convert a `QuotientCPolynomial` to a mathlib `Polynomial R`.

  Defined by lifting `Raw.toPoly` through the quotient; well-definedness follows from
  the fact that equivalent raw polynomials have equal coefficients. -/
noncomputable def toPoly (p : QuotientCPolynomial R) : Polynomial R :=
  Quotient.lift Raw.toPoly toPoly_resp p

/-- Convert a mathlib `Polynomial R` to a `QuotientCPolynomial R`.

  Defined by extracting coefficients via `Polynomial.toImpl` and taking the
  equivalence class. -/
def ofPoly (p : Polynomial R) : QuotientCPolynomial R :=
  Quotient.mk _ (Polynomial.toImpl p)

omit [LawfulBEq R] in
/-- Round-trip identity: `toPoly ∘ ofPoly = id`. -/
@[simp]
theorem toPoly_ofPoly (p : Polynomial R) : toPoly (ofPoly p) = p := by
  simp [toPoly, ofPoly, Raw.toPoly_toImpl]

/-- Round-trip identity: `ofPoly ∘ toPoly = id`. -/
@[simp]
theorem ofPoly_toPoly (q : QuotientCPolynomial R) : ofPoly (toPoly q) = q := by
  refine Quotient.inductionOn q ?_
  intro p
  simp only [toPoly, ofPoly, Quotient.lift_mk]
  apply Quotient.sound
  show Trim.equiv (Polynomial.toImpl (Raw.toPoly p)) p
  intro i
  have h₁ : (Polynomial.toImpl (Raw.toPoly p)) = p.trim := Raw.toImpl_toPoly p
  rw [h₁, Trim.coeff_eq_coeff]

/-- The ring equivalence between `QuotientCPolynomial R` and `Polynomial R`.

  The forward map is `toPoly` (quotient-lift of `Raw.toPoly`); the inverse is
  `ofPoly` (coefficient extraction via `Polynomial.toImpl`).
  Preserves both addition and multiplication. -/
noncomputable def ringEquiv : QuotientCPolynomial R ≃+* Polynomial R where
  toFun := toPoly
  invFun := ofPoly
  left_inv := ofPoly_toPoly
  right_inv := toPoly_ofPoly
  map_mul' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp only [toPoly, Quotient.lift_mk]
    show (p.mul q).toPoly = p.toPoly * q.toPoly
    exact Polynomial.ext (Raw.toPoly_mul_coeff p q)
  map_add' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    simp only [toPoly, Quotient.lift_mk]
    show (p.add q).toPoly = p.toPoly + q.toPoly
    exact Raw.toPoly_add p q

end QuotientCPolynomial

end CPolynomial

end CompPoly
