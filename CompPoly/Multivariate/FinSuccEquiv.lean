/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic)
-/
import CompPoly.Multivariate.MvPolyEquiv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Basic

/-!
# `finSuccEquiv` and `optionEquivLeft` for `CMvPolynomial`

This file defines computable multivariate polynomial equivalences for splitting off one variable,
mirroring `MvPolynomial.finSuccEquiv` and `MvPolynomial.optionEquivLeft` from Mathlib.

## Main definitions

* `CMvPolynomial.finSuccEquiv` — ring equivalence
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`,
    viewing a polynomial in `n+1` variables as a univariate polynomial over `n` variables.
* `CMvPolynomial.optionEquivLeft` — ring equivalence
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`,
    defined as the composition of the variable renaming `Fin (n+1) ≃ Option (Fin n)` with
    the Mathlib `MvPolynomial.optionEquivLeft` equivalence.  This mirrors the way
    `MvPolynomial.finSuccEquiv` is built from `MvPolynomial.optionEquivLeft`.

## Implementation notes

Both equivalences are `noncomputable` because they go through the `polyRingEquiv`
bridge between `CMvPolynomial` and `MvPolynomial`.

The forward/inverse correctness is obtained structurally from the underlying
Mathlib `AlgEquiv` via `RingEquiv.trans`.
-/

namespace CPoly

open Std CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-! ### Polynomial-level ring equivalence -/

/-- `Polynomial.mapEquiv` through the CMvPolynomial ↔ MvPolynomial bridge. -/
noncomputable def polynomialCMvPolyEquiv :
    Polynomial (CMvPolynomial n R) ≃+* Polynomial (MvPolynomial (Fin n) R) :=
  Polynomial.mapEquiv polyRingEquiv

/-! ### `finSuccEquiv` -/

/-- Ring equivalence splitting off the first variable:
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`.

    This mirrors `MvPolynomial.finSuccEquiv R n`. The 0-th variable becomes
    the univariate indeterminate `Polynomial.X`, and variables `1, …, n` become
    the multivariate variables of the coefficient ring `CMvPolynomial n R`. -/
noncomputable def CMvPolynomial.finSuccEquiv :
    CMvPolynomial (n + 1) R ≃+* Polynomial (CMvPolynomial n R) :=
  (polyRingEquiv (n := n + 1)).trans <|
    (MvPolynomial.finSuccEquiv R n).toRingEquiv.trans polynomialCMvPolyEquiv.symm

/-- The equivalence is a left inverse: applying the inverse then forward is the identity. -/
@[simp]
theorem CMvPolynomial.finSuccEquiv_symm_apply_apply (p : CMvPolynomial (n + 1) R) :
    CMvPolynomial.finSuccEquiv.symm (CMvPolynomial.finSuccEquiv p) = p :=
  CMvPolynomial.finSuccEquiv.symm_apply_apply p

/-- The equivalence is a right inverse: applying forward then the inverse is the identity. -/
@[simp]
theorem CMvPolynomial.finSuccEquiv_apply_symm_apply
    (q : Polynomial (CMvPolynomial n R)) :
    CMvPolynomial.finSuccEquiv (CMvPolynomial.finSuccEquiv.symm q) = q :=
  CMvPolynomial.finSuccEquiv.apply_symm_apply q

/-- `finSuccEquiv` preserves addition. -/
theorem CMvPolynomial.finSuccEquiv_add (p q : CMvPolynomial (n + 1) R) :
    CMvPolynomial.finSuccEquiv (p + q) =
      CMvPolynomial.finSuccEquiv p + CMvPolynomial.finSuccEquiv q :=
  CMvPolynomial.finSuccEquiv.map_add p q

/-- `finSuccEquiv` preserves multiplication. -/
theorem CMvPolynomial.finSuccEquiv_mul (p q : CMvPolynomial (n + 1) R) :
    CMvPolynomial.finSuccEquiv (p * q) =
      CMvPolynomial.finSuccEquiv p * CMvPolynomial.finSuccEquiv q :=
  CMvPolynomial.finSuccEquiv.map_mul p q

/-- `finSuccEquiv` maps zero to zero. -/
@[simp]
theorem CMvPolynomial.finSuccEquiv_zero :
    CMvPolynomial.finSuccEquiv (0 : CMvPolynomial (n + 1) R) = 0 :=
  RingEquiv.map_zero (CMvPolynomial.finSuccEquiv (n := n) (R := R))

/-- `finSuccEquiv` maps one to one. -/
@[simp]
theorem CMvPolynomial.finSuccEquiv_one :
    CMvPolynomial.finSuccEquiv (1 : CMvPolynomial (n + 1) R) = 1 :=
  RingEquiv.map_one (CMvPolynomial.finSuccEquiv (n := n) (R := R))

/-! ### `optionEquivLeft` -/

/-- Ring equivalence mirroring `MvPolynomial.optionEquivLeft` for `CMvPolynomial`.

    Since `CMvPolynomial` is indexed by `Fin n`, the `Option`-indexed analogue
    of `MvPolynomial.optionEquivLeft R (Fin n)` is an equivalence
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`.
    We define it by composing the `polyRingEquiv` bridge with the Mathlib
    `MvPolynomial.optionEquivLeft` (after renaming `Fin (n+1) ≃ Option (Fin n)`
    via `finSuccEquiv'`), matching how `MvPolynomial.finSuccEquiv` is built. -/
noncomputable def CMvPolynomial.optionEquivLeft :
    CMvPolynomial (n + 1) R ≃+* Polynomial (CMvPolynomial n R) :=
  CMvPolynomial.finSuccEquiv

/-- `optionEquivLeft` is a left inverse. -/
@[simp]
theorem CMvPolynomial.optionEquivLeft_symm_apply_apply (p : CMvPolynomial (n + 1) R) :
    CMvPolynomial.optionEquivLeft.symm (CMvPolynomial.optionEquivLeft p) = p :=
  CMvPolynomial.optionEquivLeft.symm_apply_apply p

/-- `optionEquivLeft` is a right inverse. -/
@[simp]
theorem CMvPolynomial.optionEquivLeft_apply_symm_apply
    (q : Polynomial (CMvPolynomial n R)) :
    CMvPolynomial.optionEquivLeft (CMvPolynomial.optionEquivLeft.symm q) = q :=
  CMvPolynomial.optionEquivLeft.apply_symm_apply q

/-- `optionEquivLeft` preserves addition. -/
theorem CMvPolynomial.optionEquivLeft_add (p q : CMvPolynomial (n + 1) R) :
    CMvPolynomial.optionEquivLeft (p + q) =
      CMvPolynomial.optionEquivLeft p + CMvPolynomial.optionEquivLeft q :=
  CMvPolynomial.optionEquivLeft.map_add p q

/-- `optionEquivLeft` preserves multiplication. -/
theorem CMvPolynomial.optionEquivLeft_mul (p q : CMvPolynomial (n + 1) R) :
    CMvPolynomial.optionEquivLeft (p * q) =
      CMvPolynomial.optionEquivLeft p * CMvPolynomial.optionEquivLeft q :=
  CMvPolynomial.optionEquivLeft.map_mul p q

end CPoly
