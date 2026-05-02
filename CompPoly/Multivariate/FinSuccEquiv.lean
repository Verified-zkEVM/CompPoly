/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic), Dimitris Mitsios
-/
import CompPoly.Multivariate.MvPolyEquiv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Basic

/-!
# `finSuccEquiv` for `CMvPolynomial`

This file defines the computable multivariate polynomial equivalence for
splitting off one variable, mirroring `MvPolynomial.finSuccEquiv` from Mathlib.

In Mathlib, `MvPolynomial` accepts a general type `σ` for the index set of the
variables. Then, `optionEquivLeft` provides the algebra isomorphism
`MvPolynomial (Option σ) R ≃ₐ[R] Polynomial (MvPolynomial σ R)`. Finally,
`finSuccEquiv` is defined as the composition of the rename step
(`Fin (n+1) ≃ Option (Fin n)`) with `optionEquivLeft`. There is no such
distinction in `CMvPolynomial` because the variables are of type `Fin n` by
definition. Therefore, only `CMvPolynomial.finSuccEquiv` applies.

## Main definitions

* `CMvPolynomial.finSuccEquiv` — ring equivalence
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`,
    viewing a polynomial in `n+1` variables as a univariate polynomial over `n` variables.

## Implementation notes

The equivalence is `noncomputable` because it goes through the `polyRingEquiv`
bridge between `CMvPolynomial` and `MvPolynomial`.

The forward/inverse correctness is obtained structurally from the underlying
Mathlib `AlgEquiv` via `RingEquiv.trans`.
-/

open Std CPoly CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

namespace CPoly

/-! ### Polynomial-level ring equivalence -/

/-- `Polynomial.mapEquiv` through the CMvPolynomial ↔ MvPolynomial bridge. -/
noncomputable def polynomialCMvPolyEquiv :
    Polynomial (CMvPolynomial n R) ≃+* Polynomial (MvPolynomial (Fin n) R) :=
  Polynomial.mapEquiv polyRingEquiv

end CPoly

namespace CMvPolynomial

/-! ### `finSuccEquiv` -/

/-- Ring equivalence splitting off the first variable:
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`.

    This mirrors `MvPolynomial.finSuccEquiv R n`. The 0-th variable becomes
    the univariate indeterminate `Polynomial.X`, and variables `1, …, n` become
    the multivariate variables of the coefficient ring `CMvPolynomial n R`. -/
noncomputable def finSuccEquiv :
    CMvPolynomial (n + 1) R ≃+* Polynomial (CMvPolynomial n R) :=
  (polyRingEquiv (n := n + 1)).trans <|
    (MvPolynomial.finSuccEquiv R n).toRingEquiv.trans polynomialCMvPolyEquiv.symm

/-- The equivalence is a left inverse: applying the inverse then forward is the identity. -/
@[simp]
theorem finSuccEquiv_symm_apply_apply (p : CMvPolynomial (n + 1) R) :
    finSuccEquiv.symm (finSuccEquiv p) = p :=
  finSuccEquiv.symm_apply_apply p

/-- The equivalence is a right inverse: applying forward then the inverse is the identity. -/
@[simp]
theorem finSuccEquiv_apply_symm_apply
    (q : Polynomial (CMvPolynomial n R)) :
    finSuccEquiv (finSuccEquiv.symm q) = q :=
  finSuccEquiv.apply_symm_apply q

/-- `finSuccEquiv` preserves addition. -/
theorem finSuccEquiv_add (p q : CMvPolynomial (n + 1) R) :
    finSuccEquiv (p + q) =
      finSuccEquiv p + finSuccEquiv q :=
  finSuccEquiv.map_add p q

/-- `finSuccEquiv` preserves multiplication. -/
theorem finSuccEquiv_mul (p q : CMvPolynomial (n + 1) R) :
    finSuccEquiv (p * q) =
      finSuccEquiv p * finSuccEquiv q :=
  finSuccEquiv.map_mul p q

/-- `finSuccEquiv` maps zero to zero. -/
@[simp]
theorem finSuccEquiv_zero :
    finSuccEquiv (0 : CMvPolynomial (n + 1) R) = 0 :=
  RingEquiv.map_zero (finSuccEquiv (n := n) (R := R))

/-- `finSuccEquiv` maps one to one. -/
@[simp]
theorem finSuccEquiv_one :
    finSuccEquiv (1 : CMvPolynomial (n + 1) R) = 1 :=
  RingEquiv.map_one (finSuccEquiv (n := n) (R := R))

end CMvPolynomial
