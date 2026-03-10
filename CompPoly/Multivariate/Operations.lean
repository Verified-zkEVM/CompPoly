/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen, Dimitris Mitsios
-/
import CompPoly.Multivariate.MvPolyEquiv

/-!
# Computable multivariate polynomials (extended operations)

Operations on `CMvPolynomial` that depend on ring instances from `MvPolyEquiv.lean`,
such as monomial orders, leading terms, restriction, variable renaming, and substitution.

The core type and basic operations (`CMvPolynomial`, `C`, `X`, `coeff`, `eval`, etc.)
are in `CMvPolynomial.lean`. The `CommSemiring` and `CommRing` instances are in
`MvPolyEquiv.lean`.

## Main definitions

* `MonomialOrder`: Typeclass for comparing monomials.
* `leadingMonomial`, `leadingCoeff`, `leadingTerm`: Leading term operations
  according to a monomial order.
* `rename`: Rename variables using a function `Fin n → Fin m`.
* `aeval`: Algebra evaluation.
* `bind₁`: Substitution of polynomials for variables.
-/
namespace CPoly

open Std

variable {R : Type}

namespace CMvPolynomial

/-- Monomial ordering typeclass for `n` variables.

  Provides a way to compare monomials for determining leading terms.
-/
class MonomialOrder (n : ℕ) where
  compare : CMvMonomial n → CMvMonomial n → Ordering
  -- TODO: Add ordering axioms (transitivity, etc.)

/-- Baseline degree of a monomial.

  Currently this is the ordinary total degree and is independent of
  `MonomialOrder.compare`.
-/
def MonomialOrder.degree {n : ℕ} (m : CMvMonomial n) : ℕ :=
  m.totalDegree

/-- Leading monomial of a polynomial according to a monomial order.

  Returns `none` for the zero polynomial.
-/
def leadingMonomial {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : Option (CMvMonomial n) :=
  ExtTreeMap.foldl
    (fun acc m _ =>
      match acc with
      | none => some m
      | some m' =>
          match MonomialOrder.compare m m' with
          | .gt => some m
          | _ => some m')
    none p.1

/-- Leading term of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial, and otherwise returns the monomial with
  leading monomial and leading coefficient.
-/
def leadingTerm {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder n]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  match leadingMonomial p with
  | none => 0
  | some m => monomial m (coeff m p)

/-- Leading coefficient of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial.
-/
def leadingCoeff {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : R :=
  match leadingMonomial p with
  | none => 0
  | some m => coeff m p

@[simp] lemma leadingCoeff_eq_zero_of_leadingMonomial_eq_none
    {n : ℕ} {R : Type} [Zero R] [MonomialOrder n] {p : CMvPolynomial n R}
    (h : leadingMonomial p = none) : leadingCoeff p = 0 := by
  simp [leadingCoeff, h]

lemma leadingCoeff_eq_coeff_of_leadingMonomial_eq_some
    {n : ℕ} {R : Type} [Zero R] [MonomialOrder n] {p : CMvPolynomial n R}
    {m : CMvMonomial n} (h : leadingMonomial p = some m) : leadingCoeff p = coeff m p := by
  simp [leadingCoeff, h]

/-- Packaged form of `leadingCoeff`: it is the coefficient at the optional leading monomial,
defaulting to `0` when no leading monomial exists. -/
lemma leadingCoeff_eq_coeff_leadingMonomial
    {n : ℕ} {R : Type} [Zero R] [MonomialOrder n] (p : CMvPolynomial n R) :
    leadingCoeff p = (leadingMonomial p).elim 0 (fun m => coeff m p) := by
  grind [leadingCoeff]

@[simp] lemma leadingTerm_eq_zero_of_leadingMonomial_eq_none
    {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder n]
    {p : CMvPolynomial n R} (h : leadingMonomial p = none) :
    leadingTerm p = 0 := by
  grind [leadingTerm]

@[simp] lemma leadingTerm_eq_monomial_of_leadingMonomial_eq_some
    {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder n]
    {p : CMvPolynomial n R} {m : CMvMonomial n} (h : leadingMonomial p = some m) :
    leadingTerm p = monomial m (coeff m p) := by
  grind [leadingTerm]

/-- Algebra evaluation: evaluates polynomial in an algebra.

  Given an algebra `σ` over `R` and a function `f : Fin n → σ`, evaluates the polynomial.
-/
def aeval {n : ℕ} {R σ : Type} [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) : σ :=
  sorry

/-- Substitution: substitutes polynomials for variables.

  Given `f : Fin n → CMvPolynomial m R`, substitutes `f i` for variable `X i`.
-/
def bind₁ {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  sorry

/-- Rename variables using a function.

  Given `f : Fin n → Fin m`, renames variable `X i` to `X (f i)`.
-/
def rename {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → Fin m) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  let renameMonomial (mono : CMvMonomial n) : CMvMonomial m :=
    Vector.ofFn (fun j => (Finset.univ.filter (fun i => f i = j)).sum (fun i => mono.get i))
  ExtTreeMap.foldl (fun acc mono c => acc + monomial (renameMonomial mono) c) 0 p.1

-- `renameEquiv` is defined in `CompPoly.Multivariate.Rename`

/-- Scalar multiplication with zero handling.

  This is automatically provided by `Module`, but we list it for completeness.

  TODO: Requires `Module` instance (see above).
-/
instance {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] : SMulZeroClass R (CMvPolynomial n R) :=
  sorry

/-- Convert sum representation to iterative form.

  Folds over the monomial-coefficient pairs of `p`, rebuilding the polynomial
  one term at a time via `monomial m c` and addition.
-/
def sumToIter {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  ExtTreeMap.foldl (fun acc m c => acc + monomial m c) 0 p.1

end CMvPolynomial

end CPoly
