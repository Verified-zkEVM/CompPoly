/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa
-/

import CompPoly.Multivariate.Lawful

/-!
# Computable multivariate polynomials

Polynomials of the form `α₁ * m₁ + α₂ * m₂ + ... + αₖ * mₖ` where `αᵢ` is any semiring
and `mᵢ` is a `CMvMonomial`.

This is implemented as a wrapper around `CPoly.Lawful`, which ensures that all stored
coefficients are non-zero.

## Main definitions

* `CPoly.CMvPolynomial n R`: The type of multivariate polynomials in `n` variables with coefficients in `R`.
-/

namespace CPoly

open Std

/-- A computable multivariate polynomial in `n` variables with coefficients in `R`. -/
abbrev CMvPolynomial (n : ℕ) (R : Type) [Zero R] : Type := Lawful n R

variable {R : Type}

namespace CMvPolynomial

/-- Construct a constant polynomial. -/
def C {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R] (c : R) : CMvPolynomial n R :=
  Lawful.C (n := n) (R := R) c

/-- Construct the polynomial $X_i$. -/
def X {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] (i : Fin n) : CMvPolynomial n R :=
  let monomial : CMvMonomial n := Vector.ofFn (fun j => if j = i then 1 else 0)
  Lawful.fromUnlawful <| .ofList [(monomial, (1 : R))]

/-- Extract the coefficient of a monomial. -/
def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : CMvPolynomial n R) : R :=
  p.1[m]?.getD 0

attribute [grind =] coeff.eq_def

/-- Extensionality: two polynomials are equal if all their coefficients are equal. -/
@[ext, grind ext]
theorem ext {n : ℕ} [Zero R] (p q : CMvPolynomial n R)
    (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
  congr
  apply ExtTreeMap.ext_getElem?
  intros k; specialize h k
  by_cases k ∈ p <;> by_cases k ∈ q <;> grind

attribute [local grind =] Option.some_inj

section

variable [BEq R] [LawfulBEq R]

@[simp, grind =]
lemma fromUnlawful_zero {n : ℕ} [Zero R] : Lawful.fromUnlawful 0 = (0 : Lawful n R) := by
  unfold Lawful.fromUnlawful
  grind

variable {n : ℕ} [CommSemiring R] {m : CMvMonomial n} {p q : CMvPolynomial n R}

@[simp, grind =]
lemma add_getD? : (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0 := by
  erw [Unlawful.filter_get]
  exact Unlawful.add_getD?

@[simp, grind =]
lemma coeff_add : coeff m (p + q) = coeff m p + coeff m q := by simp only [coeff, add_getD?]

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects the sum fold. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful₀
    {t : List (CMvMonomial n × R)} {f : CMvMonomial n → R → Unlawful n R} :
    ∀ init : Unlawful n R,
    Lawful.fromUnlawful (List.foldl (fun u term => (f term.1 term.2) + u) init t) =
    List.foldl (fun l term => (Lawful.fromUnlawful (f term.1 term.2)) + l)
               (Lawful.fromUnlawful init) t := by
  induction' t with head tail ih
  · simp
  · intro init
    simp only [List.foldl_cons, ih]
    congr 1; ext m
    simp only [CMvMonomial.eq_1, coeff_add]
    unfold coeff Lawful.fromUnlawful
    iterate 3 erw [Unlawful.filter_get]
    exact Unlawful.add_getD?

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects the fold over terms. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful {t : Unlawful n R}
    {f : CMvMonomial n → R → Unlawful n R} :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
  ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t := by
  simp only [CMvMonomial.eq_1, ExtTreeMap.foldl_eq_foldl_toList]
  erw [fromUnlawful_fold_eq_fold_fromUnlawful₀ 0]
  simp
  rfl

end

/-- Evaluate a polynomial at a point given by a ring homomorphism `f` and variable assignments `vs`. -/
def eval₂ {R S : Type} {n : ℕ} [Semiring R] [CommSemiring S] :
    (R →+* S) → (Fin n → S) → CMvPolynomial n R → S :=
  fun f vs p => ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1

/-- Evaluate a polynomial at a given point. -/
def eval {R : Type} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvPolynomial n R → R :=
  eval₂ (RingHom.id _)

/-- The support of a polynomial (set of monomials with non-zero coefficients), represented as Finsupps. -/
def support {R : Type} {n : ℕ} [Zero R] (p : CMvPolynomial n R) : Finset (Fin n →₀ ℕ) :=
  (Lawful.monomials p).map CMvMonomial.toFinsupp |>.toFinset

/-- The total degree of a polynomial (maximum total degree of its monomials). -/
def totalDegree {R : Type} {n : ℕ} [inst : CommSemiring R] : CMvPolynomial n R → ℕ :=
  fun p => Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
    (fun s => Finsupp.sum s (fun _ e => e))

/-- The degree of a polynomial in a specific variable. -/
def degreeOf {R : Type} {n : ℕ} [CommSemiring R] (i : Fin n) : CMvPolynomial n R → ℕ :=
  fun p =>
    Multiset.count i
    (Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
      fun s => Finsupp.toMultiset s)

end CMvPolynomial

end CPoly
