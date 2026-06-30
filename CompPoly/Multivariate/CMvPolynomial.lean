/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen, Dimitris Mitsios
-/
import CompPoly.Multivariate.Lawful
import CompPoly.Univariate.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Computable multivariate polynomials

Polynomials of the form `α₁ * m₁ + α₂ * m₂ + ... + αₖ * mₖ` where `αᵢ` is any semiring
and `mᵢ` is a `CMvMonomial`.

This is implemented as a wrapper around `CPoly.Lawful`, which ensures that all stored
coefficients are non-zero.

This file contains the core type definition and basic operations. Higher-level definitions
that depend on ring instances (monomial orders, `rename`, `aeval`, etc.) are in
`CMvPolynomial.lean`. The `CommSemiring` and `CommRing` instances are in `MvPolyEquiv.lean`.

## Main definitions

* `CPoly.CMvPolynomial σ R`: The type of multivariate polynomials in variables `σ`
  with coefficients in `R`.
* `CPoly.CMvPolynomial.C`: Constant polynomial constructor.
* `CPoly.CMvPolynomial.X`: Variable polynomial constructor.
* `CPoly.CMvPolynomial.monomial`: Monomial constructor.
* `CPoly.CMvPolynomial.coeff`: Extract the coefficient of a monomial.
* `CPoly.CMvPolynomial.eval₂`, `CPoly.CMvPolynomial.eval`: Polynomial evaluation.
* `CPoly.CMvPolynomial.eval₂Horner`, `CPoly.CMvPolynomial.evalHorner`:
  Polynomial evaluation using Horner's method.
* `CPoly.CMvPolynomial.support`, `CPoly.CMvPolynomial.totalDegree`,
  `CPoly.CMvPolynomial.degreeOf`, `CPoly.CMvPolynomial.degrees`,
  `CPoly.CMvPolynomial.vars`: Degree and support queries.
-/
namespace CPoly

open Std

/-- A computable multivariate polynomial in variables `σ` with coefficients in `R`. -/
abbrev CMvPolynomial (σ : Type*) [FinEnum σ] (R : Type*) [Zero R] : Type _ := Lawful σ R

variable {R : Type*}

namespace CMvPolynomial

/-- Construct a constant polynomial. -/
def C {σ : Type*} [FinEnum σ] {R : Type*} [BEq R] [LawfulBEq R] [Zero R] (c : R) :
    CMvPolynomial σ R :=
  Lawful.C (σ := σ) (R := R) c

/-- Construct the polynomial $X_i$. -/
def X {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [One R] [BEq R] [LawfulBEq R]
    (i : σ) : CMvPolynomial σ R :=
  let monomial : CMvMonomial σ := Vector.ofFn (fun j => if j = FinEnum.equiv i then 1 else 0)
  Lawful.fromUnlawful <| .ofList [(monomial, (1 : R))]

/-- Extract the coefficient of a monomial. -/
def coeff {R : Type*} {σ : Type*} [FinEnum σ] [Zero R] (m : CMvMonomial σ) (p : CMvPolynomial σ R) :
    R :=
  p.1[m]?.getD 0

attribute [grind =] coeff.eq_def

/-- Extensionality: two polynomials are equal if all their coefficients are equal. -/
@[ext, grind ext]
theorem ext {σ : Type*} [FinEnum σ] [Zero R] (p q : CMvPolynomial σ R)
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
lemma fromUnlawful_zero {σ : Type*} [FinEnum σ] [Zero R] :
    Lawful.fromUnlawful 0 = (0 : Lawful σ R) := by
  unfold Lawful.fromUnlawful
  grind

variable {σ : Type*} [FinEnum σ] [CommSemiring R] {m : CMvMonomial σ} {p q : CMvPolynomial σ R}

@[simp, grind =]
lemma add_getD? : (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0 := by
  erw [Unlawful.filter_get]
  exact Unlawful.add_getD?

@[simp, grind =]
lemma coeff_add : coeff m (p + q) = coeff m p + coeff m q := by simp only [coeff, add_getD?]

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects the sum fold. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful₀
    {t : List (CMvMonomial σ × R)} {f : CMvMonomial σ → R → Unlawful σ R} :
    ∀ init : Unlawful σ R,
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

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects
    the fold over terms. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful {t : Unlawful σ R}
    {f : CMvMonomial σ → R → Unlawful σ R} :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
  ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t := by
  simp only [CMvMonomial.eq_1, ExtTreeMap.foldl_eq_foldl_toList]
  erw [fromUnlawful_fold_eq_fold_fromUnlawful₀ 0]
  simp
  rfl

end

/-- Evaluate a polynomial at a point given by a ring homomorphism `f`
    and variable assignments `vs`. -/
def eval₂ {R S : Type*} {σ : Type*} [FinEnum σ] [Semiring R] [CommSemiring S] :
    (R →+* S) → (σ → S) → CMvPolynomial σ R → S :=
  fun f vs p => ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1

/-- Term representation used by the fixed-order multivariate Horner evaluator. -/
abbrev HornerTerm (σ : Type*) [FinEnum σ] (S : Type*) := CMvMonomial σ × S

/-- Terms grouped by one variable exponent. -/
abbrev HornerGroup (σ : Type*) [FinEnum σ] (S : Type*) := ℕ × List (HornerTerm σ S)

/-- Read the exponent for a variable index represented as a natural number. -/
def hornerExponent {σ : Type*} [FinEnum σ] (k : ℕ) (m : CMvMonomial σ) : ℕ :=
  m[k]?.getD 0

/-- Add a term to an association list keyed by the current variable exponent. -/
def insertHornerTerm {σ : Type*} [FinEnum σ] {S : Type*}
    (exponent : ℕ) (term : HornerTerm σ S) :
    List (HornerGroup σ S) → List (HornerGroup σ S)
  | [] => [(exponent, [term])]
  | group :: groups =>
      if group.1 = exponent then
        (group.1, term :: group.2) :: groups
      else
        group :: insertHornerTerm exponent term groups

/-- Insert an exponent group into descending exponent order. -/
def insertHornerGroupDesc {σ : Type*} [FinEnum σ] {S : Type*}
    (group : HornerGroup σ S) : List (HornerGroup σ S) → List (HornerGroup σ S)
  | [] => [group]
  | group' :: groups =>
      if group'.1 < group.1 then
        group :: group' :: groups
      else
        group' :: insertHornerGroupDesc group groups

/-- Collect terms into association-list groups keyed by the current variable exponent. -/
def collectHornerGroups {σ : Type*} [FinEnum σ] {S : Type*}
    (k : ℕ) (terms : List (HornerTerm σ S)) : List (HornerGroup σ S) :=
  terms.foldl
    (fun groups term ↦ insertHornerTerm (hornerExponent k term.1) term groups) []

/-- Sort exponent groups from high exponent to low exponent. -/
def sortHornerGroups {σ : Type*} [FinEnum σ] {S : Type*}
    (groups : List (HornerGroup σ S)) : List (HornerGroup σ S) :=
  groups.foldl (fun sorted group ↦ insertHornerGroupDesc group sorted) []

/-- Group terms by the current variable exponent, sorted from high to low exponent. -/
def hornerGroups {σ : Type*} [FinEnum σ] {S : Type*}
    (k : ℕ) (terms : List (HornerTerm σ S)) : List (HornerGroup σ S) :=
  sortHornerGroups (collectHornerGroups k terms)

/-- Sparse Horner fold for already-evaluated coefficient groups. -/
def evalSparseHornerGroups {S : Type*} [CommSemiring S]
    (x : S) : List (ℕ × S) → S
  | [] => 0
  | group :: groups =>
      let state := groups.foldl
        (fun state group ↦
          let previousExponent := state.1
          let acc := state.2
          let exponent := group.1
          (exponent, acc * x ^ (previousExponent - exponent) + group.2))
        group
      state.2 * x ^ state.1

/-- Evaluate sparse multivariate terms by fixed-order Horner in variables `0, 1, ..., card σ-1`. -/
def eval₂HornerTerms {σ : Type*} [FinEnum σ] {S : Type*} [CommSemiring S]
    (xs : ℕ → S) : ℕ → ℕ → List (HornerTerm σ S) → S
  | 0, _, terms => terms.foldl (fun acc term ↦ acc + term.2) 0
  | fuel + 1, k, terms =>
      let groups := hornerGroups k terms
      let evaluatedGroups := groups.map fun group ↦
        (group.1, eval₂HornerTerms xs fuel (k + 1) group.2)
      evalSparseHornerGroups (xs k) evaluatedGroups

/-- Evaluate a polynomial using fixed-order multivariate Horner evaluation. -/
def eval₂Horner {R S : Type*} {σ : Type*} [FinEnum σ] [Semiring R] [CommSemiring S] :
    (R →+* S) → (σ → S) → CMvPolynomial σ R → S :=
  fun f vs p ↦
    let xs : ℕ → S := fun k ↦ if h : k < FinEnum.card σ then vs (FinEnum.equiv.symm ⟨k, h⟩) else 0
    let terms := p.1.toList.map fun term ↦ (term.1, f term.2)
    eval₂HornerTerms xs (FinEnum.card σ) 0 terms

/-- Evaluate a polynomial at a given point. -/
def eval {R : Type*} {σ : Type*} [FinEnum σ] [CommSemiring R] : (σ → R) → CMvPolynomial σ R → R :=
  eval₂ (RingHom.id _)

/-- Evaluate a polynomial at a given point using fixed-order multivariate Horner evaluation. -/
def evalHorner {R : Type*} {σ : Type*} [FinEnum σ] [CommSemiring R] :
    (σ → R) → CMvPolynomial σ R → R :=
  eval₂Horner (RingHom.id _)

/-- The support of a polynomial (set of monomials with non-zero coefficients),
    represented as Finsupps. -/
def support {R : Type*} {σ : Type*} [FinEnum σ] [Zero R] (p : CMvPolynomial σ R) :
    Finset (σ →₀ ℕ) :=
  (Lawful.monomials p).map CMvMonomial.toFinsupp |>.toFinset

/-- The total degree of a polynomial (maximum total degree of its monomials). -/
def totalDegree {R : Type*} {σ : Type*} [FinEnum σ] [Zero R] : CMvPolynomial σ R → ℕ :=
  fun p => Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
    (fun s => Finsupp.sum s (fun _ e => e))

/-- The degree of a polynomial in a specific variable. -/
def degreeOf {R : Type*} {σ : Type*} [FinEnum σ] [Zero R] (i : σ) : CMvPolynomial σ R → ℕ :=
  fun p => Finset.sup (Lawful.monomials p).toFinset (fun m => m.degreeOf i)

/-- Construct a monomial `c * m` as a `CMvPolynomial σ R`.

  Creates a polynomial with a single monomial term. If `c = 0`, returns the zero polynomial.
-/
def monomial {σ : Type*} [FinEnum σ] {R : Type*} [BEq R] [LawfulBEq R] [Zero R]
    (m : CMvMonomial σ) (c : R) : CMvPolynomial σ R :=
  if c == 0 then 0 else Lawful.fromUnlawful <| Unlawful.ofList [(m, c)]

/-- Multiset of all variable degrees appearing in the polynomial.

  Each variable `i` appears `degreeOf i p` times in the multiset.
-/
def degrees {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] (p : CMvPolynomial σ R) : Multiset σ :=
  Finset.univ.sum fun i => Multiset.replicate (p.degreeOf i) i

/-- `degreeOf` is the multiplicity of a variable in `degrees`. -/
lemma degreeOf_eq_count_degrees {σ : Type*} [FinEnum σ] {R : Type*} [Zero R]
    (i : σ) (p : CMvPolynomial σ R) :
    p.degreeOf i = Multiset.count i p.degrees := by
  classical
  unfold CMvPolynomial.degrees
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_ite_eq' Finset.univ i (fun j => p.degreeOf j)]
  simp

/-- Extract the set of variables that appear in a polynomial.

  Returns the set of variable indices `i : σ` such that `degreeOf i p > 0`.
-/
def vars {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] (p : CMvPolynomial σ R) : Finset σ :=
  Finset.univ.filter fun i => 0 < p.degreeOf i

/-- Filter a polynomial, keeping only monomials for which `keep m` is true. -/
def restrictBy {σ : Type*} [FinEnum σ] {R : Type*} [BEq R] [LawfulBEq R] [Zero R]
    (keep : CMvMonomial σ → Prop) [DecidablePred keep]
    (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  Lawful.fromUnlawful <| p.1.filter (fun m _ => decide (keep m))

/-- Restrict polynomial to monomials with total degree ≤ d.

  Filters out all monomials where `m.totalDegree > d`.
-/
def restrictTotalDegree {σ : Type*} [FinEnum σ] {R : Type*} [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  restrictBy (fun m => m.totalDegree ≤ d) p

/-- Restrict polynomial to monomials whose degree in each variable is ≤ d.

  Filters out all monomials where `m.degreeOf i > d` for some variable `i`.
-/
def restrictDegree {σ : Type*} [FinEnum σ] {R : Type*} [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  restrictBy (fun m => ∀ i : σ, m.degreeOf i ≤ d) p

end CMvPolynomial

end CPoly
