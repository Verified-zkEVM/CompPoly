/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen
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

## Main definitions

* `CPoly.CMvPolynomial n R`: The type of multivariate polynomials in `n` variables
  with coefficients in `R`.
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

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects
    the fold over terms. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful {t : Unlawful n R}
    {f : CMvMonomial n → R → Unlawful n R} :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
  ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t := by
  simp only [CMvMonomial.eq_1, ExtTreeMap.foldl_eq_foldl_toList]
  erw [fromUnlawful_fold_eq_fold_fromUnlawful₀ 0]
  simp
  rfl

end

/-- Evaluate a polynomial at a point given by a ring homomorphism `f`
    and variable assignments `vs`. -/
def eval₂ {R S : Type} {n : ℕ} [Semiring R] [CommSemiring S] :
    (R →+* S) → (Fin n → S) → CMvPolynomial n R → S :=
  fun f vs p => ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1

/-- Evaluate a polynomial at a given point. -/
def eval {R : Type} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvPolynomial n R → R :=
  eval₂ (RingHom.id _)

/-- The support of a polynomial (set of monomials with non-zero coefficients),
    represented as Finsupps. -/
def support {R : Type} {n : ℕ} [Zero R] (p : CMvPolynomial n R) : Finset (Fin n →₀ ℕ) :=
  (Lawful.monomials p).map CMvMonomial.toFinsupp |>.toFinset

/-- The total degree of a polynomial (maximum total degree of its monomials). -/
def totalDegree {R : Type} {n : ℕ} [inst : CommSemiring R] : CMvPolynomial n R → ℕ :=
  fun p => Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
    (fun s => Finsupp.sum s (fun _ e => e))

/-- The degree of a polynomial in a specific variable. -/
def degreeOf {R : Type} {n : ℕ} [Zero R] (i : Fin n) : CMvPolynomial n R → ℕ :=
  fun p =>
    Multiset.count i
    (Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
      fun s => Finsupp.toMultiset s)

/-- Construct a monomial `c * m` as a `CMvPolynomial n R`.

  Creates a polynomial with a single monomial term. If `c = 0`, returns the zero polynomial.
-/
def monomial {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (m : CMvMonomial n) (c : R) : CMvPolynomial n R :=
  if c == 0 then 0 else Lawful.fromUnlawful <| Unlawful.ofList [(m, c)]

/-- Monomial ordering typeclass for `n` variables.

  Provides a way to compare monomials for determining leading terms.
-/
class MonomialOrder (n : ℕ) where
  compare : CMvMonomial n → CMvMonomial n → Ordering
  -- TODO: Add ordering axioms (transitivity, etc.)

/-- Degree of a monomial according to a monomial order.

  Returns the degree of a monomial as determined by the ordering.
  The exact meaning depends on the specific monomial order implementation
  (e.g., total degree for graded orders, weighted degree, etc.).
-/
def MonomialOrder.degree {n : ℕ} [MonomialOrder n] (m : CMvMonomial n) : ℕ :=
  sorry

/-- Leading monomial of a polynomial according to a monomial order.

  Returns `none` for the zero polynomial.
-/
def leadingMonomial {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : Option (CMvMonomial n) :=
  sorry

/-- Leading coefficient of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial.
-/
def leadingCoeff {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : R :=
  sorry

/-- Multiset of all variable degrees appearing in the polynomial.

  Each variable `i` appears `degreeOf i p` times in the multiset.
-/
def degrees {n : ℕ} {R : Type} [Zero R] (p : CMvPolynomial n R) : Multiset (Fin n) :=
  Finset.univ.sum fun i => Multiset.replicate (p.degreeOf i) i

/-- Extract the set of variables that appear in a polynomial.

  Returns the set of variable indices `i : Fin n` such that `degreeOf i p > 0`.
-/
def vars {n : ℕ} {R : Type} [Zero R] (p : CMvPolynomial n R) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < p.degreeOf i

/-- `degreeOf` is the multiplicity of a variable in `degrees`. -/
lemma degreeOf_eq_count_degrees {n : ℕ} {R : Type} [Zero R]
    (i : Fin n) (p : CMvPolynomial n R) :
    p.degreeOf i = Multiset.count i p.degrees := by
  classical
  unfold CMvPolynomial.degrees
  symm
  calc
    Multiset.count i (∑ j, Multiset.replicate (p.degreeOf j) j)
        = ∑ j ∈ Finset.univ, Multiset.count i (Multiset.replicate (p.degreeOf j) j) := by
          simpa [Finset.sum] using
            (Multiset.count_sum' (s := Finset.univ)
              (a := i) (f := fun j => Multiset.replicate (p.degreeOf j) j))
    _ = ∑ j ∈ Finset.univ, if j = i then p.degreeOf j else 0 := by
          simp [Multiset.count_replicate, eq_comm]
    _ = p.degreeOf i := by
          simp

/-- Restrict polynomial to monomials with total degree ≤ d.

  Filters out all monomials where `m.totalDegree > d`.
-/
def restrictBy {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (keep : CMvMonomial n → Prop) [DecidablePred keep]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  Lawful.fromUnlawful <| p.1.filter (fun m _ => decide (keep m))

def restrictTotalDegree {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial n R) : CMvPolynomial n R :=
  restrictBy (fun m => m.totalDegree ≤ d) p

/-- Restrict polynomial to monomials whose degree in each variable is ≤ d.

  Filters out all monomials where `m.degreeOf i > d` for some variable `i`.
-/
def restrictDegree {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial n R) : CMvPolynomial n R :=
  restrictBy (fun m => ∀ i : Fin n, m.degreeOf i ≤ d) p

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

/-- `CMvPolynomial n R` forms a commutative ring when `R` is a commutative ring.

  Extends the `CommSemiring` structure with subtraction.

  TODO: Requires `CommSemiring` instance (defined in MvPolyEquiv.lean).
  TODO: Verify Neg/Sub operations exist in Lawful.lean.
  Note: Cannot import MvPolyEquiv.lean due to circular dependency, so all fields are `sorry`.
-/
instance {n : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R] :
    CommRing (CMvPolynomial n R) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  npow := sorry
  npow_zero := sorry
  npow_succ := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  mul_comm := sorry

/-- Convert sum representation to iterative form.

  TODO: Clarify intended behavior - may be related to converting between different
  polynomial representations or evaluation strategies.
-/
def sumToIter {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  sorry

end CMvPolynomial

-- TODO: Phase 1 items requiring Semiring/CommSemiring instances from MvPolyEquiv.lean
--       (circular dependency):
-- TODO: `Algebra R (CMvPolynomial n R)` instance
-- TODO: `Module R (CMvPolynomial n R)` instance
-- TODO: `finSuccEquiv` - Equivalence between (n+1)-variable and n-variable polynomials
-- TODO: `optionEquivLeft` - Equivalence for option-indexed variables
-- See MvPolyEquiv.lean for: eval₂Hom, isEmptyRingEquiv, SMulZeroClass

end CPoly
