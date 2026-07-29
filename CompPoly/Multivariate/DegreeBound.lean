/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Univariate.ToPoly.Impl

/-!
# Degree-Bounded Computable Polynomials

Generic wrappers for computable univariate and multivariate polynomials bundled
with degree bounds.
-/

open CPoly Std

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `p` has individual degree at most `deg` when every monomial exponent is
bounded by `deg` in every coordinate. -/
def IndividualDegreeLE (deg : ℕ) (p : CMvPolynomial n R) : Prop :=
  letI := Classical.decEq R
  ∀ i : Fin n, ∀ mono ∈ Lawful.monomials p, mono.degreeOf i ≤ deg

end CPoly.CMvPolynomial

namespace CompPoly

/-- A computable univariate polynomial with `natDegree ≤ d`. -/
def CDegreeLE (R : Type) [BEq R] [Semiring R] [LawfulBEq R] (d : ℕ) :=
  { p : CPolynomial R // p.natDegree ≤ d }

/-- A computable multivariate polynomial with individual degree at most `d` in
every coordinate. -/
def CMvDegreeLE
    (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (n d : ℕ) :=
  { p : CMvPolynomial n R // CMvPolynomial.IndividualDegreeLE (R := R) d p }

end CompPoly
