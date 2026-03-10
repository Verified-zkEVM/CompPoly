/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Desmond Coles, Derek Sorensen
-/
import CompPoly.Univariate.Basic

/-!
# Linear Algebra API for Computable Univariate Polynomials

This file contains linear-map and bounded-degree submodule constructions for `CPolynomial`.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*} [BEq R]

section LinearTheory

variable [Semiring R] [LawfulBEq R]

/-- This is an R-linear function that returns the coefficient of X^n. -/
def lcoeff (S : Type*) [BEq S] [Semiring S] [LawfulBEq S] (n : ℕ) : (CPolynomial S) →ₗ[S] S where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

/-- The `R`-submodule of `CPolynomial R` consisting of polynomials of degree ≤ `n`. -/
def degreeLE (S : Type*) [BEq S] [Semiring S] [LawfulBEq S] (n : WithBot ℕ) :
    Submodule S (CPolynomial S) :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff S k)

/-- The `R`-submodule of `CPolynomial R` consisting of polynomials of degree < `n`. -/
def degreeLT (S : Type*) [BEq S] [Semiring S] [LawfulBEq S] (n : ℕ) :
    Submodule S (CPolynomial S) :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff S k)

/-- The forward map of `degreeLTEquiv` preserves addition:
  extracting coefficients commutes with polynomial addition.  -/
lemma degreeLTEquiv_map_add (n : ℕ)
    (p q : ↥(degreeLT R n)) :
    (fun i : Fin n => coeff (↑(p + q) : CPolynomial R) (↑i)) =
    (fun i : Fin n => coeff (↑p : CPolynomial R) (↑i) + coeff (↑q : CPolynomial R) (↑i)) := by
  exact funext fun i => coeff_add _ _ _

/-- The forward map of `degreeLTEquiv` preserves scalar multiplication:
  extracting coefficients commutes with scalar multiplication. -/
lemma degreeLTEquiv_map_smul (n : ℕ)
    (r : R) (p : ↥(degreeLT R n)) :
    (fun i : Fin n => coeff (↑(r • p) : CPolynomial R) (↑i)) =
    (fun i : Fin n => r * coeff (↑p : CPolynomial R) (↑i)) := by
  exact funext fun i => coeff_smul r ↑p i

/-- The first `n` coefficients on `degreeLT n` define a linear map to `Fin n → R`.

  This is the computable polynomial analogue of `Polynomial.degreeLTEquiv`.

  The map sends a polynomial `p` with `degree p < n` to the function
  `i ↦ coeff p i` for `i : Fin n`. -/
def degreeLTEquiv (S : Type*) [BEq S] [Semiring S] [LawfulBEq S] [DecidableEq S] (n : ℕ) :
    degreeLT S n →ₗ[S] (Fin n → S) where
  toFun p i := coeff p.1 i
  map_add' := fun p q => degreeLTEquiv_map_add n p q
  map_smul' := fun r p => degreeLTEquiv_map_smul n r p

end LinearTheory

end CPolynomial

end CompPoly
