/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Univariate.Basic

/-!
# Formal Derivative of Computable Univariate Polynomials

Defines the formal derivative `CPolynomial.derivative` and proves its
core properties.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

section Definition

/-- The formal derivative of a computable polynomial.
    Coefficient `n` of the result is `coeff p (n+1) * (n+1)`. -/
def derivative [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CPolynomial R :=
  sorry

end Definition

section Coefficients

/-- Coefficient formula for the derivative. -/
theorem coeff_derivative [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (↑(n + 1) : R) :=
  sorry

end Coefficients

section BasicLemmas

/-- The derivative of the zero polynomial is zero. -/
theorem derivative_zero [Semiring R] [BEq R] [LawfulBEq R] :
    derivative (0 : CPolynomial R) = 0 :=
  sorry

/-- The derivative of a constant is zero. -/
theorem derivative_C [Semiring R] [BEq R] [LawfulBEq R] (r : R) :
    derivative (C r) = 0 :=
  sorry

/-- The derivative of a monomial. -/
theorem derivative_monomial [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (r : R) :
    derivative (monomial n r) =
      monomial (n - 1) (r * (↑n : R)) :=
  sorry

/-- The derivative distributes over addition. -/
theorem derivative_add [Semiring R] [DecidableEq R]
    [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    derivative (p + q) = derivative p + derivative q :=
  sorry

end BasicLemmas

end CPolynomial

end CompPoly
