/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Basic

/-!
# Formal Derivatives for Computable Univariate Polynomials
-/

namespace CompPoly

namespace CPolynomial

/-- Formal derivative of a canonical univariate polynomial. -/
def derivative {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CPolynomial R :=
  ofArray
    ((List.range (p.val.size - 1)).map fun i ↦
      ((i + 1 : Nat) : R) * p.coeff (i + 1)).toArray

end CPolynomial

end CompPoly
