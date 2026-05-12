/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.Basic

/-!
# Batch Evaluation Contexts

Algorithm dictionaries for univariate batch-evaluation implementations.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

/-- Explicit multiplication backend for algorithms that should not replace the canonical `Mul`
instance on `CPolynomial R`. -/
structure MulContext (R : Type*) [Semiring R] [BEq R] [LawfulBEq R] where
  /-- Multiply two canonical polynomials. -/
  mul : CPolynomial R → CPolynomial R → CPolynomial R
  /-- The backend agrees with canonical polynomial multiplication. -/
  mul_eq_mul : ∀ p q, mul p q = p * q

/-- Explicit remainder backend for algorithms that only need reduction modulo monic divisors. -/
structure ModContext (R : Type*) [Field R] [BEq R] [LawfulBEq R] where
  /-- Reduce the first polynomial modulo the second, assuming the divisor is monic. -/
  modByMonic : CPolynomial R → CPolynomial R → CPolynomial R
  /-- The backend agrees with the canonical monic-remainder operation. -/
  modByMonic_eq_modByMonic : ∀ p q, modByMonic p q = CPolynomial.modByMonic p q

namespace MulContext

/-- The default multiplication context, backed by canonical `CPolynomial` multiplication. -/
def naive [Semiring R] [BEq R] [LawfulBEq R] : MulContext R where
  mul p q := p * q
  mul_eq_mul _ _ := rfl

end MulContext

namespace ModContext

/-- The default monic-remainder context, backed by `CPolynomial.modByMonic`. -/
def naive [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.modByMonic p q
  modByMonic_eq_modByMonic _ _ := rfl

end ModContext

end CPolynomial
end CompPoly
