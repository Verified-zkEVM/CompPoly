/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Univariate.NTT.FastMulLow
import CompPoly.Univariate.NTTFast.Correctness.Pipeline
import CompPoly.Univariate.NTTFast.FastMulLow
import CompPoly.Univariate.Raw.Context

/-!
# Univariate Algorithm Contexts

Algorithm dictionaries for reusable univariate polynomial operations, including
canonical, NTT, and NTTFast-backed implementations.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

/-- Explicit multiplication backend for univariate polynomial algorithms. -/
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

/--
NTT-backed multiplication context with canonical multiplication as a fallback.

The context asks the selector for a domain that fits the current operands. If no
supported domain is available, it falls back to ordinary `CPolynomial`
multiplication.
-/
def ntt [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    MulContext R where
  mul := NTT.FastMul.withFallback bestDomainForLength?
  mul_eq_mul := NTT.FastMul.withFallback_eq_mul bestDomainForLength?

/--
NTTFast-backed multiplication context with canonical multiplication as a fallback.

The context asks the selector for a domain that fits the current operands. If no
supported domain is available, it falls back to ordinary `CPolynomial`
multiplication.
-/
def nttFast [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    MulContext R where
  mul := NTTFast.withFallback bestDomainForLength?
  mul_eq_mul := NTTFast.withFallback_eq_mul bestDomainForLength?

end MulContext

namespace ModContext

/-- The default monic-remainder context, backed by `CPolynomial.modByMonic`. -/
def naive [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.modByMonic p q
  modByMonic_eq_modByMonic _ _ := rfl

/-- A remainder-only backend for monic remainders. -/
def remainderOnly [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.modByMonicRemainderOnly p q
  modByMonic_eq_modByMonic p q := CPolynomial.modByMonicRemainderOnly_eq_modByMonic p q

/-- A reversal-based monic-remainder backend parameterized by low-product multiplication. -/
def reversal [Field R] [BEq R] [LawfulBEq R]
    (M : Raw.MulLowContext R) : ModContext R where
  modByMonic p q := CPolynomial.modByMonicByReversal M p q
  modByMonic_eq_modByMonic p q := CPolynomial.modByMonicByReversal_eq_modByMonic M p q

/-- Monic remainders by reversal, using an NTT low-product backend. -/
def reversalNtt [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    ModContext R :=
  reversal (NTT.FastMulLow.withFallback bestDomainForLength?)

/-- Monic remainders by reversal, using an NTTFast low-product backend. -/
def reversalNttFast [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    ModContext R :=
  reversal (NTTFast.FastMulLow.withFallback bestDomainForLength?)

end ModContext

end CPolynomial
end CompPoly
