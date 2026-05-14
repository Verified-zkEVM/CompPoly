/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.NTT.FastMul

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
  /-- Multiply two canonical polynomials while seeing the subproduct-tree level. -/
  mulAtLevel : Nat → CPolynomial R → CPolynomial R → CPolynomial R
  /-- The backend agrees with canonical polynomial multiplication at every level. -/
  mulAtLevel_eq_mul : ∀ level p q, mulAtLevel level p q = p * q

/-- Explicit remainder backend for algorithms that only need reduction modulo monic divisors. -/
structure ModContext (R : Type*) [Field R] [BEq R] [LawfulBEq R] where
  /-- Reduce the first polynomial modulo the second, assuming the divisor is monic. -/
  modByMonic : CPolynomial R → CPolynomial R → CPolynomial R
  /-- The backend agrees with the canonical monic-remainder operation. -/
  modByMonic_eq_modByMonic : ∀ p q, modByMonic p q = CPolynomial.modByMonic p q

namespace MulContext

/-- The default multiplication context, backed by canonical `CPolynomial` multiplication. -/
def naive [Semiring R] [BEq R] [LawfulBEq R] : MulContext R where
  mulAtLevel _ p q := p * q
  mulAtLevel_eq_mul _ _ _ := rfl

/--
Subproduct-tree NTT-backed multiplication context with canonical multiplication as a fallback.

At subproduct-tree level `level`, this context uses an NTT domain with
`logN = min (level + 2) maxLogN`. If the selected domain is still too small for
the current operands, the backend falls back to ordinary `CPolynomial`
multiplication.
-/
def ntt [Field R] [BEq R] [LawfulBEq R]
    (maxLogN : Nat) (domainOfLogN : (logN : Nat) → logN ≤ maxLogN → NTT.Domain R) :
    MulContext R where
  mulAtLevel level p q :=
    let D := domainOfLogN (min (level + 2) maxLogN) (Nat.min_le_right _ _)
    if hfit : NTT.Domain.requiredLength p.val q.val ≤ 2 ^ D.logN then
      NTT.FastMul.fastMulImpl D p q
    else
      p * q
  mulAtLevel_eq_mul level p q := by
    let D := domainOfLogN (min (level + 2) maxLogN) (Nat.min_le_right _ _)
    by_cases hfit :
        NTT.Domain.requiredLength p.val q.val ≤ 2 ^ D.logN
    · simp [D, hfit, NTT.FastMul.fastMulImpl_eq_mul D p q (by
        simpa [NTT.Domain.fits, NTT.Domain.n] using hfit)]
    · simp [D, hfit]

end MulContext

namespace ModContext

/-- The default monic-remainder context, backed by `CPolynomial.modByMonic`. -/
def naive [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.modByMonic p q
  modByMonic_eq_modByMonic _ _ := rfl

/-- A remainder-only compiled backend for monic remainders. -/
def fast [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.modByMonicFast p q
  modByMonic_eq_modByMonic p q := CPolynomial.modByMonicFast_eq_modByMonic p q

end ModContext

end CPolynomial
end CompPoly
