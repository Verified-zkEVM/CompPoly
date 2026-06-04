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

/-!
# Raw Univariate Algorithm Contexts

Array-level execution dictionaries for reusable raw univariate polynomial
kernels.
-/

namespace CompPoly

namespace CPolynomial

namespace Raw

variable {R : Type*}

/-- Internal raw multiplication backend for array-level polynomial kernels. -/
structure MulContext (R : Type*) [Semiring R] [BEq R] [LawfulBEq R] where
  /-- Multiply two raw polynomials, returning the trimmed raw product. -/
  mul : CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  /-- The backend agrees with raw polynomial multiplication. -/
  mul_eq_mul : ∀ p q, mul p q = p * q

/-- Internal raw monic-remainder backend for array-level polynomial kernels. -/
structure ModContext (R : Type*) [Field R] [BEq R] [LawfulBEq R] where
  /-- Reduce the first raw polynomial modulo the second raw monic divisor. -/
  modByMonic : CPolynomial.Raw R → CPolynomial.Raw R → CPolynomial.Raw R
  /-- The backend agrees with raw monic remainders for canonical raw inputs. -/
  modByMonic_eq_modByMonic :
    ∀ p q, p.trim = p → q.trim = q → modByMonic p q = CPolynomial.Raw.modByMonic p q

namespace MulContext

/-- The default raw multiplication context, backed by raw polynomial multiplication. -/
def naive [Semiring R] [BEq R] [LawfulBEq R] : MulContext R where
  mul p q := p * q
  mul_eq_mul _ _ := rfl

/-- NTT-backed raw multiplication context with raw multiplication for unsupported lengths. -/
def ntt [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    MulContext R where
  mul p q :=
    let requiredLen := NTT.Domain.requiredLength p q
    match bestDomainForLength? requiredLen with
    | some ⟨D, _⟩ => (NTT.FastMul.Raw.fastMulImpl D p q).trim
    | none => p * q
  mul_eq_mul p q := by
    let requiredLen := NTT.Domain.requiredLength p q
    cases hdomain : bestDomainForLength? requiredLen with
    | none =>
        simp [hdomain, requiredLen]
    | some fitted =>
        rcases fitted with ⟨D, hfit⟩
        simp [hdomain, requiredLen, NTT.FastMul.Raw.fastMulImpl_trim_eq_mul D p q (by
          simpa [NTT.Domain.fits] using hfit)]

/-- NTTFast-backed raw multiplication context with raw multiplication for unsupported lengths. -/
def nttFast [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    MulContext R where
  mul p q :=
    let requiredLen := NTT.Domain.requiredLength p q
    match bestDomainForLength? requiredLen with
    | some ⟨D, _⟩ => (NTTFast.Raw.fastMulImpl D p q).trim
    | none => p * q
  mul_eq_mul p q := by
    let requiredLen := NTT.Domain.requiredLength p q
    cases hdomain : bestDomainForLength? requiredLen with
    | none =>
        simp [hdomain, requiredLen]
    | some fitted =>
        rcases fitted with ⟨D, hfit⟩
        simp [hdomain, requiredLen, NTTFast.Raw.fastMulImpl_trim_eq_mul D p q (by
          simpa [NTT.Domain.fits] using hfit)]

end MulContext

namespace ModContext

/-- The default raw monic-remainder context, backed by raw `modByMonic`. -/
def naive [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.Raw.modByMonic p q
  modByMonic_eq_modByMonic _ _ _ _ := rfl

/-- Raw remainder-only monic-remainder context. -/
def remainderOnly [Field R] [BEq R] [LawfulBEq R] : ModContext R where
  modByMonic p q := CPolynomial.Raw.modByMonicRemainderOnly p q
  modByMonic_eq_modByMonic p q _ _ := CPolynomial.Raw.modByMonicRemainderOnly_eq_modByMonic p q

/-- Raw reversal-based monic-remainder context parameterized by low-product multiplication. -/
def reversal [Field R] [BEq R] [LawfulBEq R]
    (M : Raw.MulLowContext R) : ModContext R where
  modByMonic p q := CPolynomial.Raw.modByMonicByReversal M p q
  modByMonic_eq_modByMonic p q hp hq := by
    have h := congrArg Subtype.val
      (CPolynomial.modByMonicByReversal_eq_modByMonic M
        (CPolynomial.ofArray p) (CPolynomial.ofArray q))
    simpa [CPolynomial.ofArray, hp, hq] using h

/-- Raw monic remainders by reversal, using an NTT low-product backend. -/
def reversalNtt [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    ModContext R :=
  reversal (NTT.FastMulLow.withFallback bestDomainForLength?)

/-- Raw monic remainders by reversal, using an NTTFast low-product backend. -/
def reversalNttFast [Field R] [BEq R] [LawfulBEq R]
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (NTT.FittingDomain R requiredLen)) :
    ModContext R :=
  reversal (NTTFast.FastMulLow.withFallback bestDomainForLength?)

end ModContext

end Raw

end CPolynomial

end CompPoly
