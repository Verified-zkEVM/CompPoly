/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.FastMul

/-!
# Low Product via NTT

This file exposes an NTT-backed `Raw.MulLowContext` for computing the low
coefficients of a raw polynomial product.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace FastMulLow

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

omit [BEq R] [LawfulBEq R] in
private theorem truncate_coeff_of_lt (k : Nat) (p : CPolynomial.Raw R) {i : Nat}
    (hi : i < k) : (CPolynomial.Raw.truncate k p).coeff i = p.coeff i := by
  simp [CPolynomial.Raw.truncate, CPolynomial.Raw.coeff, Array.getElem?_extract, hi]
  by_cases hp : i < p.size
  · simp [hp]
  · simp [hp]

private theorem mul_truncate_inputs_coeff_of_lt (k : Nat) (p q : CPolynomial.Raw R)
    {i : Nat} (hi : i < k) :
    ((CPolynomial.Raw.truncate k p) * (CPolynomial.Raw.truncate k q)).coeff i =
      (p * q).coeff i := by
  rw [CPolynomial.Raw.mul_coeff, CPolynomial.Raw.mul_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < i + 1 := Finset.mem_range.mp hj
  have hjle : j ≤ i := Nat.le_of_lt_succ hjlt
  have hjk : j < k := Nat.lt_of_le_of_lt hjle hi
  have hik : i - j < k := Nat.lt_of_le_of_lt (Nat.sub_le i j) hi
  rw [truncate_coeff_of_lt k p hjk, truncate_coeff_of_lt k q hik]

private def run
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (FittingDomain R requiredLen))
    (k : Nat) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  match bestDomainForLength?
      (Domain.requiredLength (CPolynomial.Raw.truncate k p) (CPolynomial.Raw.truncate k q)) with
  | some ⟨D, _⟩ =>
      CPolynomial.Raw.truncate k
        (FastMul.Raw.fastMulImpl D (CPolynomial.Raw.truncate k p)
          (CPolynomial.Raw.truncate k q))
  | none =>
      (CPolynomial.Raw.MulLowContext.convolution (R := R)).mulLow k p q

/--
NTT-backed low-product context with low-convolution as a fallback.

This truncates both inputs to the requested output precision, multiplies them
with the selected fitting NTT domain when one is available, and truncates the
result back to the requested precision. If the domain table cannot cover the
requested product length, it falls back to the low-convolution backend.
-/
def withFallback
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (FittingDomain R requiredLen)) :
    CPolynomial.Raw.MulLowContext R where
  mulLow := run bestDomainForLength?
  size_le := by
    intro k p q
    unfold run
    cases hdomain :
        bestDomainForLength?
          (Domain.requiredLength (CPolynomial.Raw.truncate k p)
            (CPolynomial.Raw.truncate k q)) with
    | none =>
        simpa [hdomain] using
          (CPolynomial.Raw.MulLowContext.convolution (R := R)).size_le k p q
    | some fitted =>
        rcases fitted with ⟨D, hfit⟩
        simp [CPolynomial.Raw.truncate]
  coeff_of_lt := by
    intro k p q i hi
    unfold run
    cases hdomain :
        bestDomainForLength?
          (Domain.requiredLength (CPolynomial.Raw.truncate k p)
            (CPolynomial.Raw.truncate k q)) with
    | none =>
        simpa [hdomain] using
          (CPolynomial.Raw.MulLowContext.convolution (R := R)).coeff_of_lt k p q i hi
    | some fitted =>
        rcases fitted with ⟨D, hfit⟩
        rw [truncate_coeff_of_lt]
        · have hfast :
              (FastMul.Raw.fastMulImpl D (CPolynomial.Raw.truncate k p)
                (CPolynomial.Raw.truncate k q)).coeff i =
              ((CPolynomial.Raw.truncate k p) * (CPolynomial.Raw.truncate k q)).coeff i := by
            rw [← CPolynomial.Raw.Trim.coeff_eq_coeff
              (FastMul.Raw.fastMulImpl D (CPolynomial.Raw.truncate k p)
                (CPolynomial.Raw.truncate k q)) i]
            have htrim := FastMul.Raw.fastMulImpl_trim_eq_mul D
              (CPolynomial.Raw.truncate k p) (CPolynomial.Raw.truncate k q)
              (by
                simpa [Domain.fits] using hfit)
            rw [htrim]
          exact hfast.trans (mul_truncate_inputs_coeff_of_lt k p q hi)
        · exact hi

end FastMulLow
end NTT
end CPolynomial
end CompPoly
