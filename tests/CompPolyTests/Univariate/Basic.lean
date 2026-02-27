import CompPoly.Univariate.Basic

namespace CompPoly
namespace CPolynomial

-- TODO: expand this file with more operation-level regression checks.

example (r : ℚ) : (C r).coeff 0 = r := by
  simpa using coeff_C (R := ℚ) r 0

example (r : ℚ) : (C r).coeff 3 = 0 := by
  simpa using coeff_C (R := ℚ) r 3

example : (X : CPolynomial ℚ).coeff 1 = 1 := by
  native_decide

example (p : CPolynomial ℚ) : (divX p).coeff 2 = p.coeff 3 := by
  simpa using coeff_divX (R := ℚ) p 2

example (p : CPolynomial ℚ) : p + 0 = p := by
  simp

example (p : CPolynomial ℚ) : 0 + p = p := by
  simp

example (p : CPolynomial ℚ) : p * 0 = 0 := by
  simp

example (p : CPolynomial ℚ) : 1 * p = p := by
  simp

end CPolynomial
end CompPoly
