import CompPoly.Univariate.Raw

namespace CompPoly
namespace CPolynomial.Raw

/-- Regression test for issue #115: `(X^2 - 1) / (X + 1) = X - 1` with zero remainder. -/
example :
    divByMonic ((X : CPolynomial.Raw ℚ) ^ 2 - C 1) ((X : CPolynomial.Raw ℚ) + C 1)
      = #[-(1 : ℚ), 1] := by
  native_decide

example :
    modByMonic ((X : CPolynomial.Raw ℚ) ^ 2 - C 1) ((X : CPolynomial.Raw ℚ) + C 1)
      = #[] := by
  native_decide

/-- Regression test for review-thread case: `X^3 = (X^2 + 1) * X + (-X)`. -/
example :
    divByMonic ((X : CPolynomial.Raw ℚ) ^ 3) ((X : CPolynomial.Raw ℚ) ^ 2 + C 1)
      = #[(0 : ℚ), 1] := by
  native_decide

example :
    modByMonic ((X : CPolynomial.Raw ℚ) ^ 3) ((X : CPolynomial.Raw ℚ) ^ 2 + C 1)
      = #[(0 : ℚ), -(1 : ℚ)] := by
  native_decide

end CPolynomial.Raw
end CompPoly
