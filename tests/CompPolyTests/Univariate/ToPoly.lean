import CompPoly.Univariate.ToPoly

namespace CompPoly
namespace CPolynomial

-- TODO: add focused edge cases for degree/leadingCoeff transport once API settles.

example (p : Polynomial ℚ) : p.toImpl.toPoly = p := by
  simpa using Raw.toPoly_toImpl (Q := ℚ) (p := p)

example (p : CPolynomial.Raw ℚ) : p.toPoly.toImpl = p.trim := by
  simp [Raw.toImpl_toPoly]

example (p : CPolynomial ℚ) : p.toPoly.toImpl = p := by
  simp [toImpl_toPoly_of_canonical]

example (p q : CPolynomial ℚ) : (p + q).toPoly = p.toPoly + q.toPoly := by
  simp [toPoly_add]

example (p q : CPolynomial ℚ) : (p * q).toPoly = p.toPoly * q.toPoly := by
  simp [toPoly_mul]

example (r : ℚ) : (C r).toPoly = Polynomial.C r := by
  simp [C_toPoly]

end CPolynomial
end CompPoly
