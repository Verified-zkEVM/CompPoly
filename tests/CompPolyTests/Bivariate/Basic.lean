/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Bivariate.ToPoly

/-!
  # Bivariate Basic Tests

  Lightweight regressions for the canonical Y-facing API and its `toPoly` transport.
-/

namespace CompPoly
namespace CBivariate

example (f : CBivariate ℚ) : (toPoly f).natDegree = f.natDegreeY := by
  simpa using natDegreeY_toPoly (R := ℚ) (f := f)

example (f : CBivariate ℚ) :
    (leadingCoeffY (R := ℚ) f).toPoly = (toPoly f).leadingCoeff := by
  simpa using leadingCoeffY_toPoly (R := ℚ) (f := f)

example : coeff (R := ℚ) (monomialXY (R := ℚ) 2 1 5) 2 1 = 5 := by
  change ((CPolynomial.monomial 1 (CPolynomial.monomial (R := ℚ) 2 5)).coeff 1).coeff 2 = 5
  have h_outer :
      (CPolynomial.monomial 1 (CPolynomial.monomial (R := ℚ) 2 5)).coeff 1 =
        CPolynomial.monomial (R := ℚ) 2 5 := by
    simpa using
      (CPolynomial.coeff_monomial (R := CPolynomial ℚ) 1 1
        (CPolynomial.monomial (R := ℚ) 2 5))
  rw [h_outer]
  simpa using (CPolynomial.coeff_monomial (R := ℚ) 2 2 5)

end CBivariate
end CompPoly
