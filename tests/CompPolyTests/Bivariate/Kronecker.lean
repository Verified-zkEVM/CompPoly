/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Kronecker

/-!
  # Kronecker substitution tests

  Regressions for `kroneckerPack` / `kroneckerUnpack` packing coefficients and the
  round-trip recovery under the X-degree bound.
-/

namespace CompPoly
namespace CBivariate

/-- The X-degree of the monomial `X Y^2` is `1`. -/
private theorem natDegreeX_XY2 : natDegreeX (monomialXY 1 2 (1 : ℚ)) = 1 := by
  rw [natDegreeX_eq_natWeightedDegree, natWeightedDegree_monomialXY (by norm_num) 1 0]

/-- Packing `X Y^2` with stride `3` puts its coefficient at position `3 * 2 + 1 = 7`. -/
example : CPolynomial.coeff (kroneckerPack 3 (monomialXY 1 2 (1 : ℚ))) 7 = 1 := by
  rw [coeff_kroneckerPack (by norm_num) _ (by rw [natDegreeX_XY2]; omega)]
  rw [coeff_monomialXY, if_pos (by decide)]

/-- Positions that do not encode a monomial of `X Y^2` pack to `0`. -/
example : CPolynomial.coeff (kroneckerPack 3 (monomialXY 1 2 (1 : ℚ))) 5 = 0 := by
  rw [coeff_kroneckerPack (by norm_num) _ (by rw [natDegreeX_XY2]; omega)]
  rw [coeff_monomialXY, if_neg (by decide)]

/-- Round-trip: unpacking the packed monomial recovers it (stride `2 > natDegreeX = 1`). -/
example :
    kroneckerUnpack 2 (kroneckerPack 2 (monomialXY 1 2 (1 : ℚ))) = monomialXY 1 2 (1 : ℚ) := by
  apply kroneckerUnpack_kroneckerPack (by norm_num)
  rw [natDegreeX_XY2]; omega

end CBivariate
end CompPoly
