/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Kronecker
import CompPolyTests.Bivariate.KroneckerCommon

/-!
  # Kronecker substitution tests

  Packing coefficients and round-trip recovery for `kroneckerPack` / `kroneckerUnpack`,
  followed by a runtime check that, on small KoalaBear data, each pipeline (schoolbook,
  classic NTT, recursive NTT) returns the same product as direct multiplication. The full
  timing comparison lives in `KroneckerBenchmark.lean`.
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

/- Each pipeline must return the same product as direct multiplication on small data. -/
#eval show IO Unit from do
  let n := 4
  let D := 2 * n
  let p := TestCommon.mkBiv n n 41
  let q := TestCommon.mkBiv n n 73
  let expected := p * q
  let kron := TestCommon.kronWith (· * ·) D p q
  let ntt := TestCommon.kronWith
    (CPolynomial.NTT.FastMul.withFallback TestCommon.bestDomainForLength?) D p q
  let fast := TestCommon.kronWith
    (CPolynomial.NTTFast.withFallback TestCommon.bestDomainForLength?) D p q
  unless (kron == expected) && (ntt == expected) && (fast == expected) do
    throw <| IO.userError "a Kronecker pipeline disagreed with direct multiplication"

end CBivariate
end CompPoly
