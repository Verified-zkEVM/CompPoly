/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Multivariate.UnivariateEquiv

/-!
  # Multivariate Univariate-Bridge Tests

  Compile-time regressions for the dedicated computable
  `CMvPolynomial 1 R ≃+* CPolynomial R` bridge.
-/

namespace CPoly

namespace CMvPolynomial

open CompPoly

example (p : CMvPolynomial 1 ℚ) : ofUnivariate (toUnivariate p) = p := by
  exact ofUnivariate_toUnivariate (R := ℚ) p

example (p : CompPoly.CPolynomial ℚ) : toUnivariate (ofUnivariate p) = p := by
  exact toUnivariate_ofUnivariate (R := ℚ) p

example (p q : CMvPolynomial 1 ℚ) :
    univariateRingEquiv (R := ℚ) (p + q) =
      univariateRingEquiv (R := ℚ) p + univariateRingEquiv (R := ℚ) q := by
  exact (univariateRingEquiv (R := ℚ)).map_add p q

example (p q : CMvPolynomial 1 ℚ) :
    univariateRingEquiv (R := ℚ) (p * q) =
      univariateRingEquiv (R := ℚ) p * univariateRingEquiv (R := ℚ) q := by
  exact (univariateRingEquiv (R := ℚ)).map_mul p q

example (p : CMvPolynomial 1 ℚ) (n : ℕ) :
    CompPoly.CPolynomial.coeff (toUnivariate p) n =
      coeff (univariateMonomial n) p := by
  simpa using coeff_toUnivariate (R := ℚ) p n

example (p : CompPoly.CPolynomial ℚ) (n : ℕ) :
    coeff (univariateMonomial n) (ofUnivariate p) =
      CompPoly.CPolynomial.coeff p n := by
  simpa using coeff_ofUnivariate (R := ℚ) p n

example :
    coeff (univariateMonomial 1) (ofUnivariate (CompPoly.CPolynomial.X (R := ℚ))) = 1 := by
  rw [coeff_ofUnivariate]
  simp [CompPoly.CPolynomial.coeff, CompPoly.CPolynomial.X,
    CompPoly.CPolynomial.Raw.X, CompPoly.CPolynomial.Raw.coeff]

example :
    coeff (univariateMonomial 0) (ofUnivariate (CompPoly.CPolynomial.X (R := ℚ))) = 0 := by
  rw [coeff_ofUnivariate]
  simp [CompPoly.CPolynomial.coeff, CompPoly.CPolynomial.X,
    CompPoly.CPolynomial.Raw.X, CompPoly.CPolynomial.Raw.coeff]

example (c : ℚ) :
    coeff (univariateMonomial 0) (ofUnivariate (CompPoly.CPolynomial.C c)) = c := by
  rw [coeff_ofUnivariate, CompPoly.CPolynomial.coeff_C]
  simp

end CMvPolynomial

end CPoly
