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
  exact of_univariate_to_univariate p

example (p : CPolynomial ℚ) : toUnivariate (ofUnivariate p) = p := by
  exact to_univariate_of_univariate p

example (p q : CMvPolynomial 1 ℚ) :
    univariateRingEquiv (p + q) = univariateRingEquiv p + univariateRingEquiv q := by
  exact (univariateRingEquiv (R := ℚ)).map_add p q

example (p q : CMvPolynomial 1 ℚ) :
    univariateRingEquiv (p * q) = univariateRingEquiv p * univariateRingEquiv q := by
  exact (univariateRingEquiv (R := ℚ)).map_mul p q

example (p : CMvPolynomial 1 ℚ) (n : ℕ) :
    CPolynomial.coeff (toUnivariate p) n =
      coeff (univariateMonomial n) p := by
  simpa using coeff_to_univariate p n

example (p : CPolynomial ℚ) (n : ℕ) :
    coeff (univariateMonomial n) (ofUnivariate p) =
      CPolynomial.coeff p n := by
  simpa using coeff_of_univariate p n

example :
    coeff (univariateMonomial 1) (ofUnivariate (CPolynomial.X (R := ℚ))) = 1 := by
  rw [coeff_of_univariate]
  simp [CPolynomial.coeff, CPolynomial.X, CPolynomial.Raw.X, CPolynomial.Raw.coeff]

example :
    coeff (univariateMonomial 0) (ofUnivariate (CPolynomial.X (R := ℚ))) = 0 := by
  rw [coeff_of_univariate]
  simp [CPolynomial.coeff, CPolynomial.X, CPolynomial.Raw.X, CPolynomial.Raw.coeff]

example (c : ℚ) :
    coeff (univariateMonomial 0) (ofUnivariate (CPolynomial.C c)) = c := by
  rw [coeff_of_univariate, CPolynomial.coeff_C]
  simp

example :
    univariateRingEquiv (R := ℚ) =
      (CPoly.CMvPolynomial.finSuccEquiv (n := 0) (R := ℚ)).trans
        ((Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := ℚ))).trans
          (CPolynomial.ringEquiv (R := ℚ)).symm) := by
  simpa using univariate_ring_equiv_eq_fin_succ_composite (R := ℚ)

example (p : CMvPolynomial 1 ℚ) :
    univariateRingEquiv p =
      ((CPoly.CMvPolynomial.finSuccEquiv (n := 0) (R := ℚ)).trans
        ((Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := ℚ))).trans
          (CPolynomial.ringEquiv (R := ℚ)).symm)) p := by
  simpa using congrArg (fun e : CMvPolynomial 1 ℚ ≃+* CPolynomial ℚ => e p)
    (univariate_ring_equiv_eq_fin_succ_composite (R := ℚ))

end CMvPolynomial

end CPoly
