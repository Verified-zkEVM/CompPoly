/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Multivariate.CMvPolynomial

open CompPoly CPoly

variable R

#check CPolynomial
#print CPolynomial

/- theorem CBivariate_eq_CMvPolynomial {R : Type*}  [CommSemiring R] [BEq R] [LawfulBEq R] : CBivariate R ≃+* CMvPolynomial 2 R := by sorry -/
noncomputable def bivariateEquiv {R : Type*} [Semiring R] : CBivariate R ≃+* CMvPolynomial 2 R := sorry
