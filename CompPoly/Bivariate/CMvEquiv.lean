/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Bivariate.ToPoly
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv.Instances
import CompPoly.Multivariate.FinSuccEquiv

open CompPoly CPoly CBivariate

variable {R : Type*}
variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]

namespace CMvPolynomial

@[simp]
lemma isEmptyRingEquiv_symm_apply (r : R) :
  CMvPolynomial.isEmptyRingEquiv.symm r = CMvPolynomial.C r := by
    unfold CMvPolynomial.isEmptyRingEquiv
    exact CPoly.polyRingEquiv.symm_apply_eq.mpr (CMvPolynomial.fromCMvPolynomial_C r).symm

/- theorem CBivariate_eq_CMvPolynomial {R : Type*}  [CommSemiring R] [BEq R] [LawfulBEq R] : CBivariate R ≃+* CMvPolynomial 2 R := by sorry -/
noncomputable def bivariateEquiv : CBivariate R ≃+* CMvPolynomial 2 R :=
  let step1 := CBivariate.ringEquiv
  let step2 := Polynomial.mapEquiv (Polynomial.mapEquiv CMvPolynomial.isEmptyRingEquiv.symm)
  let step3 := Polynomial.mapEquiv (CMvPolynomial.finSuccEquiv (n:=0) (R:=R)).symm
  let step4 := (CMvPolynomial.finSuccEquiv (n:=1) (R:=R)).symm
  step1.trans <| step2.trans <| step3.trans step4

lemma bivariateEquiv_add (p q : CBivariate R) :
  bivariateEquiv (p + q) = bivariateEquiv p + bivariateEquiv q :=
    bivariateEquiv.map_add p q

lemma bivariateEquiv_mul (p q : CBivariate R) :
  bivariateEquiv (p * q) = bivariateEquiv p *  bivariateEquiv q :=
    bivariateEquiv.map_mul p q

lemma bivariateEquiv_zero : bivariateEquiv (0 : CBivariate R) = 0 :=
  map_zero bivariateEquiv

lemma bivariateEquiv_CC (r : R) : bivariateEquiv (CBivariate.CC r) = CMvPolynomial.C r := by
  unfold CC
