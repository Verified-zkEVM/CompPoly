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
import CompPoly.Multivariate.Rename

open CompPoly CPoly CBivariate

variable {R : Type*}
variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]

namespace CMvPolynomial

@[simp]
lemma isEmptyRingEquiv_symm_apply
    {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] (r : R) :
    CMvPolynomial.isEmptyRingEquiv.symm r = CMvPolynomial.C r := by
  unfold CMvPolynomial.isEmptyRingEquiv
  rw [RingEquiv.symm_trans_apply, polyRingEquiv.symm_apply_eq]
  exact (CMvPolynomial.fromCMvPolynomial_C r).symm

@[simp]
lemma finSuccEquiv_symm_C
    {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    {n : ℕ} (x : CMvPolynomial n R) :
    CMvPolynomial.finSuccEquiv.symm (Polynomial.C x) =
      CMvPolynomial.rename Fin.succ x := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_rename]
  unfold finSuccEquiv
  simp [RingEquiv.symm_trans_apply, CPoly.polynomialCMvPolyEquiv]
  show polyRingEquiv (polyRingEquiv.symm
      (((MvPolynomial.finSuccEquiv R n)).symm
        (Polynomial.C (polyRingEquiv x)))) =
    (MvPolynomial.rename Fin.succ) (fromCMvPolynomial x)
  rw [polyRingEquiv.apply_symm_apply]
  change (MvPolynomial.finSuccEquiv R n).symm
      (Polynomial.C (fromCMvPolynomial x)) =
    (MvPolynomial.rename Fin.succ) (fromCMvPolynomial x)
  generalize fromCMvPolynomial x = p
  apply (MvPolynomial.finSuccEquiv R n).injective
  rw [AlgEquiv.apply_symm_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  | add p q hp hq => simp only [_root_.map_add, hp, hq]
  | mul_X p i hp =>
    simp only [_root_.map_mul, MvPolynomial.rename_X, hp,
               MvPolynomial.finSuccEquiv_X_succ]

end CMvPolynomial

noncomputable def bivariateEquiv :
    CBivariate R ≃+* CMvPolynomial 2 R :=
  let step1 := CBivariate.ringEquiv
  let step2 := Polynomial.mapEquiv
    (Polynomial.mapEquiv CMvPolynomial.isEmptyRingEquiv.symm)
  let step3 := Polynomial.mapEquiv
    (CMvPolynomial.finSuccEquiv (n := 0) (R := R)).symm
  let step4 :=
    (CMvPolynomial.finSuccEquiv (n := 1) (R := R)).symm
  step1.trans <| step2.trans <| step3.trans step4

lemma bivariateEquiv_add (p q : CBivariate R) :
    bivariateEquiv (p + q) =
      bivariateEquiv p + bivariateEquiv q :=
  bivariateEquiv.map_add p q

lemma bivariateEquiv_mul (p q : CBivariate R) :
    bivariateEquiv (p * q) =
      bivariateEquiv p * bivariateEquiv q :=
  bivariateEquiv.map_mul p q

lemma bivariateEquiv_zero :
    bivariateEquiv (0 : CBivariate R) = 0 :=
  map_zero bivariateEquiv

lemma bivariateEquiv_CC (r : R) :
    bivariateEquiv (CBivariate.CC r) = CMvPolynomial.C r := by
  unfold bivariateEquiv
  simp [ringEquiv, Polynomial.map_C, CC_toPoly,
        CMvPolynomial.isEmptyRingEquiv_symm_apply,
        CMvPolynomial.finSuccEquiv_symm_C]
