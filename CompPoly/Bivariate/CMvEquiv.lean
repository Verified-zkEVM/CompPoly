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

/-!
# Equivalence between `CBivariate` and `CMvPolynomial 2`

This file establishes the ring equivalence
`bivariateEquiv : CBivariate R ≃+* CMvPolynomial 2 R`
by composing `CBivariate.ringEquiv` with `CMvPolynomial.finSuccEquiv`
and `CMvPolynomial.isEmptyRingEquiv`.

The equivalence chain is:
  `CBivariate R ≃ R[X][Y] ≃ (CMvPolynomial 0 R)[X][Y]
    ≃ (CMvPolynomial 1 R)[Y] ≃ CMvPolynomial 2 R`

## Main definitions

* `bivariateEquiv` — ring equivalence `CBivariate R ≃+* CMvPolynomial 2 R`

## Bridge lemmas

* `bivariateEquiv_CC` — `bivariateEquiv (CC r) = C r`
* `bivariateEquiv_X` — `bivariateEquiv X = CMvPolynomial.X 1`
* `bivariateEquiv_Y` — `bivariateEquiv Y = CMvPolynomial.X 0`
* `bivariateEquiv_symm_C` — `bivariateEquiv.symm (C r) = CC r`
* `bivariateEquiv_symm_X0` — `bivariateEquiv.symm (X 0) = Y`
* `bivariateEquiv_symm_X1` — `bivariateEquiv.symm (X 1) = X`

## Helper lemmas (for `CMvPolynomial.finSuccEquiv`)

* `CMvPolynomial.isEmptyRingEquiv_symm_apply` —
  `isEmptyRingEquiv.symm r = C r`
* `CMvPolynomial.finSuccEquiv_symm_C` —
  `finSuccEquiv.symm (Polynomial.C x) = rename Fin.succ x`
* `CMvPolynomial.finSuccEquiv_symm_X` —
  `finSuccEquiv.symm Polynomial.X = CMvPolynomial.X 0`
-/

namespace CMvPolynomial

open CPoly

/-- `isEmptyRingEquiv.symm` maps scalars to constants. -/
@[simp]
lemma isEmptyRingEquiv_symm_apply
    {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] (r : R) :
    CMvPolynomial.isEmptyRingEquiv.symm r = CMvPolynomial.C r := by
  unfold CMvPolynomial.isEmptyRingEquiv
  rw [RingEquiv.symm_trans_apply, polyRingEquiv.symm_apply_eq]
  exact (CMvPolynomial.fromCMvPolynomial_C r).symm

/-- `finSuccEquiv.symm` maps `Polynomial.C` to `rename Fin.succ`. -/
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

/-- `finSuccEquiv.symm` maps `Polynomial.X` to the zeroth variable. -/
@[simp]
lemma finSuccEquiv_symm_X
    {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    {n : ℕ} :
    CMvPolynomial.finSuccEquiv.symm
      (Polynomial.X : Polynomial (CMvPolynomial n R)) =
      CMvPolynomial.X 0 := by
  rw [finSuccEquiv, polyRingEquiv.symm_trans_apply,
    polyRingEquiv.symm_apply_eq, RingEquiv.symm_trans_apply]
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.symm_symm]
  rw [polynomialCMvPolyEquiv, Polynomial.mapEquiv_apply,
    Polynomial.map_X]
  have h : (MvPolynomial.finSuccEquiv R n).symm
      Polynomial.X = MvPolynomial.X 0 := by
    apply (MvPolynomial.finSuccEquiv R n).injective
    simp [MvPolynomial.finSuccEquiv_X_zero]
  change (MvPolynomial.finSuccEquiv R n).symm
      Polynomial.X = polyRingEquiv (CMvPolynomial.X 0)
  rw [h]
  exact (fromCMvPolynomial_X (R := R) 0).symm

end CMvPolynomial

namespace CompPoly.CBivariate

open CPoly CompPoly.CBivariate

variable {R : Type*}
variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
  [DecidableEq R]

/-- Ring equivalence between `CBivariate R` and `CMvPolynomial 2 R`. -/
noncomputable def bivariateEquiv :
    CBivariate R ≃+* CMvPolynomial 2 R :=
  let toPolyEquiv := CBivariate.ringEquiv
  let embedCoeffs := Polynomial.mapEquiv
    (Polynomial.mapEquiv CMvPolynomial.isEmptyRingEquiv.symm)
  let foldInner := Polynomial.mapEquiv
    (CMvPolynomial.finSuccEquiv (n := 0) (R := R)).symm
  let foldOuter :=
    (CMvPolynomial.finSuccEquiv (n := 1) (R := R)).symm
  toPolyEquiv.trans <|
    embedCoeffs.trans <| foldInner.trans foldOuter

/-- `bivariateEquiv` preserves addition. -/
lemma bivariateEquiv_add (p q : CBivariate R) :
    bivariateEquiv (p + q) =
      bivariateEquiv p + bivariateEquiv q :=
  bivariateEquiv.map_add p q

/-- `bivariateEquiv` preserves multiplication. -/
lemma bivariateEquiv_mul (p q : CBivariate R) :
    bivariateEquiv (p * q) =
      bivariateEquiv p * bivariateEquiv q :=
  bivariateEquiv.map_mul p q

/-- `bivariateEquiv` maps zero to zero. -/
lemma bivariateEquiv_zero :
    bivariateEquiv (0 : CBivariate R) = 0 :=
  map_zero bivariateEquiv

/-- `bivariateEquiv` maps bivariate constants to multivariate constants. -/
lemma bivariateEquiv_CC (r : R) :
    bivariateEquiv (CBivariate.CC r) = CMvPolynomial.C r := by
  unfold bivariateEquiv
  simp [ringEquiv, Polynomial.map_C, CC_toPoly,
        CMvPolynomial.isEmptyRingEquiv_symm_apply,
        CMvPolynomial.finSuccEquiv_symm_C]

/-- `bivariateEquiv` maps `CBivariate.X` to the second variable. -/
lemma bivariateEquiv_X :
    bivariateEquiv (CBivariate.X : CBivariate R) =
      CMvPolynomial.X 1 := by
  simp [bivariateEquiv, ringEquiv, X_toPoly]

/-- `bivariateEquiv` maps `CBivariate.Y` to the first variable. -/
lemma bivariateEquiv_Y :
    bivariateEquiv (CBivariate.Y : CBivariate R) =
      CMvPolynomial.X 0 := by
  simp [bivariateEquiv, ringEquiv, Y_toPoly]

/-- `bivariateEquiv.symm` maps multivariate constants to bivariate constants. -/
lemma bivariateEquiv_symm_C (r : R) :
    bivariateEquiv.symm (CMvPolynomial.C r) =
      CBivariate.CC r := by
  apply bivariateEquiv.injective
  simp [bivariateEquiv_CC]

/-- `bivariateEquiv.symm` maps the first variable to `CBivariate.Y`. -/
lemma bivariateEquiv_symm_X0 :
    bivariateEquiv.symm (CMvPolynomial.X 0 : CMvPolynomial 2 R) =
      CBivariate.Y := by
  apply bivariateEquiv.injective
  simp [bivariateEquiv_Y]

/-- `bivariateEquiv.symm` maps the second variable to `CBivariate.X`. -/
lemma bivariateEquiv_symm_X1 :
    bivariateEquiv.symm (CMvPolynomial.X 1 : CMvPolynomial 2 R) =
      CBivariate.X := by
  apply bivariateEquiv.injective
  simp [bivariateEquiv_X]

end CompPoly.CBivariate
