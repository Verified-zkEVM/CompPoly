/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Zitek-Estrada
-/

import CompPoly.Multivariate.FinSuccEquiv
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Univariate.ToPoly.Impl
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Equivalence between `CPolynomial` and `CMvPolynomial 1`

This file establishes the ring equivalence
`CPolynomial.cmvEquiv : CPolynomial R ≃+* CMvPolynomial 1 R`.

The equivalence chain is:
  `CPolynomial R ≃ R[X] ≃ (CMvPolynomial 0 R)[X] ≃ CMvPolynomial 1 R`

The bridge lemmas expose how the inverse equivalence interacts with evaluation
and degree, so one-variable results proved for `CPolynomial` can be transported
to callers that still use `CMvPolynomial 1`.
-/

namespace CompPoly.CPolynomial

open CPoly
open CMvPolynomial

variable {R : Type*}

/-- Ring equivalence between computable univariate polynomials and
single-variable computable multivariate polynomials. -/
noncomputable def cmvEquiv
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    CPolynomial R ≃+* CMvPolynomial 1 R :=
  (ringEquiv (R := R)).trans <|
    (Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R))).symm.trans
      (CMvPolynomial.finSuccEquiv (n := 0) (R := R)).symm

/-- Bridge a single-variable `MvPolynomial (Fin 1) R` to `Polynomial R` by
sending the unique variable to `Polynomial.X`. -/
private noncomputable def mvToUnivariate [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) : Polynomial R :=
  MvPolynomial.eval₂ Polynomial.C (fun _ ↦ Polynomial.X) p

/-- The `MvPolynomial (Fin 1)` to `Polynomial` bridge factors through
`finSuccEquiv` and `isEmptyRingEquiv`. -/
private lemma mvToUnivariate_eq_map_finSuccEquiv [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) :
    mvToUnivariate p =
      Polynomial.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
        (MvPolynomial.finSuccEquiv R 0 p) := by
  have :
      (MvPolynomial.eval₂Hom Polynomial.C (fun _ : Fin 1 ↦ Polynomial.X) :
          MvPolynomial (Fin 1) R →+* Polynomial R)
        = (Polynomial.mapRingHom
            (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom).comp
            (MvPolynomial.finSuccEquiv R 0).toRingHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      simp [MvPolynomial.finSuccEquiv_apply, Polynomial.map_C,
            MvPolynomial.isEmptyRingEquiv]
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [MvPolynomial.finSuccEquiv_X_zero]
  exact congrArg (fun f : MvPolynomial (Fin 1) R →+* Polynomial R ↦ f p) this

private lemma mvToUnivariate_sub [CommRing R]
    (p q : MvPolynomial (Fin 1) R) :
    mvToUnivariate (p - q) = mvToUnivariate p - mvToUnivariate q := by
  change
    (MvPolynomial.eval₂Hom Polynomial.C (fun _ : Fin 1 ↦ Polynomial.X)) (p - q) =
      (MvPolynomial.eval₂Hom Polynomial.C (fun _ : Fin 1 ↦ Polynomial.X)) p -
        (MvPolynomial.eval₂Hom Polynomial.C (fun _ : Fin 1 ↦ Polynomial.X)) q
  exact RingHom.map_sub _ _ _

/-- The `MvPolynomial (Fin 1)` to `Polynomial` bridge preserves univariate
degree. -/
private lemma natDegree_mvToUnivariate [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) :
    (mvToUnivariate p).natDegree = p.degreeOf 0 := by
  rw [mvToUnivariate_eq_map_finSuccEquiv]
  have hmap : (Polynomial.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
        (MvPolynomial.finSuccEquiv R 0 p)).natDegree =
      (MvPolynomial.finSuccEquiv R 0 p).natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective _
  rw [hmap, MvPolynomial.natDegree_finSuccEquiv]

/-- Evaluating the `MvPolynomial (Fin 1)` to `Polynomial` bridge at `x` agrees
with evaluating the original multivariate polynomial at the constant assignment
`fun _ ↦ x`. -/
private lemma eval_mvToUnivariate [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) (x : R) :
    (mvToUnivariate p).eval x = MvPolynomial.eval (fun _ ↦ x) p := by
  show Polynomial.eval x
      (MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 ↦ Polynomial.X) p) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext r; simp
  · funext _; simp

private theorem cmvEquiv_symm_toPoly
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CMvPolynomial 1 R) :
    ((cmvEquiv (R := R)).symm p).toPoly =
      mvToUnivariate (fromCMvPolynomial p) := by
  rw [mvToUnivariate_eq_map_finSuccEquiv]
  change ((ringEquiv (R := R)).symm
      ((Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R)))
        (CMvPolynomial.finSuccEquiv (n := 0) (R := R) p))).toPoly =
    Polynomial.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
      (MvPolynomial.finSuccEquiv R 0 (fromCMvPolynomial p))
  rw [show ((ringEquiv (R := R)).symm
      ((Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R)))
        (CMvPolynomial.finSuccEquiv (n := 0) (R := R) p))).toPoly =
      (Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R)))
        (CMvPolynomial.finSuccEquiv (n := 0) (R := R) p) from
    (ringEquiv (R := R)).right_inv _]
  unfold CMvPolynomial.finSuccEquiv CPoly.polynomialCMvPolyEquiv
    CMvPolynomial.isEmptyRingEquiv
  ext n
  simp [RingEquiv.trans_apply, Polynomial.coeff_map, CPoly.polyRingEquiv, CPoly.polyEquiv]

/-- Evaluation after converting a single-variable `CMvPolynomial` back to
`CPolynomial` agrees with multivariate evaluation at the constant assignment. -/
theorem eval_cmvEquiv_symm
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CMvPolynomial 1 R) (x : R) :
    ((cmvEquiv (R := R)).symm p).eval x = p.eval (fun _ ↦ x) := by
  rw [eval_toPoly, cmvEquiv_symm_toPoly, eval_mvToUnivariate, ← eval_equiv]

/-- Degree transport for differences through the inverse of `cmvEquiv`. -/
theorem natDegree_cmvEquiv_symm_sub
    [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CMvPolynomial 1 R) :
    (((cmvEquiv (R := R)).symm p - (cmvEquiv (R := R)).symm q).natDegree) =
      (fromCMvPolynomial p - fromCMvPolynomial q).degreeOf 0 := by
  rw [natDegree_toPoly, toPoly_sub, cmvEquiv_symm_toPoly, cmvEquiv_symm_toPoly,
    ← mvToUnivariate_sub, natDegree_mvToUnivariate]

end CompPoly.CPolynomial
