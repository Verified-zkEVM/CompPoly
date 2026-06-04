/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Basis

/-!
# Lee-O'Sullivan Divisibility Helpers

Hasse-derivative and vanishing-polynomial divisibility bridges used in completeness.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
private theorem lee_hasseDeriv_mul_C_pow
    (P : Polynomial F) (c : F) (n a : Nat) :
    Polynomial.hasseDeriv a (P * Polynomial.C c ^ n) =
      Polynomial.hasseDeriv a P * Polynomial.C c ^ n := by
  rw [show Polynomial.C c ^ n = Polynomial.C (c ^ n) by rw [Polynomial.C_pow]]
  ext d
  rw [Polynomial.hasseDeriv_coeff]
  rw [Polynomial.coeff_mul_C]
  rw [Polynomial.coeff_mul_C]
  rw [Polynomial.hasseDeriv_coeff]
  ring

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
private theorem lee_hasseDeriv_eval_C_eq_eval_coeffwise_hasseDeriv
    (P : Polynomial (Polynomial F)) (y : F) (a : Nat) :
    Polynomial.hasseDeriv a (Polynomial.eval (Polynomial.C y) P) =
      Polynomial.eval (Polynomial.C y)
        (P.sum fun j coeff ↦ Polynomial.monomial j (Polynomial.hasseDeriv a coeff)) := by
  rw [Polynomial.eval_eq_sum]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.sum_add_index]
      rw [map_add]
      rw [hP, hQ]
      rw [Polynomial.sum_add_index]
      · simp
      · intro i
        simp
      · intro i p q
        simp
      · intro i
        simp
      · intro i p q
        simp [add_mul]
  | monomial n coeff =>
      simp [Polynomial.sum_monomial_index, lee_hasseDeriv_mul_C_pow]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
private theorem lee_coeff_coeffwise_hasseDeriv_sum
    (P : Polynomial (Polynomial F)) (a j : Nat) :
    ((P.sum fun k coeff ↦ Polynomial.monomial k (Polynomial.hasseDeriv a coeff)).coeff j) =
      Polynomial.hasseDeriv a (P.coeff j) := by
  rw [Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  by_cases hj : j ∈ P.support
  · rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro k _hk hkj
      rw [Polynomial.coeff_monomial, if_neg hkj]
    · intro hjnot
      contradiction
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj]
      simp
    · intro k hk
      have hkj : k ≠ j := by
        intro h
        exact hj (h ▸ hk)
      rw [Polynomial.coeff_monomial, if_neg hkj]

private theorem lee_toPoly_hasseDerivative_eq_coeffwise_hasseDeriv_hasseDeriv
    (Q : CBivariate F) (a b : Nat) :
    (CBivariate.hasseDerivative a b Q).toPoly =
      (Polynomial.hasseDeriv b Q.toPoly).sum fun j coeff ↦
        Polynomial.monomial j (Polynomial.hasseDeriv a coeff) := by
  ext j n
  rw [lee_coeff_coeffwise_hasseDeriv_sum]
  simp [Polynomial.hasseDeriv_coeff, CBivariate.hasseDerivative_coeff,
    CBivariate.coeff_toPoly]
  ring

private theorem lee_eval_hasseDeriv_eval_hasseDeriv_toPoly
    (Q : CBivariate F) (x y : F) (a b : Nat) :
    Polynomial.eval x (Polynomial.hasseDeriv a
        (Polynomial.eval (Polynomial.C y) (Polynomial.hasseDeriv b Q.toPoly))) =
      CBivariate.hasseDerivativeEval a b x y Q := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [CBivariate.evalEval_toPoly]
  rw [Polynomial.evalEval]
  rw [lee_hasseDeriv_eval_C_eq_eval_coeffwise_hasseDeriv]
  rw [← lee_toPoly_hasseDerivative_eq_coeffwise_hasseDeriv_hasseDeriv]

private theorem coeffY_hasseDeriv_eval_eq_hasseDerivativeEval_of_forall_gt
    {P : CBivariate F} {n a : Nat} {x y : F}
    (hY : ∀ j, n < j → P.val.coeff j = 0) :
    Polynomial.eval x (Polynomial.hasseDeriv a (CPolynomial.toPoly (P.val.coeff n))) =
      CBivariate.hasseDerivativeEval a n x y P := by
  have houter :
      Polynomial.hasseDeriv n (CBivariate.toPoly P) =
        Polynomial.C (CPolynomial.toPoly (P.val.coeff n)) := by
    ext j i
    by_cases hj : j = 0
    · subst j
      rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_C, if_pos rfl]
      simp [CBivariate.coeff_toPoly_Y]
    · rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_C, if_neg hj]
      have hgt : n < j + n := by omega
      rw [CBivariate.coeff_toPoly_Y, hY (j + n) hgt, CPolynomial.toPoly_zero]
      simp
  rw [← lee_eval_hasseDeriv_eval_hasseDeriv_toPoly P x y a n]
  rw [houter, Polynomial.eval_C]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
private theorem X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero
    {A : Polynomial F} {x : F} {k : Nat}
    (hzero : ∀ a, a < k → Polynomial.eval x (Polynomial.hasseDeriv a A) = 0) :
    (Polynomial.X - Polynomial.C x) ^ k ∣ A := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [← Polynomial.taylor_apply]
  rw [Polynomial.taylor_coeff]
  exact hzero d hd

omit [BEq F] [LawfulBEq F] [Nontrivial F] in
private theorem multiset_prod_X_sub_C_pow_dvd_of_nodup
    {A : Polynomial F} {xs : List F} {k : Nat}
    (hA : A ≠ 0) (hnodup : xs.Nodup)
    (hroot : ∀ x, x ∈ xs → (Polynomial.X - Polynomial.C x) ^ k ∣ A) :
    (((xs : Multiset F).map fun x ↦
      (Polynomial.X - Polynomial.C x : Polynomial F)).prod) ^ k ∣ A := by
  let ms : Multiset F := xs
  have hmsNodup : ms.Nodup := by
    simpa [ms] using hnodup
  have hle : k • ms ≤ A.roots := by
    rw [Multiset.le_iff_count]
    intro x
    rw [Multiset.count_nsmul]
    by_cases hx : x ∈ ms
    · have hxCount : Multiset.count x ms = 1 :=
        Multiset.count_eq_one_of_mem hmsNodup hx
      rw [hxCount, mul_one]
      have hdiv : (Polynomial.X - Polynomial.C x) ^ k ∣ A := by
        exact hroot x (by simpa [ms] using hx)
      rw [Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hA).2 hdiv
    · rw [Multiset.count_eq_zero_of_notMem hx, mul_zero]
      exact Nat.zero_le _
  have hprod :
      (((k • ms).map fun x ↦
        (Polynomial.X - Polynomial.C x : Polynomial F)).prod) ∣ A :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hA (k • ms)).2 hle
  rw [Multiset.map_nsmul, Multiset.prod_nsmul] at hprod
  simpa [ms] using hprod

omit [Nontrivial F] [DecidableEq F] in
private theorem lee_linearFactor_toPoly (x : F) :
    (CPolynomial.linearFactor x).toPoly =
      (Polynomial.X - Polynomial.C x : Polynomial F) := by
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  simp [sub_eq_add_neg, add_comm]

omit [Nontrivial F] [DecidableEq F] in
private theorem lee_vanishingPolynomialArray_toPoly_list
    (xs : List F) (acc : CPolynomial F) :
    (xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc).toPoly =
      acc.toPoly * (xs.map fun x ↦
        (Polynomial.X - Polynomial.C x : Polynomial F)).prod := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, CPolynomial.toPoly_mul, lee_linearFactor_toPoly]
      simp only [List.map_cons, List.prod_cons]
      ring

omit [DecidableEq F] in
private theorem lee_vanishingPolynomialArray_toPoly (xs : Array F) :
    (CPolynomial.vanishingPolynomialArray xs).toPoly =
      (((xs.toList : Multiset F).map fun x ↦
        (Polynomial.X - Polynomial.C x : Polynomial F))).prod := by
  rw [CPolynomial.vanishingPolynomialArray]
  have hlist := lee_vanishingPolynomialArray_toPoly_list xs.toList (1 : CPolynomial F)
  simpa [CPolynomial.toPoly_one, Multiset.map_coe, Multiset.prod_coe] using hlist

theorem coeffY_dvd_vanishingPolynomial_pow_of_multiplicity
    (V : CPolynomial.VanishingPolynomialContext F)
    {points : Array (F × F)} {P : CBivariate F} {m n : Nat}
    (hdistinct : DistinctXCoordinates points)
    (hn : n < m)
    (hY : ∀ j, n < j → P.val.coeff j = 0)
    (hmult : CBivariate.SatisfiesMultiplicityConstraints P points m) :
    ∃ W : CPolynomial F,
      P.val.coeff n =
        W * (V.vanishingPolynomial (points.map fun point ↦ point.1)) ^ (m - n) := by
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let k := m - n
  by_cases hcoeff : P.val.coeff n = 0
  · refine ⟨0, ?_⟩
    simp [hcoeff]
  · have hAne : (P.val.coeff n).toPoly ≠ 0 := by
      exact (CPolynomial.toPoly_eq_zero_iff (P.val.coeff n)).not.mpr hcoeff
    have hxsNodup : (points.map fun point ↦ point.1).toList.Nodup := by
      simpa [DistinctXCoordinates, Array.toList_map] using hdistinct
    have hroot :
        ∀ x, x ∈ (points.map fun point ↦ point.1).toList →
          (Polynomial.X - Polynomial.C x) ^ k ∣ (P.val.coeff n).toPoly := by
      intro x hx
      rw [Array.toList_map] at hx
      rcases List.mem_map.mp hx with ⟨point, hpoint, rfl⟩
      apply X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero
      intro a ha
      rw [coeffY_hasseDeriv_eval_eq_hasseDerivativeEval_of_forall_gt hY]
      exact hmult point hpoint a n (by
        have hk : k = m - n := rfl
        omega)
    have hprodDvd :
        ((((points.map fun point ↦ point.1).toList : Multiset F).map fun x ↦
          (Polynomial.X - Polynomial.C x : Polynomial F)).prod) ^ k ∣
            (P.val.coeff n).toPoly :=
      multiset_prod_X_sub_C_pow_dvd_of_nodup hAne hxsNodup hroot
    have hGtoPoly : G.toPoly =
        ((((points.map fun point ↦ point.1).toList : Multiset F).map fun x ↦
          (Polynomial.X - Polynomial.C x : Polynomial F))).prod := by
      change (V.vanishingPolynomial (points.map fun point ↦ point.1)).toPoly = _
      rw [V.correct]
      exact lee_vanishingPolynomialArray_toPoly (points.map fun point ↦ point.1)
    have hGpowDvd : G.toPoly ^ k ∣ (P.val.coeff n).toPoly := by
      rw [hGtoPoly]
      exact hprodDvd
    rcases hGpowDvd with ⟨Wpoly, hWpoly⟩
    let W : CPolynomial F := ⟨Wpoly.toImpl, CPolynomial.Raw.isCanonical_toImpl Wpoly⟩
    refine ⟨W, ?_⟩
    apply cpoly_eq_of_toPoly_eq
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow]
    have hWto : W.toPoly = Wpoly := by
      change Wpoly.toImpl.toPoly = Wpoly
      exact CPolynomial.Raw.toPoly_toImpl
    rw [hWto]
    rw [hWpoly]
    ring

end LeeOSullivan

end GuruswamiSudan

end CompPoly
