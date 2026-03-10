/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Support.LinearIndependentFin2

open Polynomial
open AdjoinRoot
open Module

section DefiningPoly

noncomputable def definingPoly {F : Type*} [instField : Field F] (s : F) :=
  X ^ 2 + C s * X + 1

lemma degree_s_smul_X {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (C s * (X : (F)[X])).degree = 1 := by
  apply degree_C_mul_X (a:=s)
  exact NeZero.ne s

lemma degree_s_smul_X_add_1 {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (C s * (X : (F)[X]) + 1).degree = 1 := by
  rw [degree_add_eq_left_of_degree_lt]
  · exact degree_s_smul_X s
  · rw [degree_one]; rw [degree_s_smul_X]; norm_num

lemma definingPoly_is_monic {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (definingPoly s).Monic := by
  rw [definingPoly]
  -- Goal : ⊢ (X ^ 2 + (t1 * X + 1)).Monic
  have leadingCoeffIs1 : (definingPoly s).leadingCoeff = 1 := by
    calc
      (definingPoly s).leadingCoeff
        = (C s * (X : (F)[X]) + 1 + X^2).leadingCoeff := by
        rw [definingPoly, _root_.add_assoc, _root_.add_comm]
      _ = (X^2).leadingCoeff := by
        rw [leadingCoeff_add_of_degree_lt]
        rw [degree_X_pow, degree_s_smul_X_add_1]
        norm_num
      _ = 1 := by
        rw [monic_X_pow]
  exact leadingCoeffIs1

lemma degree_definingPoly {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (definingPoly s).degree = 2 := by
  rw [definingPoly, _root_.add_assoc, _root_.add_comm]
  -- ⊢ (s • X + 1 + X ^ 2).degree = 2
  rw [degree_add_eq_right_of_degree_lt]
  · rw [degree_X_pow]; rfl
  · have h_deg_left := degree_s_smul_X_add_1 s
    rw [degree_X_pow];
    rw [h_deg_left]
    norm_num

lemma natDegree_definingPoly {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (definingPoly s).natDegree = 2 := natDegree_eq_of_degree_eq_some (h:=degree_definingPoly s)

lemma definingPoly_ne_zero {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (definingPoly s) ≠ 0 := by
  refine Monic.ne_zero_of_ne ?_ ?_
  · exact zero_ne_one' (F)
  · exact definingPoly_is_monic s

lemma definingPoly_is_not_unit {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    ¬IsUnit (definingPoly s) := by
  by_contra h_unit
  have deg_poly_is_0 := degree_eq_zero_of_isUnit h_unit
  have deg_poly_is_2 : (definingPoly s).degree = 2 := by
    exact degree_definingPoly s
  have zero_is_two : (0 : WithBot ℕ) = 2 := by
    rw [deg_poly_is_0] at deg_poly_is_2
    exact deg_poly_is_2

  contradiction

lemma definingPoly_coeffOf0 {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (definingPoly s).coeff 0 = 1 := by
  simp only [definingPoly, coeff_add, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte,
      mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, add_zero, coeff_one_zero, zero_add]

lemma definingPoly_coeffOf1 {F : Type*} [Field F] [Fintype F] (s : F) [NeZero s] :
    (definingPoly s).coeff 1 = s := by
  simp only [definingPoly, coeff_add, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, coeff_mul_X,
    coeff_C_zero, zero_add, coeff_one, one_ne_zero, add_zero]

end DefiningPoly
