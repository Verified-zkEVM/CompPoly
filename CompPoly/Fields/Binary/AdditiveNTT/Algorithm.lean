/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.Intermediate

/-!
# Additive NTT Algorithm

Core Additive NTT data flow: evaluation points, twiddle factors, stage/update
definitions, coefficient tiling, and the stage invariant.
-/

open Polynomial AdditiveNTT Module
namespace AdditiveNTT

universe u

variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ R_rate : ℕ} (h_ℓ_add_R_rate : ℓ + R_rate < r)

section Algorithm

noncomputable def evaluationPointω (i : Fin (ℓ + 1))
    (x : Fin (2 ^ (ℓ + R_rate - i))) : L :=
  ∑ (⟨k, hk⟩ : Fin (ℓ + R_rate - i)),
    if Nat.getBit k x.val = 1 then
      (normalizedW 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + k, by omega⟩)
    else
      0

noncomputable def twiddleFactor (i : Fin ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  ∑ (⟨k, hk⟩ : Fin (ℓ + R_rate - i - 1)),
    if Nat.getBit k u.val = 1 then
      (normalizedW 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + 1 + k, by omega⟩)
    else 0

omit [DecidableEq L] [DecidableEq 𝔽q] [Fintype 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma evaluationPointω_eq_twiddleFactor_of_div_2 (i : Fin ℓ) (x : Fin (2 ^ (ℓ + R_rate - i))) :
    evaluationPointω 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ x =
      twiddleFactor 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨x / 2, by
        have h := div_two_pow_lt_two_pow (x := x) (i := ℓ + R_rate - i - 1) (j := 1) (by
          rw [Nat.sub_add_cancel (by omega)]
          omega)
        simp only [pow_one] at h
        calc _ < 2 ^ (ℓ + R_rate - i - 1) := by omega
          _ = _ := by rfl⟩ +
        (x.val % 2 : ℕ) * eval (β ⟨i, by omega⟩) (normalizedW 𝔽q β ⟨i, by omega⟩) := by
  unfold evaluationPointω twiddleFactor
  simp only
  set f_left := fun x_1 : Fin (ℓ + R_rate - i) =>
    if Nat.getBit x_1 x = 1 then eval (β ⟨i + x_1, by omega⟩) (normalizedW 𝔽q β ⟨i, by omega⟩)
    else 0
  conv_lhs =>
    rw [← Fin.sum_congr' (b := ℓ + R_rate - i) (a := ℓ + R_rate - (i + 1) + 1) (f := f_left) (h := by omega)]
    rw [Fin.sum_univ_succ (n := ℓ + R_rate - (i + 1))]
  unfold f_left
  simp only [Fin.val_cast, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ]
  have h_bit_shift : ∀ x_1 : Fin (ℓ + R_rate - (↑i + 1)),
      Nat.getBit (↑x_1 + 1) ↑x = Nat.getBit ↑x_1 (↑x / 2) := by
    intro x_1
    rw [← Nat.shiftRight_eq_div_pow (m := x) (n := 1)]
    exact Nat.getBit_of_shiftRight (n := x) (p := 1) (k := x_1).symm
  have h_sum_eq : ∀ x_1 : Fin (ℓ + R_rate - (↑i + 1)),
      i.val + (x_1.val + 1) = i.val + 1 + x_1.val := by omega
  conv_lhs =>
    enter [2, 2, x_1]
    rw [h_bit_shift]
    simp only [h_sum_eq x_1]
  set f_right := fun x_1 : Fin (ℓ + R_rate - (↑i + 1)) =>
    if Nat.getBit (↑x_1) (↑x / 2) = 1 then
      eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i, by omega⟩)
    else 0
  rw [← Fin.sum_congr' (b := ℓ + R_rate - (↑i + 1)) (a := ℓ + R_rate - i - 1) (f := f_right) (h := by omega)]
  unfold f_right
  simp only [Fin.cast_eq_self]
  rw [add_comm]
  congr
  have h_i_lt_ℓ_add_R_rate : i < ℓ + R_rate := by omega
  have h_2_le_pow_ℓ_add_R_rate_sub_i : 2 ≤ 2 ^ (ℓ + R_rate - i.val) := by
    have h_2_eq : 2 = 2^1 := by rfl
    conv_lhs => rw [h_2_eq]
    apply Nat.pow_le_pow_right (by omega) (by omega)
  simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]
  by_cases h_lsb_of_x_eq_0 : x.val % 2 = 0
  · simp only [h_lsb_of_x_eq_0, zero_ne_one, ↓reduceIte, Nat.cast_zero, zero_mul]
  · push_neg at h_lsb_of_x_eq_0
    simp only [ne_eq, Nat.mod_two_not_eq_zero] at h_lsb_of_x_eq_0
    simp only [h_lsb_of_x_eq_0, ↓reduceIte, Nat.cast_one, one_mul]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma eval_point_ω_eq_next_twiddleFactor_comp_qmap
    (i : Fin ℓ) (x : Fin (2 ^ (ℓ + R_rate - (i + 1)))) :
    evaluationPointω 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩ x =
      eval (twiddleFactor 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨x.val, by
        calc x.val < 2 ^ (ℓ + R_rate - (i.val + 1)) := by omega
          _ = 2 ^ (ℓ + R_rate - i.val - 1) := by rfl⟩) (qMap 𝔽q β ⟨i, by omega⟩) := by
  simp [evaluationPointω, twiddleFactor]
  set q_eval_is_linear_map := linear_map_of_comp_to_linear_map_of_eval (f := qMap 𝔽q β ⟨i, by omega⟩)
    (h_f_linear := qMap_is_linear_map 𝔽q β (i := ⟨i, by omega⟩))
  let eval_qmap_linear := polyEvalLinearMap (qMap 𝔽q β ⟨i, by omega⟩) q_eval_is_linear_map
  set right_inner_func := fun x_1 : Fin (ℓ + R_rate - i - 1) =>
    if Nat.getBit ↑x_1 ↑x = 1 then eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i, by omega⟩)
    else 0
  have h_rhs :
      eval (∑ x_1 : Fin (ℓ + R_rate - i - 1), right_inner_func x_1) (qMap 𝔽q β ⟨↑i, by omega⟩) =
        ∑ x_1 : Fin (ℓ + R_rate - i - 1), (eval (right_inner_func x_1) (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
    change eval_qmap_linear (∑ x_1, right_inner_func x_1) = _
    rw [map_sum (g := eval_qmap_linear) (f := right_inner_func)
      (s := (Finset.univ : Finset (Fin (ℓ + R_rate - i - 1))))]
    congr
  rw [h_rhs]
  set left_inner_func := fun x_1 : Fin (ℓ + R_rate - (i.val + 1)) =>
    if Nat.getBit ↑x_1 ↑x = 1 then eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i + 1, by omega⟩)
    else 0
  conv_lhs =>
    rw [← Fin.sum_congr' (b := ℓ + R_rate - (i.val + 1))
      (a := ℓ + R_rate - i - 1) (f := left_inner_func) (h := by omega)]
    simp only [Fin.cast_eq_self]
  congr
  funext x1
  have h_normalized_comp_qmap : normalizedW 𝔽q β ⟨i + 1, by omega⟩ =
      (qMap 𝔽q β ⟨i, by omega⟩).comp (normalizedW 𝔽q β ⟨i, by omega⟩) := by
    have res := qMap_comp_normalizedW 𝔽q β
      (i := ⟨i, by omega⟩) (h_i_add_1 := by simp only; omega)
    rw [res]
    congr
    simp only [Nat.add_mod_mod]
    rw [Nat.mod_eq_of_lt]
    omega
  simp only [left_inner_func, right_inner_func]
  by_cases h_bit_of_x_eq_0 : Nat.getBit x1 x = 0
  · simp only [h_bit_of_x_eq_0, zero_ne_one, ↓reduceIte]
    have h_0_is_algebra_map : (0 : L) = (algebraMap 𝔽q L) 0 := by
      simp only [map_zero]
    conv_rhs => rw [h_0_is_algebra_map]
    have h_res := qMap_eval_𝔽q_eq_0 𝔽q β (i := ⟨i, by omega⟩) (c := 0)
    rw [h_res]
  · push_neg at h_bit_of_x_eq_0
    have h_bit_lt_2 := Nat.getBit_lt_2 (k := x1) (n := x)
    have bit_eq_1 : Nat.getBit x1 x = 1 := by
      interval_cases Nat.getBit x1 x
      · contradiction
      · rfl
    simp only [bit_eq_1, ↓reduceIte]
    rw [h_normalized_comp_qmap]
    rw [eval_comp]

def tileCoeffs (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  fun v => a (Fin.mk (v.val % (2^ℓ)) (Nat.mod_lt v.val (pow_pos (zero_lt_two) ℓ)))

noncomputable def NTTStage (i : Fin ℓ) (b : Fin (2 ^ (ℓ + R_rate)) → L) :
    Fin (2^(ℓ + R_rate)) → L :=
  have h_2_pow_i_lt_2_pow_ℓ_add_R_rate : 2^i.val < 2^(ℓ + R_rate) := by
    calc
      2^i.val < 2 ^ (ℓ) := by
        have hr := Nat.pow_lt_pow_right (a := 2) (m := i.val) (n := ℓ) (ha := by omega) (by omega)
        exact hr
      _ ≤ 2 ^ (ℓ + R_rate) := by
        exact Nat.pow_le_pow_right (n := 2) (i := ℓ) (j := ℓ + R_rate) (by omega) (by omega)
  fun (j : Fin (2^(ℓ + R_rate))) =>
    let u_b_v := j.val
    have h_u_b_v : u_b_v = j.val := by rfl
    let v : Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits := i.val) (n := u_b_v)
      simp only [res]⟩
    let u_b := u_b_v / (2^i.val)
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      have res := Nat.div_lt_of_lt_mul (m := u_b_v) (n := 2^i.val) (k := 2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a := 2) (m := i.val) (n := ℓ + R_rate) (by omega)))
      rw [h_u_b]
      exact res
    let u : ℕ := u_b / 2
    let b_bit := u_b % 2
    have h_u : u = u_b / 2 := by rfl
    have h_u_lt_2_pow : u < 2 ^ (ℓ + R_rate - (i + 1)) := by
      have h_u_eq : u = j.val / (2 ^ (i.val + 1)) := by
        rw [h_u, h_u_b, h_u_b_v]
        rw [Nat.div_div_eq_div_mul]
        rfl
      rw [h_u_eq]
      exact div_two_pow_lt_two_pow (x := j.val) (i := ℓ + R_rate - (i.val + 1)) (j := i.val + 1) (by
        rw [Nat.sub_add_cancel (by omega)]
        omega)
    let twiddleFactor : L := twiddleFactor 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨u, by
      simp only
      exact h_u_lt_2_pow⟩
    let x0 := twiddleFactor
    let x1 : L := x0 + 1
    have h_b_bit : b_bit = Nat.getBit i.val j.val := by
      simp only [Nat.getBit, Nat.and_one_is_mod, b_bit, u_b, u_b_v]
      rw [← Nat.shiftRight_eq_div_pow (m := j.val) (n := i.val)]
    if h_b_bit_zero : b_bit = 0 then
      let odd_split_index := u_b_v + 2^i.val
      have h_lt : odd_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq : (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [gt_iff_lt, odd_split_index, u_b_v]
        exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow (n := j.val) (m := ℓ + R_rate)
          (i := i.val) (h_n := by omega) (h_i := by omega) (h_getBit_at_i_eq_zero := by
            rw [h_b_bit_zero] at h_b_bit
            exact h_b_bit.symm)
      b j + x0 * b ⟨odd_split_index, h_lt⟩
    else
      let even_split_index := u_b_v ^^^ 2^i.val
      have h_lt : even_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq : (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [even_split_index, u_b_v]
        apply Nat.xor_lt_two_pow (by omega) (by omega)
      b ⟨even_split_index, h_lt⟩ + x1 * b j

noncomputable def additiveNTT (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b : Fin (2^(ℓ + R_rate)) → L := tileCoeffs a
  Fin.foldl (n := ℓ) (f := fun current_b i =>
    NTTStage 𝔽q β h_ℓ_add_R_rate (i := ⟨ℓ - 1 - i, by omega⟩) current_b) (init := b)

def coeffsBySuffix (a : Fin (2 ^ ℓ) → L) (i : Fin (ℓ + 1)) (v : Fin (2 ^ i.val)) :
    Fin (2 ^ (ℓ - i)) → L :=
  fun ⟨j, hj⟩ => by
    set originalIndex := (j <<< i.val) ||| v
    have h_originalIndex_lt_2_pow_ℓ : originalIndex < 2 ^ ℓ := by
      unfold originalIndex
      have res := Nat.append_lt (y := j) (x := v) (m := ℓ - i.val) (n := i.val) (by omega) (by omega)
      have h_exp_eq : (↑i + (ℓ - ↑i)) = ℓ := by omega
      rw [h_exp_eq] at res
      exact res
    exact a ⟨originalIndex, h_originalIndex_lt_2_pow_ℓ⟩

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [DecidableEq 𝔽q] [Field 𝔽q] [Algebra 𝔽q L] in
lemma base_coeffsBySuffix (a : Fin (2 ^ ℓ) → L) :
    coeffsBySuffix (r := r) (R_rate := R_rate) a 0 0 = a := by
  unfold coeffsBySuffix
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.shiftLeft_zero, Fin.isValue,
    Nat.or_zero, Fin.eta]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem evenRefinement_eq_novel_poly_of_0_leading_suffix (i : Fin ℓ) (v : Fin (2 ^ i.val))
    (original_coeffs : Fin (2 ^ ℓ) → L) :
    have h_v : v.val < 2 ^ (i.val + 1) := by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    evenRefinement 𝔽q β h_ℓ_add_R_rate i (coeffsBySuffix (r := r)
      (R_rate := R_rate) (a := original_coeffs) ⟨i, by omega⟩ v) =
      intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩
        (coeffsBySuffix (r := r) (R_rate := R_rate) original_coeffs ⟨i + 1, by omega⟩ ⟨v, h_v⟩) := by
  simp only [evenRefinement, Fin.eta, intermediateEvaluationPoly]
  set right_inner_func := fun x : Fin (2^(ℓ - (i.val + 1))) =>
    C (coeffsBySuffix (R_rate := R_rate) original_coeffs ⟨i.val + 1, by omega⟩ ⟨v.val, by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)⟩ x) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩ x
  have h_right_sum_eq := Fin.sum_congr' (M := L[X]) (b := 2^(ℓ - (i.val + 1)))
    (a := 2^(ℓ - i - 1)) (f := right_inner_func) (h := by rfl)
  conv_rhs =>
    simp only [Fin.cast_eq_self]
    rw [← h_right_sum_eq]
    simp only [Fin.cast_eq_self]
  congr
  funext x
  simp only [right_inner_func]
  have h_coeffs_eq : coeffsBySuffix (r := r) (R_rate := R_rate)
      original_coeffs (i := ⟨i.val, by omega⟩) v ⟨↑x * 2, by
        have h_x_mul_2_lt := mul_two_add_bit_lt_two_pow x.val (ℓ - i - 1) (ℓ - i)
          ⟨0, by omega⟩ (by omega) (by omega)
        simp only [add_zero] at h_x_mul_2_lt
        simp only [gt_iff_lt]
        exact h_x_mul_2_lt⟩ =
      coeffsBySuffix (r := r) (R_rate := R_rate) original_coeffs
        (i := ⟨i.val + 1, by omega⟩) (v := ⟨v, by
          calc v.val < 2 ^ i.val := by omega
            _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)⟩) x := by
    simp only [coeffsBySuffix]
    have h_index_eq : (x.val * 2) <<< i.val ||| v.val = x.val <<< (i.val + 1) ||| v.val := by
      change (x.val * 2^1) <<< i.val ||| v.val = x.val <<< (i.val + 1) ||| v.val
      rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add]
      conv_lhs => rw [add_comm]
    simp_rw [h_index_eq]
  rw [h_coeffs_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem oddRefinement_eq_novel_poly_of_1_leading_suffix (i : Fin ℓ) (v : Fin (2 ^ i.val))
    (original_coeffs : Fin (2 ^ ℓ) → L) :
    have h_v : v.val ||| (1 <<< i.val) < 2 ^ (i.val + 1) := by
      apply Nat.or_lt_two_pow (x := v.val) (y := 1 <<< i.val) (n := i.val + 1) (by omega)
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    oddRefinement 𝔽q β h_ℓ_add_R_rate i (coeffsBySuffix (r := r) (R_rate := R_rate)
      original_coeffs ⟨i, by omega⟩ v) =
      intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩
        (coeffsBySuffix (r := r) (R_rate := R_rate) original_coeffs ⟨i + 1, by omega⟩
          ⟨v ||| (1 <<< i.val), h_v⟩) := by
  simp only [oddRefinement, Fin.eta, intermediateEvaluationPoly]
  set right_inner_func := fun x : Fin (2^(ℓ - (i.val + 1))) =>
    C (coeffsBySuffix (R_rate := R_rate) original_coeffs
      ⟨i.val + 1, by omega⟩ ⟨v.val ||| (1 <<< i.val), by
      simp only
      apply Nat.or_lt_two_pow
      · omega
      · rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.pow_lt_pow_right (by omega) (by omega)⟩ x) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩ x
  have h_right_sum_eq := Fin.sum_congr' (M := L[X]) (b := 2^(ℓ - (i.val + 1)))
    (a := 2^(ℓ - i - 1)) (f := right_inner_func) (h := by rfl)
  conv_rhs =>
    simp only [Fin.cast_eq_self]
    rw [← h_right_sum_eq]
    simp only [Fin.cast_eq_self]
  congr
  funext x
  simp only [right_inner_func]
  have h_coeffs_eq : coeffsBySuffix (r := r) (R_rate := R_rate) original_coeffs
      (i := ⟨i.val, by omega⟩) v ⟨↑x * 2 + 1, by
        have h_x_mul_2_lt := mul_two_add_bit_lt_two_pow x.val (ℓ - i - 1) (ℓ - i)
          ⟨1, by omega⟩ (by omega) (by omega)
        simp only at h_x_mul_2_lt
        simp only [gt_iff_lt]
        exact h_x_mul_2_lt⟩ =
      coeffsBySuffix (r := r) (R_rate := R_rate) original_coeffs (i := ⟨i.val + 1, by omega⟩)
        (v := ⟨v.val ||| (1 <<< i.val), by
          simp only
          apply Nat.or_lt_two_pow (x := v.val) (y := 1 <<< i.val) (n := i.val + 1) (by omega)
          rw [Nat.shiftLeft_eq, one_mul]
          exact Nat.pow_lt_pow_right (by omega) (by omega)⟩) x := by
    simp only [coeffsBySuffix]
    have h_index_eq : (x.val * 2 + 1) <<< i.val ||| v.val =
        x.val <<< (i.val + 1) ||| (v.val ||| (1 <<< i.val)) := by
      change (x.val * 2^1 + 1) <<< i.val ||| v.val =
        x.val <<< (i.val + 1) ||| (v.val ||| (1 <<< i.val))
      rw [← Nat.shiftLeft_eq]
      conv_lhs => rw [add_comm]
      conv_rhs => rw [Nat.or_comm v.val (1 <<< i.val), ← Nat.or_assoc]
      congr
      have h_left : 1 + (x.val <<< 1) = 1 ||| (x.val <<< 1) := by
        apply Nat.sum_of_and_eq_zero_is_or
        simp only [Nat.one_and_eq_mod_two, Nat.shiftLeft_eq]
        simp only [pow_one, Nat.mul_mod_left]
      rw [h_left, Nat.shiftLeft_add, Nat.shiftLeft_or_distrib, Nat.or_comm]
      rw [← Nat.shiftLeft_add, ← Nat.shiftLeft_add, Nat.add_comm]
    simp_rw [h_index_eq]
  rw [h_coeffs_eq]

def additiveNTTInvariant (evaluation_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
    (original_coeffs : Fin (2 ^ ℓ) → L) (i : Fin (ℓ + 1)) : Prop :=
  ∀ (j : Fin (2^(ℓ + R_rate))),
    let u_b_v := j.val
    let v : Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits := i.val) (n := u_b_v)
      simp only [res]⟩
    let u_b := u_b_v / (2^i.val)
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      have res := Nat.div_lt_of_lt_mul (m := u_b_v) (n := 2^i.val) (k := 2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a := 2) (m := i.val) (n := ℓ + R_rate) (by omega)))
      rw [h_u_b]
      exact res
    let b_bit := Nat.getLowBits 1 u_b_v
    let u := u_b / 2
    let coeffs_at_j : Fin (2 ^ (ℓ - i)) → L :=
      coeffsBySuffix (r := r) (R_rate := R_rate) original_coeffs i v
    let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate i coeffs_at_j
    let ω := evaluationPointω 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (Fin.mk u_b (by omega))
    evaluation_buffer j = P_i.eval ω

end Algorithm
end AdditiveNTT
