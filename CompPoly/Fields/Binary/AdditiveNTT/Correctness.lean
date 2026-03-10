/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.Algorithm

/-!
# Additive NTT Correctness

The stage-wise correctness argument and the final correctness theorem for the
Additive NTT.
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

section AlgorithmCorrectness

omit [DecidableEq 𝔽q] hF₂ in
lemma initial_tiled_coeffs_correctness (h_ℓ : ℓ ≤ r) (a : Fin (2 ^ ℓ) → L) :
    let b : Fin (2^(ℓ + R_rate)) → L := tileCoeffs a
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate b a (i := ⟨ℓ, by omega⟩) := by
  unfold additiveNTTInvariant
  simp only
  intro j
  unfold coeffsBySuffix
  simp only [tileCoeffs, evaluationPointω, intermediateEvaluationPoly, Fin.eta]
  have h_ℓ_sub_ℓ : 2^(ℓ - ℓ) = 1 := by norm_num
  set f_right : Fin (2^(ℓ - ℓ)) → L[X] :=
    fun ⟨x, hx⟩ => C (a ⟨↑x <<< ℓ ||| Nat.getLowBits ℓ (↑j), by
      simp only [tsub_self, pow_zero, Nat.lt_one_iff] at hx
      simp only [hx, Nat.zero_shiftLeft, Nat.zero_or]
      exact Nat.getLowBits_lt_two_pow (numLowBits := ℓ) (n := j.val)⟩) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨ℓ, by omega⟩ ⟨x, by omega⟩
  have h_sum_right : ∑ (x : Fin (2^(ℓ - ℓ))), f_right x =
      C (a ⟨Nat.getLowBits ℓ (↑j), by exact Nat.getLowBits_lt_two_pow ℓ⟩) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨ℓ, by omega⟩ 0 := by
    have h_sum_eq := Fin.sum_congr' (b := 2^(ℓ - ℓ)) (a := 1) (f := f_right) (by omega)
    rw [← h_sum_eq]
    rw [Fin.sum_univ_one]
    unfold f_right
    simp only [Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, tsub_self, pow_zero,
      Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    congr
  rw [h_sum_right]
  set f_left : Fin (ℓ + R_rate - ℓ) → L := fun x =>
    if Nat.getBit (x.val) (j.val / 2 ^ ℓ) = 1 then
      eval (β ⟨ℓ + x.val, by omega⟩) (normalizedW 𝔽q β ⟨ℓ, by omega⟩)
    else 0
  simp only [eval_mul, eval_C]
  have h_eval : eval (Finset.univ.sum f_left) (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate
      ⟨ℓ, by omega⟩ 0) = 1 := by
    have h_base_novel_basis := base_intermediateNovelBasisX 𝔽q β
      h_ℓ_add_R_rate ⟨ℓ, by exact Nat.lt_two_pow_self⟩
    simp only [intermediateNovelBasisX, Fin.coe_ofNat_eq_mod, tsub_self, pow_zero, Nat.zero_mod]
    set f_inner : Fin (ℓ - ℓ) → L[X] := fun x => intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨ℓ, by omega⟩ ⟨x, by simp only; omega⟩ ^ Nat.getBit (x.val) 0
    have h_sum_eq := Fin.prod_congr' (b := ℓ - ℓ) (a := 0) (f := f_inner) (by omega)
    simp_rw [← h_sum_eq, Fin.prod_univ_zero]
    simp only [eval_one]
  rw [h_eval, mul_one]
  simp only [Nat.getLowBits_eq_mod_two_pow]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma NTTStage_correctness (i : Fin (ℓ))
    (input_buffer : Fin (2 ^ (ℓ + R_rate)) → L) (original_coeffs : Fin (2 ^ ℓ) → L) :
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate (evaluation_buffer := input_buffer)
      (original_coeffs := original_coeffs) (i := ⟨i.val + 1, by omega⟩) →
      additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate
        (evaluation_buffer := NTTStage 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ input_buffer)
        (original_coeffs := original_coeffs) ⟨i, by omega⟩ := by
  intro h_prev
  simp only [additiveNTTInvariant] at h_prev
  set output_buffer := NTTStage 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ input_buffer
  unfold additiveNTTInvariant at *
  simp only at *
  intro j
  have h_j_div_2_pow_i_lt := div_two_pow_lt_two_pow (x := j.val)
    (i := ℓ + R_rate - i.val) (j := i.val) (by
      rw [Nat.sub_add_cancel (by omega)]
      omega)
  set cur_evaluation_point := evaluationPointω 𝔽q β h_ℓ_add_R_rate
    ⟨↑i, by omega⟩ ⟨↑j / 2 ^ i.val, by simp only; exact h_j_div_2_pow_i_lt⟩
  set cur_coeffs := coeffsBySuffix (R_rate := R_rate) original_coeffs ⟨↑i, by omega⟩
    ⟨Nat.getLowBits i.val (↑j), by exact Nat.getLowBits_lt_two_pow (numLowBits := i.val)⟩
  have h_P_i_split_even_odd := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate
    ⟨i, by omega⟩ cur_coeffs
  simp at h_P_i_split_even_odd
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ cur_coeffs
  set even_coeffs_poly := evenRefinement 𝔽q β h_ℓ_add_R_rate i cur_coeffs
  set odd_coeffs_poly := oddRefinement 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ cur_coeffs
  conv_lhs =>
    unfold output_buffer NTTStage
    simp only [beq_iff_eq, Fin.eta]
  have h_bit : Nat.getBit i.val j.val = (j.val / (2 ^ i.val)) % 2 := by
    simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have h_qmap_linear_map := qMap_is_linear_map 𝔽q β
    (i := ⟨i, by omega⟩)
  have h_qmap_additive : IsLinearMap 𝔽q fun x ↦ eval x (qMap 𝔽q β ⟨↑i, by omega⟩) :=
    linear_map_of_comp_to_linear_map_of_eval
      (f := (qMap 𝔽q β ⟨i, by omega⟩)) (h_f_linear := h_qmap_linear_map)
  let eval_qmap_linear : L →ₗ[𝔽q] L := {
    toFun := fun x ↦ eval x (qMap 𝔽q β ⟨i, by omega⟩)
    map_add' := h_qmap_additive.map_add
    map_smul' := h_qmap_additive.map_smul
  }
  have h_lsb_and_two_pow_eq_zero : (Nat.getLowBits i.val j.val) &&& (1 <<< i.val) = 0 := by
    rw [Nat.shiftLeft_eq, one_mul]
    apply Nat.and_two_pow_eq_zero_of_getBit_0
    rw [Nat.getBit_of_lowBits]
    simp only [lt_self_iff_false, ↓reduceIte]
  have h_j_div_2_pow_i_add_1_lt := div_two_pow_lt_two_pow (x := j.val)
    (i := ℓ + R_rate - (i.val + 1)) (j := i.val + 1) (by
      rw [Nat.sub_add_cancel (by omega)]
      omega)
  have h_j_div_2_pow_left : j.val / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
    simp only [Nat.div_div_eq_div_mul]
    congr
  have h_j_div_2_pow_div_2_left_lt : j.val / 2 ^ i.val / 2 < 2 ^ (ℓ + R_rate - (i.val + 1)) := by
    rw [← h_j_div_2_pow_left]
    exact h_j_div_2_pow_i_add_1_lt
  have h_eval_qmap_at_1 : eval 1 (qMap 𝔽q β ⟨↑i, by omega⟩) = 0 := by
    have h_1_is_algebra_map : (1 : L) = algebraMap 𝔽q L 1 := by rw [map_one]
    rw [h_1_is_algebra_map]
    apply qMap_eval_𝔽q_eq_0 𝔽q β (i := ⟨i, by omega⟩) (c := 1)
  have h_msb_eq_j_xor_lsb : (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
      = j.val ^^^ Nat.getLowBits (i.val + 1) j.val := by
    have h_xor : j.val = Nat.getHighBits (i.val + 1) j.val ^^^ Nat.getLowBits (i.val + 1) j.val :=
      Nat.num_eq_highBits_xor_lowBits (n := j.val) (i.val + 1)
    conv_lhs => rw [← Nat.shiftLeft_eq]; rw [← Nat.shiftRight_eq_div_pow]
    change Nat.getHighBits (i.val + 1) j.val = _
    conv_rhs => enter [1]; rw [h_xor]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have h_msb_eq_j_sub_lsb : (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
      = j.val - Nat.getLowBits (i.val + 1) j.val := by
    have h_msb := Nat.num_eq_highBits_add_lowBits (n := j.val) (numLowBits := i.val + 1)
    conv_rhs => enter [1]; rw [h_msb]
    norm_num
    rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  by_cases h_b_bit_eq_0 : (j.val / (2 ^ i.val)) % 2 = 0
  · simp only [h_b_bit_eq_0, ↓reduceDIte]
    simp only at h_b_bit_eq_0
    have bit_i_j_eq_0 : Nat.getBit i.val j.val = 0 := by omega
    set x0 := twiddleFactor 𝔽q β h_ℓ_add_R_rate i ⟨j.val / 2 ^ i.val / 2, by
      rw [h_j_div_2_pow_left.symm]
      exact h_j_div_2_pow_i_add_1_lt⟩
    have h_j_add_2_pow_i : j.val + 2 ^ i.val < 2 ^ (ℓ + R_rate) := by
      exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow
        (n := j.val) (m := ℓ + R_rate) (i := i.val) (h_n := by omega)
        (h_i := by omega) (h_getBit_at_i_eq_zero := by
          rw [← h_b_bit_eq_0]
          simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow])
    have h_even_split : input_buffer j =
        eval x0 (even_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev j]
      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x := ⟨j.val / 2 ^ i.val / 2, by
          rw [← h_j_div_2_pow_left]
          simp only [h_j_div_2_pow_i_add_1_lt]⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      conv_rhs =>
        rw [eval_comp]
        simp only [x0]
        rw [← h_twiddle_comp_qmap_eq_left]
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left]
      congr
      simp only [even_coeffs_poly, cur_coeffs]
      have h_res := evenRefinement_eq_novel_poly_of_0_leading_suffix 𝔽q β h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits := i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      have h_v_eq : Nat.getLowBits i.val j.val = Nat.getLowBits (i.val + 1) j.val := by
        rw [Nat.getLowBits_succ]
        rw [h_bit, h_b_bit_eq_0, Nat.zero_shiftLeft, Nat.add_zero]
      simp_rw [h_v_eq]
    have h_odd_split : input_buffer ⟨↑j + 2 ^ i.val, h_j_add_2_pow_i⟩ =
        eval x0 (odd_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev ⟨j.val + 2^i.val, by omega⟩]
      have h_j_div_2_pow_right : (⟨j.val + 2^i.val, by omega⟩ : Fin (2^(ℓ + R_rate))).val
          / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
        simp only
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add (a := 2) (m := i.val) (n := 1)]
        apply Nat.div_eq_of_lt_le (m := (j.val + 2 ^ i.val))
          (n := 2 ^ (i.val + 1)) (k := j.val / 2 ^ (i.val + 1))
        · calc
            (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1)) ≤ j.val := by
              simp only [Nat.div_mul_le_self (m := j.val) (n := 2^(i.val + 1))]
            _ ≤ _ := by exact Nat.le_add_right j.val (2 ^ i.val)
        · rw [add_mul]
          rw [one_mul]
          conv_rhs => enter [2]; rw [Nat.pow_succ, mul_two]
          rw [← Nat.add_assoc]
          apply Nat.add_lt_add_right
          have h_j : j = j / 2^(i.val + 1) * 2^(i.val + 1) + Nat.getLowBits i.val j.val := by
            conv_lhs => rw [Nat.num_eq_highBits_add_lowBits (n := j.val) (numLowBits := i.val + 1)]
            rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq,
              Nat.shiftRight_eq_div_pow]
            apply Nat.add_left_cancel_iff.mpr
            rw [Nat.getLowBits_succ]
            conv_rhs => rw [← Nat.add_zero (n := Nat.getLowBits i.val j.val)]
            apply Nat.add_left_cancel_iff.mpr
            rw [bit_i_j_eq_0, Nat.zero_shiftLeft]
          conv_lhs => rw [h_j]
          apply Nat.add_lt_add_left
          exact Nat.getLowBits_lt_two_pow (numLowBits := i.val) (n := j.val)
      have h_twiddle_comp_qmap_eq_right := eval_point_ω_eq_next_twiddleFactor_comp_qmap 𝔽q β
        h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x := ⟨j.val / 2 ^ i.val / 2, by
          exact h_j_div_2_pow_div_2_left_lt⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_right
      conv_rhs =>
        rw [eval_comp]
        simp only [x0]
        rw [← h_twiddle_comp_qmap_eq_right]
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_right]
      simp only [odd_coeffs_poly, cur_coeffs]
      have h_res := oddRefinement_eq_novel_poly_of_1_leading_suffix 𝔽q β h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits := i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      have h_j_and_2_pow_i_eq_0 : j.val &&& 2 ^ i.val = 0 := by
        apply Nat.and_two_pow_eq_zero_of_getBit_0
        omega
      have h_bit1 : Nat.getBit (i.val) (j.val + 2 ^ i.val) = 1 := by
        rw [Nat.sum_of_and_eq_zero_is_or h_j_and_2_pow_i_eq_0]
        rw [Nat.getBit_of_or]
        rw [Nat.getBit_two_pow]
        rw [bit_i_j_eq_0]
        simp only [BEq.rfl, ↓reduceIte, Nat.zero_or]
      have h_v_eq : Nat.getLowBits (i.val + 1) (j.val + 2^i.val)
          = (Nat.getLowBits i.val j.val) ||| 1 <<< i.val := by
        rw [Nat.getLowBits_succ]
        rw [h_bit1]
        have h_get_lsb_eq :
            Nat.getLowBits i.val (j.val + 2^i.val) = Nat.getLowBits i.val j.val := by
          apply Nat.eq_iff_eq_all_getBits.mpr
          intro k
          change Nat.getBit k (Nat.getLowBits i.val (j.val + 2^i.val)) =
            Nat.getBit k (Nat.getLowBits i.val j.val)
          rw [Nat.getBit_of_lowBits, Nat.getBit_of_lowBits]
          if h_k : k < i.val then
            simp only [h_k, ↓reduceIte]
            rw [Nat.getBit_of_add_distrib h_j_and_2_pow_i_eq_0]
            rw [Nat.getBit_two_pow]
            simp only [beq_iff_eq, Nat.add_eq_left, ite_eq_right_iff, one_ne_zero, imp_false]
            omega
          else
            simp only [h_k, ↓reduceIte]
        rw [h_get_lsb_eq]
        apply Nat.sum_of_and_eq_zero_is_or h_lsb_and_two_pow_eq_zero
      congr
    rw [h_even_split, h_odd_split]
    rw [h_P_i_split_even_odd]
    have h_x0_eq_cur_evaluation_point : x0 = cur_evaluation_point := by
      unfold x0 cur_evaluation_point
      simp only
      rw [evaluationPointω_eq_twiddleFactor_of_div_2 𝔽q]
      simp only [Fin.eta, h_b_bit_eq_0, Nat.cast_zero, zero_mul, add_zero]
    rw [h_x0_eq_cur_evaluation_point]
    simp only [eval_comp, eval_add, eval_mul, eval_X]
  · simp only [h_b_bit_eq_0, ↓reduceDIte]
    push_neg at h_b_bit_eq_0
    have bit_i_j_eq_1 : Nat.getBit i.val j.val = 1 := by omega
    simp only [ne_eq, Nat.mod_two_not_eq_zero] at h_b_bit_eq_0
    set x1 := twiddleFactor 𝔽q β h_ℓ_add_R_rate i
      ⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩ + 1
    have h_j_xor_2_pow_i : j.val ^^^ 2 ^ i.val < 2 ^ (ℓ + R_rate) := by
      exact Nat.xor_lt_two_pow (by omega) (by
        apply Nat.pow_lt_pow_right (by omega) (by omega))
    have h_2_pow_i_le_lsb_succ : 2 ^ i.val ≤ Nat.getLowBits (i.val + 1) j.val := by
      rw [Nat.getLowBits_succ]
      rw [bit_i_j_eq_1, Nat.shiftLeft_eq, one_mul]
      omega
    have h_2_pow_i_le_j : 2 ^ i.val ≤ j.val := by
      rw [Nat.num_eq_highBits_add_lowBits (n := j.val) (numLowBits := i.val + 1), add_comm]
      apply Nat.le_add_right_of_le
      exact h_2_pow_i_le_lsb_succ
    have h_j_and_2_pow_i_eq_2_pow_i : j.val &&& 2 ^ i.val = 2 ^ i.val := by
      rw [Nat.and_two_pow_eq_two_pow_of_getBit_1 (n := j.val) (i := i.val) (by omega)]
    have h_j_xor_2_pow_i_eq_sub : j.val ^^^ 2 ^ i.val = j.val - 2 ^ i.val := by
      exact Nat.xor_eq_sub_iff_submask (n := j.val) (m := 2^i.val)
        (h := h_2_pow_i_le_j).mpr h_j_and_2_pow_i_eq_2_pow_i
    have h_2_pow_i_le_lsb_succ_2 : Nat.getLowBits i.val j.val < 2 ^ i.val := by
      exact Nat.getLowBits_lt_two_pow (numLowBits := i.val) (n := j.val)
    have h_even_split : input_buffer ⟨↑j ^^^ 2 ^ i.val, h_j_xor_2_pow_i⟩ =
        eval x1 (even_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev ⟨j.val ^^^ 2 ^ i.val, by omega⟩]
      have h_j_div_2_pow_right : (⟨j.val ^^^ 2 ^ i.val, h_j_xor_2_pow_i⟩ :
        Fin (2^(ℓ + R_rate))).val / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
        simp only
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add (a := 2) (m := i.val) (n := 1)]
        apply Nat.div_eq_of_lt_le (m := (j.val ^^^ 2 ^ i.val))
          (n := 2 ^ (i.val + 1)) (k := j.val / 2 ^ (i.val + 1))
        · calc
            (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1)) =
                j.val - Nat.getLowBits (i.val + 1) j.val := by
                  rw [h_msb_eq_j_sub_lsb]
            _ ≤ j.val ^^^ 2 ^ i.val := by
                  rw [h_j_xor_2_pow_i_eq_sub]
                  apply Nat.sub_le_sub_left (k := j.val) (h := h_2_pow_i_le_lsb_succ)
        · rw [add_mul]
          rw [one_mul]
          conv_rhs =>
            rw [h_msb_eq_j_sub_lsb]
            rw [← Nat.sub_add_comm (h := Nat.getLowBits_le_self (n := j.val)
              (numLowBits := i.val + 1)), Nat.pow_succ, mul_two]
            rw [← Nat.add_assoc]
            rw [Nat.getLowBits_succ, bit_i_j_eq_1, Nat.shiftLeft_eq, one_mul]
            rw [Nat.add_comm (Nat.getLowBits i.val j.val) (2 ^ i.val), ← Nat.sub_sub]
            rw [Nat.add_sub_cancel (m := 2^i.val)]
          rw [Nat.add_sub_assoc (n := j.val) (m := 2^i.val)
            (k := Nat.getLowBits i.val j.val) (h := by omega)]
          omega
      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap 𝔽q β
        h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x := ⟨j.val / 2 ^ i.val / 2, by
          exact h_j_div_2_pow_div_2_left_lt⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      conv_rhs =>
        rw [eval_comp]
        simp only [x1]
      set t := twiddleFactor (r := r) 𝔽q β h_ℓ_add_R_rate
        (i := i) (u := ⟨j.val / 2 ^ i.val / 2, by
          exact h_j_div_2_pow_div_2_left_lt⟩) with ht
      have hh := eval_qmap_linear.map_add' (x := t) (y := 1)
      conv_rhs =>
        enter [1]
        change eval_qmap_linear.toFun (t + 1)
        rw [eval_qmap_linear.map_add' (x := t) (y := 1)]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, t]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, eval_qmap_linear]
        rw [← h_twiddle_comp_qmap_eq_left]
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left]
        simp only [h_j_div_2_pow_right]
      simp only [even_coeffs_poly, cur_coeffs]
      have h_res := evenRefinement_eq_novel_poly_of_0_leading_suffix 𝔽q β h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits := i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      have h_bit0 : Nat.getBit (i.val) (j.val ^^^ 2 ^ i.val) = 0 := by
        rw [Nat.getBit_of_xor (n := j.val) (m := 2^i.val) (k := i.val)]
        rw [bit_i_j_eq_1, Nat.getBit_two_pow]
        simp only [BEq.rfl, ↓reduceIte, Nat.xor_self]
      have h_v_eq :
          Nat.getLowBits (i.val + 1) (j.val ^^^ 2^i.val) = Nat.getLowBits i.val j.val := by
        rw [Nat.getLowBits_succ]
        rw [h_bit0, Nat.zero_shiftLeft, Nat.add_zero]
        apply Nat.eq_iff_eq_all_getBits.mpr
        intro k
        change Nat.getBit k (Nat.getLowBits i.val (j.val ^^^ 2^i.val)) =
          Nat.getBit k (Nat.getLowBits i.val j.val)
        rw [Nat.getBit_of_lowBits, Nat.getBit_of_lowBits]
        if h_k : k < i.val then
          simp only [h_k, ↓reduceIte]
          rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
          have h_ne_i_eq_k : ¬(i.val = k) := by omega
          simp only [beq_iff_eq, h_ne_i_eq_k, ↓reduceIte, Nat.xor_zero]
        else
          simp only [h_k, ↓reduceIte]
      have h_suffix_fin_eq :
          (⟨Nat.getLowBits (i.val + 1) (j.val ^^^ 2 ^ i.val),
            Nat.getLowBits_lt_two_pow (numLowBits := i.val + 1)⟩ : Fin (2 ^ (i.val + 1))) =
          ⟨Nat.getLowBits i.val j.val, by
            calc Nat.getLowBits i.val j.val
              < 2 ^ i.val := Nat.getLowBits_lt_two_pow (numLowBits := i.val)
              _ < 2 ^ (i.val + 1) := Nat.pow_lt_pow_right (by omega) (by omega)⟩ :=
        Fin.ext h_v_eq
      simp only [h_suffix_fin_eq]
      congr 1
      rw [h_eval_qmap_at_1, add_zero]
    have h_odd_split : input_buffer j = eval x1
      (odd_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev j]
      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (x := ⟨j.val / 2 ^ i.val / 2, by
          rw [← h_j_div_2_pow_left]
          have h := div_two_pow_lt_two_pow (x := j.val) (i :=
            ℓ + R_rate - (i.val + 1)) (j := i.val + 1) (by
            rw [Nat.sub_add_cancel (by omega)]
            omega)
          calc _ < 2 ^ (ℓ + R_rate - (i.val + 1)) := by omega
            _ = _ := by rfl⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      conv_rhs =>
        rw [eval_comp]
        simp only [x1]
      set t := twiddleFactor (r := r) 𝔽q β h_ℓ_add_R_rate (i := i)
        (u := ⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩) with ht
      have hh := eval_qmap_linear.map_add' (x := t) (y := 1)
      conv_rhs =>
        enter [1]
        change eval_qmap_linear.toFun (t + 1)
        rw [eval_qmap_linear.map_add' (x := t) (y := 1)]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, t]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, eval_qmap_linear]
        rw [← h_twiddle_comp_qmap_eq_left]
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left]
      simp only [odd_coeffs_poly, cur_coeffs]
      have h_res := oddRefinement_eq_novel_poly_of_1_leading_suffix 𝔽q β h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits := i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]
      congr
      rw [h_eval_qmap_at_1, add_zero]
      have h_v_eq : Nat.getLowBits (i.val + 1) j.val
          = Nat.getLowBits i.val j.val ||| 1 <<< i.val := by
        rw [Nat.getLowBits_succ]
        rw [h_bit, h_b_bit_eq_0]
        apply Nat.sum_of_and_eq_zero_is_or h_lsb_and_two_pow_eq_zero
      simp_rw [h_v_eq]
    rw [h_even_split, h_odd_split]
    rw [h_P_i_split_even_odd]
    have h_x1_eq_cur_evaluation_point : x1 = cur_evaluation_point := by
      unfold x1 cur_evaluation_point
      simp only
      rw [evaluationPointω_eq_twiddleFactor_of_div_2 𝔽q]
      simp only [Fin.eta, h_b_bit_eq_0, Nat.cast_one, one_mul, add_right_inj]
      rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    rw [h_x1_eq_cur_evaluation_point]
    simp only [eval_comp, eval_add, eval_mul, eval_X]

omit [DecidableEq 𝔽q] hF₂ in
lemma foldl_NTTStage_inductive_aux (h_ℓ : ℓ ≤ r) (k : Fin (ℓ + 1))
    (original_coeffs : Fin (2 ^ ℓ) → L) :
    additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate
      (Fin.foldl k (fun current_b i ↦ NTTStage 𝔽q β h_ℓ_add_R_rate
        ⟨ℓ - i - 1, by omega⟩ current_b) (tileCoeffs original_coeffs))
      original_coeffs ⟨ℓ - k, by omega⟩ := by
  have invariant_init := initial_tiled_coeffs_correctness 𝔽q β h_ℓ_add_R_rate h_ℓ original_coeffs
  simp only at invariant_init
  induction k using Fin.succRecOnSameFinType with
  | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero, tsub_zero]
      exact invariant_init
  | succ k k_h i_h =>
      have h_k_add_one := Fin.val_add_one' (a := k) (by omega)
      simp only [h_k_add_one, Fin.val_cast]
      simp only [Fin.foldl_succ_last, Fin.val_last, Fin.val_castSucc]
      set ntt_round := ℓ - (k + 1)
      set input_buffer := Fin.foldl k (fun current_b i ↦ NTTStage 𝔽q β h_ℓ_add_R_rate
        ⟨ℓ - i - 1, by omega⟩ current_b) (tileCoeffs original_coeffs)
      have correctness_transition :=
        NTTStage_correctness 𝔽q β h_ℓ_add_R_rate
          (i := ⟨ntt_round, by omega⟩)
          (input_buffer := input_buffer)
          (original_coeffs := original_coeffs)
      simp only at correctness_transition
      have h_ℓ_sub_k : ℓ - k = ntt_round + 1 := by omega
      simp_rw [h_ℓ_sub_k] at i_h
      have res := correctness_transition i_h
      exact res

omit [DecidableEq 𝔽q] hF₂ in
theorem additiveNTT_correctness (h_ℓ : ℓ ≤ r)
    (original_coeffs : Fin (2 ^ ℓ) → L)
    (output_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
    (h_alg : output_buffer = additiveNTT 𝔽q β h_ℓ_add_R_rate original_coeffs) :
    let P := polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ original_coeffs
    ∀ (j : Fin (2^(ℓ + R_rate))),
      output_buffer j = P.eval (evaluationPointω 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ j) := by
  simp only [Fin.zero_eta]
  intro j
  simp only [h_alg]
  unfold additiveNTT
  set output_foldl := Fin.foldl ℓ (fun current_b i ↦ NTTStage 𝔽q β h_ℓ_add_R_rate
    ⟨ℓ - i - 1, by omega⟩ current_b) (tileCoeffs original_coeffs)
  have output_foldl_correctness : additiveNTTInvariant 𝔽q β h_ℓ_add_R_rate
      output_foldl original_coeffs ⟨0, by omega⟩ := by
    have res := foldl_NTTStage_inductive_aux 𝔽q β h_ℓ_add_R_rate
      h_ℓ
      (k := ⟨ℓ, by omega⟩) original_coeffs
    simp only [tsub_self, Fin.zero_eta] at res
    exact res
  have h_nat_point_ω_eq_j : j.val / 2 * 2 + j.val % 2 = j := by
    have h_j_mod_2_eq_0 : j.val % 2 < 2 := by omega
    exact Nat.div_add_mod' (↑j) 2
  simp only [additiveNTTInvariant] at output_foldl_correctness
  have res := output_foldl_correctness j
  unfold output_foldl at res
  simp only [Fin.zero_eta, Nat.sub_zero, pow_zero, Nat.div_one, Fin.eta,
    Nat.pow_zero, Nat.getLowBits_zero_eq_zero (n := j.val), Fin.isValue, base_coeffsBySuffix] at res
  simp only [←
    intermediate_poly_P_base 𝔽q β h_ℓ_add_R_rate
      h_ℓ original_coeffs,
    Fin.zero_eta]
  rw [← res]
  simp_rw [Nat.sub_right_comm]

end AlgorithmCorrectness
end AdditiveNTT
