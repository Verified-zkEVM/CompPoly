/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Use
import Mathlib.Data.Finsupp.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Additive NTT Domains

Domain-level constructions for the Additive NTT: quotient maps, intermediate
domains, and the finite-domain bijections used by the algorithm.
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

omit h_Fq_char_prime in
lemma 𝔽q_element_eq_zero_or_eq_one : ∀ c : 𝔽q, c = 0 ∨ c = 1 := by
  intro c
  by_cases hc : c = 0
  · left
    omega
  · right
    have h_card_units : Fintype.card 𝔽qˣ = 1 := by
      rw [Fintype.card_units, hF₂.out]
    have h_c_is_one : Units.mk0 c hc = (1 : 𝔽qˣ) := by
      haveI : Subsingleton 𝔽qˣ := by
        apply Fintype.card_le_one_iff_subsingleton.mp
        exact Nat.le_of_eq h_card_units
      apply Subsingleton.elim
    exact congr_arg Units.val h_c_is_one

section IntermediateStructures

noncomputable def sDomain (i : Fin r) : Subspace 𝔽q L :=
  let W_i_norm := normalizedW 𝔽q β i
  let h_W_i_norm_is_additive : IsLinearMap 𝔽q (fun x : L => W_i_norm.eval x) :=
    AdditiveNTT.normalizedW_is_additive 𝔽q β i
  Submodule.map (polyEvalLinearMap W_i_norm h_W_i_norm_is_additive)
    (U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩)

noncomputable def qMap (i : Fin r) : L[X] :=
  let constMultiplier := ((W 𝔽q β i).eval (β i))^(Fintype.card 𝔽q)
    / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  C constMultiplier * ∏ c : 𝔽q, (X - C (algebraMap 𝔽q L c))

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem qMap_eval_𝔽q_eq_0 (i : Fin r) :
    ∀ c : 𝔽q, (qMap 𝔽q β i).eval (algebraMap 𝔽q L c) = 0 := by
  intro u
  rw [qMap]
  set vpoly𝔽q := ∏ c : 𝔽q, (X - C ((algebraMap 𝔽q L) c)) with h_vpoly𝔽q
  have h_right_term_vanish : eval ((algebraMap 𝔽q L) u) (vpoly𝔽q) = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C, vpoly𝔽q]
    rw [Finset.prod_eq_zero_iff]
    have hu : u ∈ (Finset.univ : Finset 𝔽q) := by
      simp only [Finset.mem_univ]
    use u
    constructor
    · exact hu
    · simp only [sub_self]
  simp only [eval_mul, eval_C, h_right_term_vanish, mul_zero]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma qMap_comp_normalizedW (i : Fin r) (h_i_add_1 : i + 1 < r) :
    (qMap 𝔽q β i).comp (normalizedW 𝔽q β i) = normalizedW 𝔽q β (i + 1) := by
  let q := Fintype.card 𝔽q
  set q := Fintype.card 𝔽q
  set W_i := W 𝔽q β i with h_W_i
  set W_i_plus_1 := W 𝔽q β (i + 1) with h_W_i_plus_1
  set val_i := W_i.eval (β i) with h_val_i
  set val_i_plus_1 := W_i_plus_1.eval (β (i + 1)) with h_val_i_plus_1
  have h_val_i_ne_zero : val_i ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β i
  have h_val_i_plus_1_ne_zero : val_i_plus_1 ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β (i + 1)
  calc
    (qMap 𝔽q β i).comp (normalizedW 𝔽q β i)
    _ = C (val_i ^ q / val_i_plus_1)
      * (∏ c : 𝔽q, (X - C (algebraMap 𝔽q L c))).comp (normalizedW 𝔽q β i) := by
        rw [qMap, mul_comp, C_comp]
    _ = C (val_i ^ q / val_i_plus_1) * ((normalizedW 𝔽q β i) ^ q - normalizedW 𝔽q β i) := by
        simp_rw [prod_comp, sub_comp, X_comp, C_comp]
        rw [prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L]
    _ = C (1 / val_i_plus_1) * (W_i ^ q - C (val_i ^ (q - 1)) * W_i) := by
        rw [normalizedW, mul_sub, mul_pow, C_pow]
        have hq_pos : q > 0 := by
          exact Fintype.card_pos
        have h_C : C (val_i ^ q / val_i_plus_1) = C (1 / val_i_plus_1) * C (val_i ^ q) := by
          rw [← C_mul]
          ring_nf
        rw [h_C]
        conv_lhs =>
          rw [mul_assoc, mul_assoc]
          rw [← mul_sub]
        rw [← h_val_i, ← h_W_i]
        rw [← C_pow]
        rw [← mul_assoc, ← C_mul]
        have h_mul : val_i ^ q * (1 / val_i) ^ q = 1 := by
          rw [← mul_pow (n := q)]
          rw [← inv_eq_one_div]
          rw [mul_inv_cancel₀ (h := h_val_i_ne_zero), one_pow]
        rw [h_mul, C_1, one_mul]
        rw [← mul_assoc, ← C_mul]
        have h_mul_2 : val_i ^ q * (1 / val_i) = val_i ^ (q - 1) := by
          rw [← inv_eq_one_div]
          rw [← mul_pow_sub_one (hn := by omega), mul_comm (a := val_i), mul_assoc]
          rw [mul_inv_cancel₀ (h := h_val_i_ne_zero), mul_one]
        rw [h_mul_2, C_pow]
    _ = C (1 / val_i_plus_1) * W_i_plus_1 := by
        have W_linear := AdditiveNTT.W_linear_comp_decomposition 𝔽q β
          i (p := X)
        simp_rw [comp_X] at W_linear
        simp_rw [q, val_i, W_i, W_i_plus_1]
        rw [W_linear]
        · simp only [one_div, map_pow]
        · omega
    _ = normalizedW 𝔽q β (i + 1) := by
        rw [normalizedW]

omit [DecidableEq L] [DecidableEq 𝔽q] hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem qMap_is_linear_map (i : Fin r) :
    IsLinearMap 𝔽q (f := fun inner_p ↦ (qMap 𝔽q β i).comp inner_p) := by
  set q := Fintype.card 𝔽q
  set constMultiplier := ((W 𝔽q β i).eval (β i))^q / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  have h_q_poly_form : qMap 𝔽q β i = C constMultiplier * (X ^ q - X) := by
    rw [qMap, prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L (p := X)]
  constructor
  · intro f g
    calc
      _ = (C constMultiplier * (X ^ q - X)).comp (f + g) := by
            rw [h_q_poly_form]
      _ = ((C constMultiplier).comp (f + g)) * (((X : L[X]) ^ q - X).comp (f + g)) := by
            rw [mul_comp]
      _ = (C constMultiplier) * ((X ^ q).comp (f + g) - X.comp (f + g)) := by
            rw [C_comp, sub_comp]
      _ = (C constMultiplier) * ((X ^ q).comp (f + g) - (X.comp f + X.comp g)) := by
            rw [X_comp]
            conv_lhs =>
              enter [2, 2]
              rw [← X_comp (p := f), ← X_comp (p := g)]
      _ = (C constMultiplier) * (f^q + g^q - (X.comp f + X.comp g)) := by
            rw [pow_comp, X_comp]
            unfold q
            rw [Polynomial.frobenius_identity_in_algebra (f := f) (g := g)]
      _ = (C constMultiplier) * (((X^q).comp f - X.comp f) + ((X^q).comp g - X.comp g)) := by
            rw [pow_comp, X_comp, X_comp, pow_comp, X_comp]
            ring
      _ = (C constMultiplier) * (((X : L[X]) ^ q - X).comp f + ((X : L[X]) ^ q - X).comp g) := by
            rw [← sub_comp, ← sub_comp]
      _ = (qMap 𝔽q β i).comp f + (qMap 𝔽q β i).comp g := by
            rw [h_q_poly_form]
            rw [mul_add]
            rw [mul_comp, mul_comp, C_comp, C_comp]
  · intro c f
    calc
      _ = (C constMultiplier * (X ^ q - X)).comp (c • f) := by
            rw [h_q_poly_form]
      _ = (C constMultiplier).comp (c • f) * ((c • f) ^ q - (c • f)) := by
            rw [mul_comp, sub_comp, pow_comp, X_comp]
      _ = (C constMultiplier).comp (c • f) * (c ^ q • f ^ q - c • f) := by
            rw [C_comp, smul_pow]
      _ = (C constMultiplier).comp (c • f) * (c • f^q - c • f) := by
            rw [FiniteField.pow_card]
      _ = (C constMultiplier).comp (c • f) * (C (algebraMap 𝔽q L c) * (f^q - f)) := by
            conv_lhs =>
              enter [2]
              rw [algebra_compatible_smul L c, algebra_compatible_smul L c]
              rw [smul_eq_C_mul, smul_eq_C_mul]
              rw [← mul_sub]
      _ = c • ((C constMultiplier).comp (c • f) * (f^q - f)) := by
            rw [← mul_assoc, mul_comm (a := (C constMultiplier).comp (c • f)), mul_assoc]
            rw [← smul_eq_C_mul]
            rw [← algebra_compatible_smul L c]
      _ = c • (((C constMultiplier) * ((X : L[X])^q - X)).comp f) := by
            rw [C_comp]
            conv_lhs =>
              enter [2, 2]
              rw [← X_comp (p := f)]
            rw [← pow_comp, ← sub_comp]
            rw [C_mul_comp]
      _ = c • (qMap 𝔽q β i).comp f := by
            rw [h_q_poly_form]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
theorem qMap_maps_sDomain (i : Fin r) (h_i_add_1 : i + 1 < r) :
    have q_comp_linear_map := qMap_is_linear_map 𝔽q β i
    have q_eval_linear_map := linear_map_of_comp_to_linear_map_of_eval
      (f := qMap 𝔽q β i) q_comp_linear_map
    let q_i_map := polyEvalLinearMap (qMap 𝔽q β i) q_eval_linear_map
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let S_i_plus_1 := sDomain 𝔽q β h_ℓ_add_R_rate (i + 1)
    Submodule.map q_i_map S_i = S_i_plus_1 := by
  set q_comp_linear_map := qMap_is_linear_map 𝔽q β i
  set q_eval_linear_map := linear_map_of_comp_to_linear_map_of_eval
    (f := qMap 𝔽q β i) q_comp_linear_map
  simp_rw [sDomain]
  rw [← Submodule.map_comp]
  congr
  set f := polyEvalLinearMap (qMap 𝔽q β i) q_eval_linear_map
  set g := polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β i)
  set t := polyEvalLinearMap (normalizedW 𝔽q β (i + 1))
    (normalizedW_is_additive 𝔽q β (i + 1))
  ext x
  rw [LinearMap.comp_apply]
  simp_rw [f, g, t, polyEvalLinearMap]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Polynomial.eval_comp]
  rw [qMap_comp_normalizedW 𝔽q β i h_i_add_1]

noncomputable def qCompositionChain (i : Fin r) : L[X] :=
  match i with
  | ⟨0, _⟩ => X
  | ⟨k + 1, h_k_add_1⟩ => (qMap 𝔽q β ⟨k, by omega⟩).comp (qCompositionChain ⟨k, by omega⟩)

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma qCompositionChain_eq_foldl (i : Fin r) :
    qCompositionChain 𝔽q β (ℓ := ℓ) (R_rate := R_rate) i =
      Fin.foldl (n := i) (fun acc j =>
        (qMap 𝔽q β ⟨j, by omega⟩).comp acc) X := by
  induction i using Fin.succRecOnSameFinType with
  | zero =>
      rw [qCompositionChain.eq_def]
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero]
      rfl
  | succ k k_h i_h =>
      rw [qCompositionChain.eq_def]
      have h_eq : ⟨k.val.succ, k_h⟩ = k + 1 := by
        rw [Fin.mk_eq_mk]
        rw [Fin.val_add_one']
        exact k_h
      simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
      simp only [Fin.val_cast, Fin.foldl_succ_last, Fin.val_last, Fin.eta, Fin.val_castSucc]
      congr

omit [DecidableEq 𝔽q] hF₂ in
lemma normalizedW_eq_qMap_composition (ℓ R_rate : ℕ) (i : Fin r) :
    normalizedW 𝔽q β i = qCompositionChain 𝔽q β (ℓ := ℓ) (R_rate := R_rate) i := by
  induction i using Fin.succRecOnSameFinType with
  | zero =>
      rw [qCompositionChain.eq_def]
      rw [normalizedW, W₀_eq_X, eval_X, h_β₀_eq_1.out, div_one, C_1, one_mul]
      rfl
  | succ k k_h i_h =>
      rw [qCompositionChain.eq_def]
      have h_eq : ⟨k.val.succ, k_h⟩ = k + 1 := by
        rw [Fin.mk_eq_mk]
        rw [Fin.val_add_one']
        exact k_h
      simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
      have h_res := qMap_comp_normalizedW 𝔽q β k k_h
      rw [← i_h]
      rw [h_res]
      simp only [h_eq]

noncomputable def sDomainBasisVectors (i : Fin r) : Fin (ℓ + R_rate - i) → L :=
  fun k => (normalizedW 𝔽q β i).eval (β ⟨i + k.val, by omega⟩)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma sDomainBasisVectors_mem_sDomain (i : Fin r) (k : Fin (ℓ + R_rate - i)) :
    sDomainBasisVectors 𝔽q β h_ℓ_add_R_rate i k
      ∈ sDomain 𝔽q β h_ℓ_add_R_rate i := by
  have h_i_add_k_lt_r : i + k.val < r := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  simp_rw [sDomain, sDomainBasisVectors]
  apply Submodule.mem_map_of_mem
  have h_β_i_in_U :
      β ⟨i + k.val, h_i_add_k_lt_r⟩ ∈ β '' Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
    exact Set.mem_image_of_mem β (Set.mem_Ico.mpr ⟨by norm_num, by omega⟩)
  exact Submodule.subset_span h_β_i_in_U

def sBasis (i : Fin r) (h_i : i < ℓ + R_rate) : Fin (ℓ + R_rate - i) → L :=
  fun k => β ⟨i + k.val, by omega⟩

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [Field 𝔽q] [Algebra 𝔽q L] in
lemma sBasis_range_eq (i : Fin r) (h_i : i < ℓ + R_rate) :
    β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ = Set.range (sBasis β h_ℓ_add_R_rate i h_i) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨j, hj, rfl⟩
    simp only [Set.mem_Ico] at hj
    simp only [Set.mem_range]
    have h_j_sub_i : j.val - i.val < ℓ + R_rate - i.val := by
      apply Nat.lt_sub_of_add_lt
      rw [Nat.sub_add_cancel]
      · exact hj.2
      · omega
    use ⟨j - i, h_j_sub_i⟩
    unfold sBasis
    simp only
    have h_i_add_j_sub_i : i.val + (j.val - i.val) = j.val := by
      omega
    congr
  · intro hx
    rcases hx with ⟨j, hj, rfl⟩
    simp only [Set.mem_image, Set.mem_Ico]
    use ⟨i.val + j.val, by omega⟩
    constructor
    · constructor
      · have h_j := j.2
        have h_i_add_j : i.val + j.val < ℓ + R_rate := by
          omega
        have h_i_add_j_lt_r : i.val + j.val < r := by
          omega
        apply Fin.mk_le_of_le_val
        conv_rhs => simp only
        omega
      · apply Fin.mk_lt_of_lt_val
        conv_rhs => simp only
        omega
    · rfl

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma sDomain_eq_image_of_upper_span (i : Fin r) (h_i : i < ℓ + R_rate) :
    let V_i := Submodule.span 𝔽q (Set.range (sBasis β h_ℓ_add_R_rate i h_i))
    let W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i)
      (normalizedW_is_additive 𝔽q β i)
    sDomain 𝔽q β h_ℓ_add_R_rate i = Submodule.map W_i_map V_i := by
  set V_i := Submodule.span 𝔽q (Set.range (sBasis β h_ℓ_add_R_rate i h_i))
  set W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β i)
  have h_span_supremum_decomposition : U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ = U 𝔽q β i ⊔ V_i := by
    unfold U
    have h_ico :
        Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ =
          Set.Ico 0 i ∪ Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
      ext k
      simp only [Set.mem_Ico, Fin.zero_le, true_and, Set.mem_union]
      constructor
      · intro h
        by_cases hk : k < i
        · left
          omega
        · right
          exact ⟨Nat.le_of_not_lt hk, by omega⟩
      · intro h
        cases h with
        | inl h => exact Fin.lt_trans h h_i
        | inr h => exact h.2
    rw [h_ico, Set.image_union, Submodule.span_union]
    congr
    rw [sBasis_range_eq β h_ℓ_add_R_rate i h_i]
  rw [sDomain, h_span_supremum_decomposition, Submodule.map_sup]
  have h_U_i_image : Submodule.map W_i_map (U 𝔽q β i) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    have h_eval_zero : (normalizedW 𝔽q β i).eval y = 0 :=
      normalizedWᵢ_vanishing 𝔽q β i y hy
    exact h_eval_zero
  rw [h_U_i_image]
  rw [bot_sup_eq]

noncomputable def sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    Basis (Fin (ℓ + R_rate - i)) 𝔽q (sDomain 𝔽q β h_ℓ_add_R_rate i) := by
  let V_i := Submodule.span 𝔽q (Set.range (sBasis β h_ℓ_add_R_rate i h_i))
  let W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i) (
    normalizedW_is_additive 𝔽q β i)
  have h_disjoint : Disjoint (U 𝔽q β i) V_i := by
    have h_set_disjoint : Disjoint (Set.Ico 0 i) (Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩) := by
      simp [Set.disjoint_iff]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ico, Fin.zero_le, true_and,
        Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hx hi
      omega
    unfold V_i
    have h_res := hβ_lin_indep.out.disjoint_span_image h_set_disjoint
    rw [sBasis_range_eq β h_ℓ_add_R_rate i h_i] at h_res
    exact h_res
  have h_ker_eq_U : LinearMap.ker W_i_map = U 𝔽q β i := by
    rw [kernel_normalizedW_eq_U 𝔽q β i]
  let V_i_basis : Basis (Fin (ℓ + R_rate - i)) 𝔽q V_i :=
    Basis.span (by
      have h_sub_li : LinearIndependent 𝔽q (
          v := fun (k : Fin (ℓ + R_rate - i)) => β ⟨i + k.val, by omega⟩) :=
        hβ_lin_indep.out.comp (fun (k : Fin (ℓ + R_rate - i))
          => ⟨i + k.val, by omega⟩) (by
          intro k₁ k₂ h_eq
          simp at h_eq
          apply Fin.eq_of_val_eq
          omega)
      exact h_sub_li)
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  let iso : V_i ≃ₗ[𝔽q] S_i :=
    LinearEquiv.ofBijective
      (LinearMap.codRestrict S_i (W_i_map.comp (Submodule.subtype V_i))
        (by
          intro x
          have h_x_in_S_i : (W_i_map.comp (Submodule.subtype V_i)) x ∈ S_i := by
            simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, S_i]
            rw [sDomain_eq_image_of_upper_span 𝔽q β h_ℓ_add_R_rate i h_i]
            exact
              Submodule.apply_coe_mem_map
                (polyEvalLinearMap (normalizedW 𝔽q β i)
                  (normalizedW_is_additive 𝔽q β i))
                x
          exact h_x_in_S_i)) (by
          constructor
          · intro v1 v2 h_v1_v2
            simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Submodule.coe_subtype,
              Function.comp_apply, Subtype.ext_iff] at h_v1_v2
            rw [← sub_eq_zero, ← LinearMap.map_sub] at h_v1_v2
            apply Subtype.ext
            have h_mem_ker : ↑(v1 - v2) ∈ LinearMap.ker W_i_map := h_v1_v2
            have h_mem_U : ↑(v1 - v2) ∈ U 𝔽q β i := h_ker_eq_U ▸ h_mem_ker
            have h_mem_V : ↑(v1 - v2) ∈ V_i := Submodule.sub_mem V_i v1.property v2.property
            have h_mem_inf : ↑(v1 - v2) ∈ (U 𝔽q β i) ⊓ V_i :=
              Submodule.mem_inf.mpr ⟨h_mem_U, h_mem_V⟩
            rw [h_disjoint.eq_bot] at h_mem_inf
            simp only [Submodule.mem_bot] at h_mem_inf
            simp at h_mem_inf
            rw [sub_eq_zero] at h_mem_inf
            exact h_mem_inf
          · intro y
            have h_y_in_image : y.val ∈ Submodule.map W_i_map V_i := by
              have h_y := y.property
              unfold W_i_map V_i
              have h_S_i : S_i = Submodule.map W_i_map V_i := by
                unfold S_i
                rw [sDomain_eq_image_of_upper_span 𝔽q β h_ℓ_add_R_rate i h_i]
              rw [← h_S_i]
              exact h_y
            rcases h_y_in_image with ⟨x, hx_in_Vi, hx_maps_to_y⟩
            use ⟨x, hx_in_Vi⟩
            apply Subtype.ext
            exact hx_maps_to_y)
  exact V_i_basis.map iso

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma get_sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    ∀ (k : Fin (ℓ + R_rate - i)),
      (sDomain_basis 𝔽q β h_ℓ_add_R_rate i (by omega)) k =
        eval (β ⟨i + k.val, by omega⟩) (normalizedW 𝔽q β i) := by
  intro k
  unfold sDomain_basis
  simp only [polyEvalLinearMap, eq_mpr_eq_cast, cast_eq, Basis.map_apply,
    LinearEquiv.ofBijective_apply, LinearMap.codRestrict_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype, Function.comp_apply]
  congr
  rw [Basis.span_apply]
  dsimp only [sBasis]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma get_sDomain_first_basis_eq_1 (i : Fin r) (h_i : i < ℓ + R_rate) :
    (sDomain_basis 𝔽q β h_ℓ_add_R_rate i (by omega)) ⟨0, by omega⟩ = (1 : L) := by
  rw [get_sDomain_basis]
  simp only [add_zero, Fin.eta]
  exact normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β

noncomputable instance fintype_sDomain (i : Fin r) : Fintype (sDomain 𝔽q β h_ℓ_add_R_rate i) := by
  exact Fintype.ofFinite (sDomain 𝔽q β h_ℓ_add_R_rate i)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma sDomain_card (i : Fin r) (h_i : i < ℓ + R_rate) :
    Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate i) = (Fintype.card 𝔽q)^(ℓ + R_rate - i) := by
  rw [Module.card_eq_pow_finrank (K := 𝔽q) (V := sDomain 𝔽q β h_ℓ_add_R_rate i)]
  let b := sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i
  rw [Module.finrank_eq_card_basis b]
  simp only [Fintype.card_fin]

noncomputable section DomainBijection

def splitPointIntoCoeffs (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) : Fin (ℓ + R_rate - i.val) → ℕ := fun j =>
  if ((sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i).repr x j = 0) then 0 else 1

noncomputable def sDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) : Fin (2^(ℓ + R_rate - i.val)) := by
  apply Nat.binaryFinMapToNat (n := ℓ + R_rate - i.val)
    (m := splitPointIntoCoeffs 𝔽q β h_ℓ_add_R_rate i h_i x) (by
      intro j
      simp only [splitPointIntoCoeffs]
      split_ifs <;> norm_num)

def finToBinaryCoeffs (i : Fin r) (idx : Fin (2 ^ (ℓ + R_rate - i.val))) :
    Fin (ℓ + R_rate - i.val) → 𝔽q := fun j =>
  if (Nat.getBit (k := j) (n := idx)) = 1 then (1 : 𝔽q) else (0 : 𝔽q)

omit h_β₀_eq_1 in
lemma finToBinaryCoeffs_sDomainToFin (i : Fin r) (h_i : i < ℓ + R_rate)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
    let pointFinIdx := (sDomainToFin 𝔽q β h_ℓ_add_R_rate i h_i) x
    finToBinaryCoeffs 𝔽q (i := i) (idx := pointFinIdx) = (sDomain_basis 𝔽q β
      h_ℓ_add_R_rate i h_i).repr x := by
  simp only
  ext j
  dsimp [sDomainToFin, finToBinaryCoeffs, splitPointIntoCoeffs]
  rw [Nat.getBit_of_binaryFinMapToNat]
  set c := (sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i).repr x j
  have hc : c = 0 ∨ c = 1 := by
    exact 𝔽q_element_eq_zero_or_eq_one 𝔽q c
  rcases hc with h_c_zero | h_c_one
  · simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, h_c_zero, ite_eq_right_iff, one_ne_zero, imp_false,
      ne_eq]
    unfold splitPointIntoCoeffs
    simp only [ite_eq_right_iff, zero_ne_one, imp_false, Decidable.not_not]
    omega
  · simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, h_c_one, ite_eq_left_iff, zero_ne_one, imp_false,
      Decidable.not_not]
    unfold splitPointIntoCoeffs
    simp only [ite_eq_right_iff, zero_ne_one, imp_false, ne_eq]
    change ¬(c) = 0
    rw [h_c_one]
    exact one_ne_zero

noncomputable def finToSDomain (i : Fin r) (h_i : i < ℓ + R_rate)
    (idx : Fin (2 ^ (ℓ + R_rate - i.val))) : sDomain 𝔽q β h_ℓ_add_R_rate i := by
  let basis := sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i
  let coeffs : Fin (ℓ + R_rate - i.val) → 𝔽q := finToBinaryCoeffs 𝔽q i idx
  exact basis.repr.symm ((Finsupp.equivFunOnFinite).symm coeffs)

noncomputable def sDomainFinEquiv (i : Fin r) (h_i : i < ℓ + R_rate) :
    (sDomain 𝔽q β h_ℓ_add_R_rate i) ≃ Fin (2^(ℓ + R_rate - i.val)) := by
  have h_card_eq :
      Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate i) =
        Fintype.card (Fin (2^(ℓ + R_rate - i.val))) := by
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate i h_i, hF₂.out]
    simp only [Fintype.card_fin]
  exact {
    toFun := sDomainToFin 𝔽q β h_ℓ_add_R_rate i h_i
    invFun := finToSDomain 𝔽q β h_ℓ_add_R_rate i h_i
    left_inv := fun x => by
      let basis := sDomain_basis 𝔽q β h_ℓ_add_R_rate i h_i
      let coeffs := basis.repr x
      apply (LinearEquiv.injective basis.repr)
      ext j
      simp only [finToSDomain, Basis.repr_symm_apply]
      rw [finToBinaryCoeffs_sDomainToFin]
      simp only [Finsupp.equivFunOnFinite_symm_coe, Basis.linearCombination_repr]
    right_inv := fun y => by
      apply Fin.eq_of_val_eq
      unfold sDomainToFin splitPointIntoCoeffs
      apply Nat.eq_iff_eq_all_getBits.mpr
      intro k
      rw [Nat.getBit_of_binaryFinMapToNat]
      by_cases h_k : k < ℓ + R_rate - ↑i
      · simp only [h_k, ↓reduceDIte]
        simp only [finToSDomain, Basis.repr_symm_apply, Basis.repr_linearCombination,
          Finsupp.coe_equivFunOnFinite_symm]
        simp only [finToBinaryCoeffs, ite_eq_right_iff, one_ne_zero, imp_false, ite_not]
        rw [Nat.getBit_of_lt_two_pow (k := k) (a := y)]
        simp only [h_k, ↓reduceIte]
        have h_getBit_lt_2 : k.getBit y < 2 := by
          exact Nat.getBit_lt_2
        interval_cases k.getBit y
        · simp only [zero_ne_one, ↓reduceIte]
        · simp only [↓reduceIte]
      · rw [Nat.getBit_of_lt_two_pow (k := k) (a := y)]
        simp only [h_k, ↓reduceDIte, ↓reduceIte]
  }

omit h_β₀_eq_1 in
theorem sDomainFin_bijective (i : Fin r) (h_i : i < ℓ + R_rate) :
    Function.Bijective (sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate i h_i) := by
  exact Equiv.bijective (sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate i h_i)

end DomainBijection
end IntermediateStructures
end AdditiveNTT
