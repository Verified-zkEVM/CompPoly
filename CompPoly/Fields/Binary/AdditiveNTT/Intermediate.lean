/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.Domain

/-!
# Additive NTT Intermediate Objects

Intermediate quotient-chain polynomials, intermediate novel bases, and the
intermediate evaluation polynomials used by the Additive NTT recursion.
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

section IntermediateStructures

noncomputable def intermediateNormVpoly
    (i : Fin (ℓ + 1)) (k : Fin (ℓ - i + 1)) : L[X] :=
  Fin.foldl (n := k) (fun acc j =>
    (qMap 𝔽q β ⟨(i : ℕ) + (j : ℕ), by omega⟩).comp acc) X

omit [DecidableEq L] [DecidableEq 𝔽q] hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma intermediateNormVpoly_eval_is_linear_map (i : Fin (ℓ + 1)) (k : Fin (ℓ - i + 1)) :
    IsLinearMap 𝔽q (fun x : L =>
      (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i k).eval x) := by
  induction k using Fin.induction with
  | zero =>
      unfold intermediateNormVpoly
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero]
      simp only [Polynomial.eval_X]
      exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }
  | succ k' ih =>
      unfold intermediateNormVpoly
      simp only [intermediateNormVpoly, Fin.val_castSucc] at ih
      conv =>
        enter [2, x, 2]
        simp only [Fin.val_succ]
        rw [Fin.foldl_succ_last]
      simp only [Fin.val_last, Fin.val_castSucc, eval_comp]
      set q_eval_is_linear_map := linear_map_of_comp_to_linear_map_of_eval
        (f := qMap 𝔽q β ⟨i + k', by omega⟩) (h_f_linear := qMap_is_linear_map 𝔽q β
        (i := ⟨i + k', by omega⟩))
      set innerFold := fun x : L ↦ eval x (Fin.foldl (↑k') (fun acc j ↦ (qMap 𝔽q β
        ⟨↑i + ↑j, by omega⟩).comp acc) X)
      set qmap_eval := fun x : L => (qMap 𝔽q β ⟨i + k', by omega⟩).eval x
      set isLinearMap_innerFold : IsLinearMap 𝔽q innerFold := ih
      set isLinearMap_qmap_eval : IsLinearMap 𝔽q qmap_eval := q_eval_is_linear_map
      change IsLinearMap 𝔽q fun x ↦ qmap_eval.comp innerFold x
      exact {
        map_add := fun x y => by
          dsimp only [Function.comp_apply]
          rw [isLinearMap_innerFold.map_add, isLinearMap_qmap_eval.map_add]
        map_smul := fun c x => by
          dsimp only [Function.comp_apply]
          rw [isLinearMap_innerFold.map_smul, isLinearMap_qmap_eval.map_smul]
      }

omit [DecidableEq 𝔽q] hF₂ in
theorem base_intermediateNormVpoly
    (k : Fin (ℓ + 1)) :
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨0, by
      by_contra ht
      simp only [not_lt, nonpos_iff_eq_zero] at ht
      contradiction⟩ ⟨k, by simp only [tsub_zero]; omega⟩ =
      normalizedW 𝔽q β ⟨k, by omega⟩ := by
  unfold intermediateNormVpoly
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, zero_add]
  rw [normalizedW_eq_qMap_composition 𝔽q β ℓ R_rate ⟨k, by omega⟩]
  rw [qCompositionChain_eq_foldl 𝔽q β]

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.foldl_comp (n : ℕ) (f : Fin n → L[X]) : ∀ initInner initOuter : L[X],
    Fin.foldl (n := n) (fun acc j => (f j).comp acc) (initOuter.comp initInner) =
      (Fin.foldl (n := n) (fun acc j => (f j).comp acc) initOuter).comp initInner := by
  induction n with
  | zero =>
      simp only [Fin.foldl_zero, implies_true]
  | succ n' ih =>
      intro iIn iOut
      rw [Fin.foldl_succ, Fin.foldl_succ]
      set g := fun i : Fin n' => f i.succ
      have h_left := ih g (iOut.comp iIn) (f 0)
      rw [h_left]
      have h_right := ih g iOut (f 0)
      rw [h_right]
      rw [comp_assoc]

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.comp_same_inner_eq_if_same_outer (f g : L[X]) (h_f_eq_g : f = g) :
    ∀ x, f.comp x = g.comp x := by
  intro x
  rw [h_f_eq_g]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem intermediateNormVpoly_comp_qmap (i : Fin ℓ)
    (k : Fin (ℓ - i - 1)) :
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨k + 1, by
      simp only
      omega⟩ =
      (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨k, by
        simp only
        omega⟩).comp (qMap 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediateNormVpoly
  simp only
  rw [Fin.foldl_succ]
  simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, comp_X]
  conv_lhs =>
    rw [← X_comp (p := qMap 𝔽q β ⟨↑i, by omega⟩)]
    rw [Polynomial.foldl_comp]
  congr
  funext acc j
  have h_id_eq : i.val + (j.val + 1) = i.val + 1 + j.val := by
    omega
  simp_rw [h_id_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem intermediateNormVpoly_comp (i : Fin ℓ) (k : Fin (ℓ - i + 1))
    (l : Fin (ℓ - (i.val + k.val) + 1)) :
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (k := ⟨k + l, by
      simp only
      omega⟩) =
      (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i + k, by omega⟩) (k := ⟨l, by
        simp only
        omega⟩)).comp (
          intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (k := ⟨k, by
            simp only
            omega⟩)) := by
  induction l using Fin.succRecOnSameFinType with
  | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.eta, Fin.zero_eta]
      have h_eq_X : intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i + ↑k, by omega⟩ 0 = X := by
        simp only [intermediateNormVpoly, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero]
      simp only [h_eq_X, X_comp]
  | succ j jh p =>
      unfold intermediateNormVpoly
      simp only
      have h_j_add_1_val : (j + 1).val = j.val + 1 := by
        rw [Fin.val_add_one']
        omega
      simp_rw [h_j_add_1_val]
      simp_rw [← Nat.add_assoc (n := k.val) (m := j.val) (k := 1)]
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.cast_eq_self, Fin.val_cast, Fin.val_last, Fin.val_castSucc]
      simp_rw [← Nat.add_assoc (n := i.val) (m := k.val) (k := j.val)]
      rw [comp_assoc]
      congr

noncomputable def iteratedQuotientMap (i : Fin ℓ) (k : ℕ)
    (h_bound : i.val + k ≤ ℓ) (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + k, by omega⟩ := by
  let quotient_poly := intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
    ⟨i, by omega⟩ ⟨k, by simp only; omega⟩
  let y := quotient_poly.eval (x.val : L)
  have h_x_mem : x.val ∈ sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := x.property
  have h_mem : y ∈ sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + k, by omega⟩ := by
    unfold sDomain at h_x_mem
    simp only [Submodule.mem_map] at h_x_mem
    obtain ⟨u, hu_mem, hu_eq⟩ := h_x_mem
    have h_comp_eq : quotient_poly.comp (normalizedW 𝔽q β ⟨i, by omega⟩) =
        normalizedW 𝔽q β ⟨i.val + k, by omega⟩ := by
      simp only [quotient_poly]
      rw [← base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k := ⟨i, by omega⟩)]
      rw [← base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k := ⟨i.val + k, by omega⟩)]
      have h_comp := intermediateNormVpoly_comp 𝔽q β h_ℓ_add_R_rate (i := ⟨0, by omega⟩)
        (k := ⟨i, by simp only [tsub_zero]; omega⟩) (l := ⟨k, by
          simp only [zero_add]
          omega⟩)
      simp only [Fin.zero_eta, Fin.coe_ofNat_eq_mod, Nat.sub_zero] at h_comp
      convert h_comp.symm
      omega
      omega
    unfold sDomain
    simp only [Submodule.mem_map]
    use u
    constructor
    · exact hu_mem
    · rw [eq_comm]
      calc
        y = quotient_poly.eval (x.val) := rfl
        _ = quotient_poly.eval ((normalizedW 𝔽q β ⟨i, by omega⟩).eval u) := by
              rw [← hu_eq]
              congr
        _ = (quotient_poly.comp (normalizedW 𝔽q β ⟨i, by omega⟩)).eval u := by
              rw [Polynomial.eval_comp]
        _ = (normalizedW 𝔽q β ⟨i.val + k, by omega⟩).eval u := by
              rw [h_comp_eq]
  exact ⟨y, h_mem⟩

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma qMap_eval_mem_sDomain_succ (i : Fin ℓ)
    (h_i_add_1 : i.val + 1 ≤ ℓ) (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (qMap 𝔽q β ⟨i.val, by omega⟩).eval (x.val : L) ∈ sDomain 𝔽q β h_ℓ_add_R_rate
      ⟨i.val + 1, by omega⟩ := by
  have h_x_mem := x.property
  unfold sDomain at h_x_mem
  simp only [Submodule.mem_map] at h_x_mem
  obtain ⟨u, hu_mem, hu_eq⟩ := h_x_mem
  have h_maps := qMap_maps_sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val, by omega⟩ (by
    simp only
    omega)
  have h_index : (((⟨i.val, by omega⟩ : Fin r) + 1) : Fin r) = ⟨i.val + 1, by omega⟩ := by
    refine Fin.eq_mk_iff_val_eq.mpr ?_
    rw [Fin.val_add_one' (h_a_add_1 := by simp only; omega)]
  simp only [h_index] at h_maps
  rw [← h_maps]
  simp only [polyEvalLinearMap, Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk]
  use x
  constructor
  · simp only [SetLike.coe_mem]
  · rfl

omit [DecidableEq 𝔽q] hF₂ in
theorem iteratedQuotientMap_k_eq_1_is_qMap (i : Fin ℓ)
    (h_i_add_1 : i.val + 1 ≤ ℓ) (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i 1 h_i_add_1 x =
      ⟨(qMap 𝔽q β ⟨i.val, by omega⟩).eval (x.val : L),
        qMap_eval_mem_sDomain_succ 𝔽q β h_ℓ_add_R_rate i h_i_add_1 x⟩ := by
  unfold iteratedQuotientMap
  simp only
  have h_intermediate_eq_qMap : intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨i, by omega⟩ ⟨1, by simp only; omega⟩ = qMap 𝔽q β ⟨i.val, by omega⟩ := by
    unfold intermediateNormVpoly
    simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    simp only [add_zero, comp_X]
  congr 1
  · rw [h_intermediate_eq_qMap]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma getSDomainBasisCoeff_of_sum_repr [NeZero R_rate] (i : Fin (ℓ + 1))
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (x_coeffs : Fin (ℓ + R_rate - i) → 𝔽q)
    (hx : x = ∑ j_x, (x_coeffs j_x) • (sDomain_basis 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only
        apply Nat.lt_add_of_pos_right_of_le
        omega) j_x).val) :
    ∀ (j : Fin (ℓ + R_rate - i)), ((sDomain_basis 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only
        apply Nat.lt_add_of_pos_right_of_le
        omega)).repr x) j = x_coeffs j := by
  simp only
  intro j
  set b := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (h_i := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
  have h_sum_repr : x.val = ∑ j', ((b.repr x) j') • (b j').val := by
    have hx := (b.sum_repr x).symm
    conv_lhs =>
      rw [hx]
      rw [Submodule.coe_sum]
    congr
  have h_sums_equal : ∑ j', ((b.repr x) j') • (b j').val = ∑ j_x, (x_coeffs j_x) • (b j_x).val := by
    rw [← h_sum_repr]
    exact hx
  have h_li : LinearIndependent 𝔽q (fun j' => (b j').val) := by
    simpa using (b.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
  have h_coeffs_eq : b.repr x = Finsupp.equivFunOnFinite.symm x_coeffs := by
    classical
    have h_repr_basis :
        ∀ j_x, b.repr (b j_x) = Finsupp.single j_x (1 : 𝔽q) := by
      intro j_x
      simp only [Basis.repr_self]
    have hx_at_j_simplified :
        (∑ j_x, x_coeffs j_x • (b.repr (b j_x))) j = x_coeffs j := by
      simp only [h_repr_basis, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_finset_sum,
        Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    let x_coeffs_fs := Finsupp.equivFunOnFinite.symm x_coeffs
    let rhs_sum := ∑ j_x, (x_coeffs_fs j_x) • (b j_x)
    have h_x_eq_rhs_sum : x = rhs_sum := by
      apply Subtype.ext
      have h_rhs_sum_val : rhs_sum.val = ∑ j_x, (x_coeffs_fs j_x) • (b j_x).val := by
        rw [Submodule.coe_sum]
        apply Finset.sum_congr rfl
        intro j_x _
        rw [Submodule.coe_smul]
      have hx_val_fs : x.val = ∑ j_x, (x_coeffs_fs j_x) • (b j_x).val := by
        simp only [hx]
        congr
      rw [hx_val_fs, h_rhs_sum_val]
    rw [h_x_eq_rhs_sum]
    have h_coe_eq := b.repr_sum_self x_coeffs_fs
    have h_eq : b.repr (∑ i_1, x_coeffs_fs i_1 • b i_1) = x_coeffs_fs := by
      simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.univ_sum_single]
    rw [h_eq]
  rw [h_coeffs_eq]
  rw [Finsupp.coe_equivFunOnFinite_symm]

omit [DecidableEq 𝔽q] hF₂ in
lemma getSDomainBasisCoeff_of_iteratedQuotientMap
    [NeZero R_rate] (i : Fin ℓ) (k : ℕ)
    (h_bound : i.val + k ≤ ℓ) (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    let y := iteratedQuotientMap (i := i) (k := k) (h_bound := h_bound) (x := x)
    ∀ (j : Fin (ℓ + R_rate - (i + k))),
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨↑i + k, by omega⟩) (h_i := by
        simp only
        apply Nat.lt_add_of_pos_right_of_le
        omega)).repr y) j =
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨↑i, by omega⟩)
        (h_i := by simp only; omega)).repr x) ⟨j + k, by simp only; omega⟩ := by
  simp only
  intro j
  let basis_source := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i := by simp only; omega)
  let basis_target := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val + k, by omega⟩) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  let x_coeffs := basis_source.repr x
  set y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i k h_bound x
  let y_coeffs := basis_target.repr y
  have hx_sum : x.val = ∑ j_x, (x_coeffs j_x) • (basis_source j_x).val := by
    simp only [x_coeffs]
    conv_lhs => rw [← basis_source.sum_repr x]; rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul]
  have hy_sum : y.val = ∑ j_y, (y_coeffs j_y) • (basis_target j_y).val := by
    simp only [y_coeffs]
    conv_lhs => rw [← basis_target.sum_repr y]; rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul]
  have hy_sum_from_x : y = ∑ j_x, (x_coeffs j_x) •
      ((intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
        ⟨k, by simp only; omega⟩).eval (basis_source j_x).val) := by
    have hy_eval : y.val = (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨i, by omega⟩ ⟨k, by simp only; omega⟩).eval x.val := by
      rfl
    rw [hx_sum] at hy_eval
    simp only at hy_eval
    rw [hy_eval]
    have h_res :
        eval (∑ x : Fin (ℓ + R_rate - i), x_coeffs x • (basis_source x).val)
          (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨k, by simp only; omega⟩) =
          ∑ j_x : Fin (ℓ + R_rate - i), x_coeffs j_x • eval ((basis_source j_x).val)
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨k, by simp only; omega⟩) := by
      have eval_interW_IsLinearMap :
          IsLinearMap 𝔽q (fun x : L =>
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
              ⟨i, by omega⟩ ⟨k, by simp only; omega⟩).eval x) := by
        exact intermediateNormVpoly_eval_is_linear_map 𝔽q β h_ℓ_add_R_rate
          (i := ⟨i, by omega⟩) (k := ⟨k, by simp only; omega⟩)
      let eval_interW_LinearMap := polyEvalLinearMap (intermediateNormVpoly 𝔽q β
        h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨k, by simp only; omega⟩) eval_interW_IsLinearMap
      change eval_interW_LinearMap (∑ x_1 : Fin (ℓ + R_rate - i),
        x_coeffs x_1 • (basis_source x_1).val) = _
      rw [map_sum (g := eval_interW_LinearMap) (s := (Finset.univ : Finset (Fin (ℓ + R_rate - i))))]
      simp_rw [eval_interW_LinearMap.map_smul]
      rfl
    rw [h_res]
  have h_eval_basis_i :
      ∀ j_x, (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (k := ⟨k, by simp only; omega⟩)).eval (basis_source j_x).val =
        (normalizedW 𝔽q β ⟨i.val + k, by omega⟩).eval (β ⟨i.val + j_x.val, by
          simp only
          omega⟩) := by
    intro j_x
    let interW_i_k := intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by
      omega⟩) (k := ⟨k, by simp only; omega⟩)
    let W_i := normalizedW 𝔽q β ⟨i, by omega⟩
    let W_i_add_k := normalizedW 𝔽q β ⟨i.val + k, by omega⟩
    have h_comp_eq : interW_i_k.comp W_i = W_i_add_k := by
      have hi := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k := ⟨i, by omega⟩)
      have hi_add_k := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k := ⟨i.val + k, by omega⟩)
      simp at hi hi_add_k
      simp_rw [W_i, W_i_add_k, interW_i_k, ← hi, ← hi_add_k]
      have h_interW_comp := intermediateNormVpoly_comp 𝔽q β h_ℓ_add_R_rate
        (i := ⟨0, by omega⟩) (k := ⟨i, by simp only [tsub_zero, Fin.is_le',
          Nat.lt_add_of_pos_right_of_le]⟩) (l := ⟨k, by
          simp only [zero_add]
          omega⟩)
      simp only [Fin.zero_eta, Fin.coe_ofNat_eq_mod, Nat.sub_zero] at h_interW_comp
      rw [h_interW_comp]
      have h_index : 0 + i.val = i.val := by omega
      rw! (castMode := .all) [h_index]
      rfl
    rw [get_sDomain_basis, ← Polynomial.eval_comp, h_comp_eq]
  simp_rw [h_eval_basis_i] at hy_sum_from_x
  let final_y_coeffs : Fin (ℓ + R_rate - (i + k)) → 𝔽q :=
    fun j_x : Fin (ℓ + R_rate - (i + k)) => x_coeffs ⟨j_x + k, by simp only; omega⟩
  have final_hy_sum : y = ∑ j_x : Fin (ℓ + R_rate - (i + k)),
      (final_y_coeffs j_x) • (basis_target j_x).val := by
    rw [hy_sum_from_x]
    let a := k
    let b := ℓ + R_rate - (↑i + k)
    have h_index_add : ℓ + R_rate - ↑i = a + b := by
      omega
    rw! (castMode := .all) [h_index_add]
    conv_lhs =>
      rw [Fin.sum_univ_add]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
    have hβ : ∀ x : Fin a, β ⟨↑i + x, by omega⟩ ∈ U 𝔽q β (i := ⟨i + k, by omega⟩) := by
      intro x
      apply β_lt_mem_U 𝔽q β (i := ⟨↑i + k, by omega⟩) (j := ⟨i.val + x, by simp only; omega⟩)
    have h_eval_W_at_β : ∀ x : Fin a, eval (β ⟨↑i + ↑x, by omega⟩)
        (normalizedW 𝔽q β ⟨↑i + k, by omega⟩) = 0 := by
      intro x
      rw [normalizedWᵢ_vanishing 𝔽q β ⟨↑i + k, by omega⟩]
      exact hβ x
    simp only [h_eval_W_at_β, smul_zero, Finset.sum_const_zero, zero_add]
    congr
    simp only [b]
    funext j2
    rw [get_sDomain_basis]
    have h : i + k < r := by omega
    have h2 : i.val + (a + ↑j2) = i + k + j2 := by omega
    rw! (castMode := .all) [Fin.val_mk (n := r) (m := i.val + k)]
    rw! (castMode := .all) [h2]
    have h3 : (Fin.natAdd a j2) = ⟨↑j2 + k, by omega⟩ := by
      simp only [Fin.natAdd, Fin.mk.injEq, a]
      rw [add_comm]
    congr 1
    simp only [final_y_coeffs]
    rw [h3]
    rw! (castMode := .all) [← h_index_add]
    simp
  rw [getSDomainBasisCoeff_of_sum_repr 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val, by omega⟩) (x := x) (hx := by exact hx_sum)]
  rw [getSDomainBasisCoeff_of_sum_repr 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i + k, by omega⟩) (x := y) (x_coeffs := final_y_coeffs) (hx := final_hy_sum)]

noncomputable def sDomain.lift (i j : Fin r) (h_j : j < ℓ + R_rate) (h_le : i ≤ j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate j) :
    sDomain 𝔽q β h_ℓ_add_R_rate i := by
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := j) (h_i := by exact h_j)
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
  let ϑ := j.val - i.val
  let x_coeffs : Fin (ℓ + R_rate - i) → 𝔽q := fun k =>
    if hk : k.val < ϑ then 0
    else basis_y.repr y ⟨k.val - ϑ, by omega⟩
  exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
theorem basis_repr_of_sDomain_lift (i j : Fin r) (h_j : j < ℓ + R_rate) (h_le : i ≤ j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := j)) :
    let x₀ := sDomain.lift 𝔽q β h_ℓ_add_R_rate i j (by omega) (by omega) y
    ∀ k : Fin (ℓ + R_rate - i),
      (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)).repr x₀ k =
        if hk : k < (j.val - i.val) then 0
        else (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := j)
          (h_i := by omega)).repr y ⟨k - (j.val - i.val), by omega⟩ := by
  simp only
  intro k
  simp only [sDomain.lift, Basis.repr_symm_apply, Basis.repr_linearCombination]
  rw [Finsupp.coe_equivFunOnFinite_symm]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem intermediateNormVpoly_comp_qmap_helper (i : Fin ℓ)
    (k : Fin (ℓ - (↑i + 1))) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨↑i + 1, by omega⟩ (k := ⟨k, by simp only; omega⟩)).comp (qMap 𝔽q β ⟨↑i, by omega⟩) =
      intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
        ⟨↑i, by omega⟩ ⟨k + 1, by simp only; omega⟩ := by
  simp only [intermediateNormVpoly_comp_qmap 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ k]

noncomputable def intermediateNovelBasisX (i : Fin (ℓ + 1)) (j : Fin (2 ^ (ℓ - i))) : L[X] :=
  (Finset.univ : Finset (Fin (ℓ - i))).prod (fun k =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := ⟨k, by omega⟩)) ^ (Nat.getBit k j))

omit [DecidableEq 𝔽q] hF₂ in
theorem base_intermediateNovelBasisX (j : Fin (2 ^ ℓ)) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨0, by
      by_contra ht
      simp only [not_lt, nonpos_iff_eq_zero] at ht
      contradiction⟩ j =
      Xⱼ 𝔽q β ℓ (by omega) j := by
  unfold intermediateNovelBasisX Xⱼ
  simp only [Fin.mk_zero', Fin.val_zero, Nat.sub_zero]
  have h_res := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
  simp only [Fin.mk_zero'] at h_res
  conv_lhs =>
    enter [2, x, 1]
    rw [h_res ⟨x, by omega⟩]
  congr

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma intermediateNovelBasisX_zero_eq_one (i : Fin (ℓ + 1)) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i ⟨0, by
      exact Nat.two_pow_pos (ℓ - ↑i)⟩ = 1 := by
  unfold intermediateNovelBasisX
  simp only [Nat.getBit_zero_eq_zero, pow_zero]
  exact Finset.prod_const_one

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma even_index_intermediate_novel_basis_decomposition (i : Fin ℓ) (j : Fin (2 ^ (ℓ - i - 1))) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨j * 2, by
      apply mul_two_add_bit_lt_two_pow j (ℓ - i - 1) (ℓ - i) ⟨0, by omega⟩ (by omega) (by omega)⟩ =
      (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
        apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ - i - 1) (ℓ - (i + 1)) (by omega) (by omega)⟩).comp
        (qMap 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  simp only [pow_comp]
  conv_rhs =>
    enter [2, x]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q]
  set fleft := fun x : Fin (ℓ - ↑i) =>
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩
      ⟨x, by simp only; omega⟩ ^ Nat.getBit (↑x) (↑j * 2)
  have h_n_shift : ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift : Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
    Fin.prod_univ_succ (M := L[X]) (n := ℓ - (↑i + 1)) (f := fun x => fleft ⟨x, by omega⟩)
  have h_lhs_prod_eq : ∏ x : Fin (ℓ - ↑i), fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)
  rw [← h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]
  have fleft_0_eq_0 : fleft ⟨(0 : Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = 1 := by
    unfold fleft
    simp only
    have h_exp : Nat.getBit (0 : Fin (ℓ - (↑i + 1) + 1)) (↑j * 2) = 0 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      have res := Nat.getBit_zero_of_two_mul (n := j.val)
      rw [mul_comm] at res
      exact res
    rw [h_exp]
    simp only [pow_zero]
  rw [fleft_0_eq_0, one_mul]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq : Nat.getBit (↑x + 1) (↑j * 2) = Nat.getBit ↑x ↑j := by
    have h_num_eq : j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two (k := ↑x) (n := ↑j)
  rw [h_exp_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma odd_index_intermediate_novel_basis_decomposition
    (i : Fin ℓ) (j : Fin (2 ^ (ℓ - i - 1))) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨j * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow j (ℓ - i - 1) (ℓ - i) ⟨1, by omega⟩ (by omega) (by omega)⟩ =
      X * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
        apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ - i - 1) (ℓ - (i + 1)) (by omega) (by omega)⟩).comp
        (qMap 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  simp only [pow_comp]
  conv_rhs =>
    enter [2]
    enter [2, x, 1]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q β h_ℓ_add_R_rate
      ⟨i, by omega⟩ ⟨x, by simp only; omega⟩]
  set fleft := fun x : Fin (ℓ - ↑i) =>
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩
      ⟨x, by simp only; omega⟩ ^ Nat.getBit (↑x) (↑j * 2 + 1)
  have h_n_shift : ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift : Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
    Fin.prod_univ_succ (M := L[X]) (n := ℓ - (↑i + 1)) (f := fun x => fleft ⟨x, by omega⟩)
  have h_lhs_prod_eq : ∏ x : Fin (ℓ - ↑i), fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)
  rw [← h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]
  have fleft_0_eq_X : fleft ⟨(0 : Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = X := by
    unfold fleft
    simp only
    have h_exp : Nat.getBit (0 : Fin (ℓ - (↑i + 1) + 1)) (↑j * 2 + 1) = 1 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      unfold Nat.getBit
      simp only [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_add_mod_self_right, Nat.mod_succ]
    rw [h_exp]
    simp only [pow_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero]
  rw [fleft_0_eq_X]
  congr
  funext x
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq : Nat.getBit (↑x + 1) (↑j * 2 + 1) = Nat.getBit ↑x ↑j := by
    have h_num_eq : j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two_add_one (k := ↑x) (n := ↑j)
  rw [h_exp_eq]

noncomputable def intermediateEvaluationPoly (i : Fin (ℓ + 1))
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩ : Fin (2^(ℓ-i))), C (coeffs ⟨j, by omega⟩) *
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i ⟨j, by omega⟩)

noncomputable def evenRefinement (i : Fin ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩ : Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩) *
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, hj⟩)

noncomputable def oddRefinement (i : Fin ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩ : Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2+1, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩) *
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, hj⟩)

omit [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem evaluation_poly_split_identity (i : Fin ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
    let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs
    let P_even_i_plus_1 : L[X] := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
    let P_odd_i_plus_1 : L[X] := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
    let q_i : L[X] := qMap 𝔽q β ⟨i, by omega⟩
    P_i = (P_even_i_plus_1.comp q_i) + X * (P_odd_i_plus_1.comp q_i) := by
  simp only [intermediateEvaluationPoly, Fin.eta]
  simp only [evenRefinement, Fin.eta, sum_comp, mul_comp, C_comp, oddRefinement]
  set leftEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ - i - 1) (ℓ - i) ⟨0, by omega⟩ (by omega) (by omega)⟩) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j * 2, by
        exact mul_two_add_bit_lt_two_pow j (ℓ - i - 1) (ℓ - i) ⟨0, by omega⟩ (by omega) (by omega)⟩
  set leftOddTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow j (ℓ - i - 1) (ℓ - i) ⟨1, by omega⟩ (by omega) (by omega)⟩) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j * 2 + 1, by
        exact mul_two_add_bit_lt_two_pow j (ℓ - i - 1) (ℓ - i) ⟨1, by omega⟩ (by omega) (by omega)⟩
  have h_split_P_i : ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i)), C (coeffs ⟨j, by
      apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ - i) (ℓ - i) (by omega) (by omega)⟩) *
      intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j, by omega⟩ =
      leftEvenTerm + leftOddTerm := by
    unfold leftEvenTerm leftOddTerm
    simp only [Fin.eta]
    set f1 := fun x : ℕ =>
      if hx : x < 2 ^ (ℓ - ↑i) then
        C (coeffs ⟨x, hx⟩) *
          intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x, by omega⟩
      else 0
    have h_x : ∀ x : Fin (2 ^ (ℓ - ↑i)), f1 x.val =
        C (coeffs ⟨x.val, by omega⟩) *
          intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩
            ⟨x.val, by simp only; omega⟩ := by
      intro x
      unfold f1
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    conv_lhs =>
      enter [2, x]
      rw [← h_x x]
    have h_x_2 : ∀ x : Fin (2 ^ (ℓ - ↑i - 1)), f1 (x * 2) =
        C (coeffs ⟨x.val * 2, by
          calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
            _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩) *
          intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val * 2, by
            exact mul_two_add_bit_lt_two_pow x.val (ℓ - i - 1) (ℓ - i) ⟨0, by omega⟩ (by omega) (by omega)⟩ := by
      intro x
      unfold f1
      simp only
      have h_x_lt_2_pow_i_minus_1 :=
        mul_two_add_bit_lt_two_pow x.val (ℓ - i - 1) (ℓ - i) ⟨0, by omega⟩ (by omega) (by omega)
      simp at h_x_lt_2_pow_i_minus_1
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]
    conv_rhs =>
      enter [1, 2, x]
      rw [← h_x_2 x]
    have h_x_3 : ∀ x : Fin (2 ^ (ℓ - ↑i - 1)), f1 (x * 2 + 1) =
        C (coeffs ⟨x.val * 2 + 1, by
          calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
            _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩) *
          intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val * 2 + 1, by
            exact mul_two_add_bit_lt_two_pow x.val (ℓ - i - 1) (ℓ - i) ⟨1, by omega⟩ (by omega) (by omega)⟩ := by
      intro x
      unfold f1
      simp only
      have h_x_lt_2_pow_i_minus_1 := mul_two_add_bit_lt_two_pow x.val
        (ℓ - i - 1) (ℓ - i) ⟨1, by omega⟩ (by omega) (by omega)
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]
    conv_rhs =>
      enter [2, 2, x]
      rw [← h_x_3 x]
    have h_1 : ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i)), f1 i =
        ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i - 1 + 1)), f1 i := by
      congr
      omega
    have res := Fin.sum_univ_odd_even (f := f1) (n := (ℓ - ↑i - 1))
    conv_rhs at res =>
      rw [Fin.sum_univ_eq_sum_range]
      rw [← h_1]
      rw [← Fin.sum_univ_eq_sum_range]
    rw [← res]
    congr
    · funext i
      rw [mul_comm]
    · funext i
      rw [mul_comm]
  conv_lhs => rw [h_split_P_i]
  set rightEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
      C (coeffs ⟨j * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩) *
        (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
          apply lt_two_pow_of_lt_two_pow_exp_le (x := j)
            (i := ℓ - ↑i - 1) (j := ℓ - ↑i - 1) (by omega) (by omega)⟩).comp
          (qMap 𝔽q β ⟨i, by omega⟩)
  set rightOddTerm := X *
    ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
      C (coeffs ⟨j * 2 + 1, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩) *
        (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
          apply lt_two_pow_of_lt_two_pow_exp_le (x := j)
            (i := ℓ - ↑i - 1) (j := ℓ - ↑i - 1) (by omega) (by omega)⟩).comp
          (qMap 𝔽q β ⟨i, by omega⟩)
  conv_rhs => change rightEvenTerm + rightOddTerm
  have h_right_even_term : leftEvenTerm = rightEvenTerm := by
    unfold rightEvenTerm leftEvenTerm
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.eta, mul_eq_mul_left_iff, map_eq_zero]
    by_cases h_a_j_eq_0 : coeffs ⟨j * 2, by
      calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
        _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w := ℓ - i) (h := by omega)⟩ = 0
    · simp only [h_a_j_eq_0, or_true]
    · simp only [h_a_j_eq_0, or_false]
      exact even_index_intermediate_novel_basis_decomposition
        𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) j
  have h_right_odd_term : rightOddTerm = leftOddTerm := by
    unfold rightOddTerm leftOddTerm
    simp only [Fin.eta]
    conv_rhs =>
      simp only [Fin.is_lt, odd_index_intermediate_novel_basis_decomposition, Fin.eta]
      enter [2, x]
      rw [mul_comm (a := X)]
    rw [Finset.mul_sum]
    congr
    funext x
    ring_nf
  rw [h_right_even_term, h_right_odd_term]

omit [DecidableEq 𝔽q] hF₂ in
lemma intermediate_poly_P_base (h_ℓ : ℓ ≤ r) (coeffs : Fin (2 ^ ℓ) → L) :
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ coeffs =
      polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ coeffs := by
  unfold polynomialFromNovelCoeffs intermediateEvaluationPoly
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, Fin.eta]
  conv_rhs =>
    enter [2, j]
    rw [← base_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate j]
  congr

end IntermediateStructures
end AdditiveNTT
