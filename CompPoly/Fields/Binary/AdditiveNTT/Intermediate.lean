/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Domain
public import Mathlib.Algebra.BigOperators.WithTop

/-!
# Additive NTT Intermediate Objects

Intermediate quotient-chain polynomials, intermediate novel bases, and the
intermediate evaluation polynomials used by the Additive NTT recursion.
-/

@[expose] public section

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

private theorem sum_univ_odd_even {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ x : Fin (2 ^ (n + 1)), f x =
      ∑ x : Fin (2 ^ n), f (2 * x) + ∑ x : Fin (2 ^ n), f (2 * x + 1) := by
  rw [_root_.Fin.sum_univ_eq_sum_range (f := f), _root_.Fin.sum_univ_eq_sum_range
    (f := fun x => f (2 * x)), _root_.Fin.sum_univ_eq_sum_range
    (f := fun x => f (2 * x + 1))]
  rw [pow_succ]
  induction (2 ^ n) with
  | zero => simp
  | succ m ih =>
    rw [show (m + 1) * 2 = m * 2 + 1 + 1 from by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ (f := fun x => f (2 * x)),
      Finset.sum_range_succ (f := fun x => f (2 * x + 1))]
    simp only [mul_comm 2]
    abel
/-! ### 2. Intermediate Novel Polynomial Bases `Xⱼ⁽ⁱ⁾`  and evaluation polynomials `P⁽ⁱ⁾`-/

/-- The `k`-step subspace-vanishing polynomial `Ŵₖ⁽ⁱ⁾`.

`i : Fin r` is a loose index and `h_k : i + k ≤ ℓ` supplies its NTT-level bound.
For `k = 0` this is `X`; otherwise it is `q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾`.
-/
noncomputable def intermediateNormVpoly
    (i: Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) : L[X] :=
  Fin.foldl (n:=k) (fun acc j =>
    (qMap 𝔽q β ⟨(i : ℕ) + (j : ℕ), by omega⟩
      (by change i.val + j.val + 1 < r; omega)).comp acc) (X)

omit [DecidableEq L] [DecidableEq 𝔽q] hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma intermediateNormVpoly_eval_is_linear_map (i : Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) :
    IsLinearMap 𝔽q (fun x : L =>
      (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i h_k).eval x) := by
  -- We proceed by induction on k, the number of compositions.
  -- induction k using Fin.induction with
  induction k with
  | zero => -- For k=0, the polynomial is just `X`.
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero]
    -- The evaluation map `fun x => X.eval x` is just the identity function `id`.
    simp only [Polynomial.eval_X]
    exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }
  | succ k' ih =>
    unfold intermediateNormVpoly
    simp only [intermediateNormVpoly] at ih
    conv =>
      enter [2, x, 2];
      simp only [Fin.val_succ]
      rw [Fin.foldl_succ_last]
    simp only [Fin.val_last, Fin.val_castSucc, eval_comp]
    set q_eval_is_linear_map := linear_map_of_comp_to_linear_map_of_eval
      (f:=qMap 𝔽q β ⟨i + k', by omega⟩ (by change i.val + k' + 1 < r; omega))
      (h_f_linear := qMap_is_linear_map 𝔽q β
      (i := ⟨i + k', by omega⟩) (by change i.val + k' + 1 < r; omega))
    set innerFold := fun x: L ↦ eval x (Fin.foldl (↑k') (fun acc j ↦ (qMap 𝔽q β
      ⟨↑i + ↑j, by omega⟩ (by change i.val + j.val + 1 < r; omega)).comp acc) X)
    set qmap_eval := fun x : L =>
      (qMap 𝔽q β ⟨i + k', by omega⟩ (by change i.val + k' + 1 < r; omega)).eval x
    set isLinearMap_innerFold : IsLinearMap 𝔽q innerFold := ih (h_k := by omega)
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

omit [DecidableEq 𝔽q] [DecidableEq L] hF₂ in
-- Ŵₖ⁽⁰⁾(X) = Ŵ(X)
theorem base_intermediateNormVpoly
    (k : Fin r) (h_k : k.val ≤ ℓ) :
  intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate 0 (k := k)
    (h_k := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega) =
  normalizedW 𝔽q β k := by
  classical
  unfold intermediateNormVpoly
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]
  rw [normalizedW_eq_qMap_composition 𝔽q β ℓ R_rate k]
  rw [qCompositionChain_eq_foldl 𝔽q β]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The natDegree of `Ŵₖ⁽ⁱ⁾(X)` is `2^k`. -/
lemma natDegree_intermediateNormVpoly (i : Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := k) (h_k := h_k)).natDegree = 2 ^ k := by
  induction k with
  | zero =>
    -- Base Case: X
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero, natDegree_X, pow_zero]
  | succ k' ih =>
    -- Inductive Step
    unfold intermediateNormVpoly
    -- simp only [Fin.val_succ]
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last, Fin.val_castSucc]
    -- 1. Apply natDegree_comp
    rw [Polynomial.natDegree_comp]
    -- 2. Handle qMap part
    rw [natDegree_qMap]
    -- 3. Handle Accumulator part (use IH)
    -- We match the accumulator definition to the IH term
    have h_acc_eq_prev :
      Fin.foldl (↑k') (fun acc j ↦
        (qMap 𝔽q β ⟨↑i + ↑j, by omega⟩ (by change i.val + j.val + 1 < r; omega)).comp acc) X
      = intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := k') (h_k := by omega) := rfl
    unfold intermediateNormVpoly at ih
    let ih_prev := ih (h_k := by omega)
    rw [h_acc_eq_prev] at ih_prev ⊢
    rw [ih_prev]
    -- 4. Arithmetic: 2 * 2^k' = 2^(k'+1)
    rw [pow_succ']

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The degree of `Ŵₖ⁽ⁱ⁾(X)` is `2^k`. -/
lemma degree_intermediateNormVpoly (i : Fin r) {k : ℕ} (h_k : i.val + k ≤ ℓ) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k := k) (h_k := h_k)).degree = 2 ^ k := by
  rw [Polynomial.degree_eq_natDegree]
  · rw [natDegree_intermediateNormVpoly]; norm_cast
  · apply Polynomial.ne_zero_of_natDegree_gt (n := 0);
    rw [natDegree_intermediateNormVpoly]; simp only [Nat.ofNat_pos, pow_pos]

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.foldl_comp (n : ℕ) (f : Fin n → L[X]) : ∀ initInner initOuter: L[X],
    Fin.foldl (n:=n) (fun acc j => (f j).comp acc) (initOuter.comp initInner)
    = (Fin.foldl (n:=n) (fun acc j => (f j).comp acc) (initOuter)).comp initInner := by
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

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- If `i < ℓ` and `i + k + 1 ≤ ℓ`, then
`Ŵₖ₊₁⁽ⁱ⁾ = Ŵₖ⁽ⁱ⁺¹⁾ ∘ q⁽ⁱ⁾`. -/
theorem intermediateNormVpoly_comp_qmap (i : Fin r)
    {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (k : ℕ) (h_k : i.val + k + 1 ≤ ℓ) :
    -- corresponds to intermediateNormVpoly_comp where `k = k, l = 1`
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k + 1) (h_k := by omega)=
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (k := k) (h_k := by omega)).comp
        (qMap 𝔽q β i (by omega)) := by
  unfold intermediateNormVpoly
  -- simp only -- Fin.foldl (↑k+1) ... = Fin.foldl (↑k+1) ...
  rw [Fin.foldl_succ] -- convert Fin.foldl (↑k+1) ... into (Fin.foldl (↑k) ...).comp (init value)
  simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, comp_X]
  conv_lhs =>
    rw [←X_comp (p:=qMap 𝔽q β ⟨↑i, by omega⟩ (by change i.val + 1 < r; omega))]
    rw [Polynomial.foldl_comp]
  congr -- convert Fin.foldl equality into equality of accumulator functions
  -- ⊢ (fun acc j ↦ (qMap 𝔽q β ⟨↑i + (↑j + 1), ⋯⟩).comp acc)
  -- = fun acc j ↦ (qMap 𝔽q β ⟨↑(i + 1) + ↑j, ⋯⟩).comp acc
  funext acc j
  have h_id_eq: i.val + (j.val + 1) = i.val + 1 + j.val := by omega
  simp_rw [h_id_eq]
  simp only [h_destIdx]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
theorem intermediateNormVpoly_comp (i : Fin r) {destIdx : Fin r}
    {k l : ℕ} (h_destIdx : destIdx = i.val + k)
  (h_k : i.val + k ≤ ℓ) (h_l : i.val + k + l ≤ ℓ) :
  intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k:=k + l) (h_k := by omega) =
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (k:=l) (h_k := by omega)).comp (
  intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k:=k) (h_k := by omega)) := by
    -- (l : Fin (ℓ - (i.val + k.val) + 1)) :
  induction l with
  | zero =>
    simp only [add_zero]
    have h_eq_X : intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := destIdx)
      (k := 0) (h_k := by omega) = X := by
      simp only [intermediateNormVpoly, Fin.foldl_zero]
    simp only [h_eq_X, X_comp]
  | succ j ih =>
      -- Inductive case: l = j + 1
      -- Following the pattern from concreteTowerAlgebraMap_assoc:
      -- A = |i| --- (k) --- |i+k| --- (j+1) --- |i+k+j+1|
      -- Proof: A = (j+1) ∘ (k) (direct) = ((1) ∘ (j)) ∘ (k) (succ decomposition)
      --        = (1) ∘ ((j) ∘ (k)) (associativity) = (1) ∘ (jk) (induction hypothesis)
      have h_left := ih (h_l := by omega)
      unfold intermediateNormVpoly at ⊢ h_left
      conv_lhs =>
        simp only [←Nat.add_assoc (n:=k) (m:=j) (k:=1)]
        simp only [Fin.cast_eq_self]
        rw [Fin.foldl_succ_last] -- split the outer comp
        simp only [Fin.val_last, Fin.val_castSucc]
        rw [h_left]
        simp only [←Nat.add_assoc (n:=i.val) (m:=k) (k:=j)]
        simp only [h_destIdx]
      conv_rhs =>
        rw [Fin.foldl_succ_last] -- split the outer comp
        simp only [Fin.val_last, Fin.val_castSucc]
        simp only [h_destIdx]
      rw [Polynomial.comp_assoc]

/-- Maps a point from `sDomain i` to `sDomain destIdx` by a `k`-step quotient map.

`i` and `destIdx` are loose `Fin r` indices. `h_destIdx` identifies the destination
as `i + k`, and `h_destIdx_le` supplies the NTT-level bound. -/
noncomputable def iteratedQuotientMap (i : Fin r) {destIdx : Fin r} {k : ℕ}
    (h_destIdx : destIdx = i.val + k) (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx := by
  let quotient_poly := intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega)
  let y := quotient_poly.eval (x.val : L)
  have h_x_mem : x.val ∈ sDomain 𝔽q β h_ℓ_add_R_rate i := x.property
  have h_mem : y ∈ sDomain 𝔽q β h_ℓ_add_R_rate destIdx := by
    unfold sDomain at h_x_mem
    simp only [Submodule.mem_map] at h_x_mem
    obtain ⟨u, hu_mem, hu_eq⟩ := h_x_mem
    have h_comp_eq : quotient_poly.comp (normalizedW 𝔽q β i)
      = normalizedW 𝔽q β destIdx := by
      simp only [quotient_poly]
      rw [←base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=i)]
      · rw [←base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=destIdx)]
        · have h_comp := intermediateNormVpoly_comp 𝔽q β h_ℓ_add_R_rate (i := 0)
            (k:=i) (l:=k) (destIdx := i) (h_destIdx := by
              simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]) (h_k := by
                simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega) (h_l := by
                simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
          convert h_comp.symm
        · omega
      · omega
    -- Now we can show membership
    unfold sDomain
    simp only [Submodule.mem_map]
    use u
    constructor
    · exact hu_mem
    · -- ⊢ (polyEvalLinearMap (normalizedW 𝔽q β ⟨↑i + k, ⋯⟩) ⋯) u = y
      rw [eq_comm]
      calc y = quotient_poly.eval (x.val) := rfl
        _ = quotient_poly.eval ((normalizedW 𝔽q β i).eval u) := by
          rw [← hu_eq]; congr
        _ = (quotient_poly.comp (normalizedW 𝔽q β i)).eval u := by
          rw [Polynomial.eval_comp]
        _ = (normalizedW 𝔽q β destIdx).eval u := by rw [h_comp_eq]
  exact ⟨y, h_mem⟩

/-- At the terminal index, the zero-step quotient map is the identity. -/
example (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨ℓ, by omega⟩) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨ℓ, by omega⟩) (destIdx := ⟨ℓ, by omega⟩) (k := 0)
      (h_destIdx := by rfl) (h_destIdx_le := by rfl) x = x := by
  apply Subtype.ext
  simp only [iteratedQuotientMap, intermediateNormVpoly, Fin.foldl_zero, Polynomial.eval_X]

omit [DecidableEq 𝔽q] hF₂ in
lemma iteratedQuotientMap_congr_k
    (i : Fin r) {destIdx : Fin r} {k₁ k₂ : ℕ}
    (hk : k₁ = k₂)
    (h_destIdx₁ : destIdx.val = i.val + k₁)
    (h_destIdx₂ : destIdx.val = i.val + k₂)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := k₁) (h_destIdx := h_destIdx₁) (h_destIdx_le := h_destIdx_le) x
    =
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := k₂) (h_destIdx := h_destIdx₂) (h_destIdx_le := h_destIdx_le) x := by
  subst hk; rfl

omit [DecidableEq 𝔽q] hF₂ in
/-- Composing one quotient step with a `steps`-step quotient map equals the
`steps + 1` step quotient map. -/
theorem iteratedQuotientMap_succ_comp
    (i : Fin r) {midIdx destIdx : Fin r} (steps : ℕ)
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate i) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := steps + 1) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) x
    =
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := midIdx) (k := steps)
      (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le)
      (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := i) (k := 1) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) x) := by
  apply Subtype.ext
  simp only [iteratedQuotientMap]
  have h_poly_comp := intermediateNormVpoly_comp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (destIdx := midIdx) (k := 1) (l := steps)
    (h_destIdx := by simpa using h_midIdx) (h_k := by omega) (h_l := by omega)
  have h_poly_comp' :
      intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps + 1) (h_k := by omega) =
        (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := midIdx) (k := steps)
          (h_k := by omega)).comp
        (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := 1) (h_k := by omega)) := by
    simpa [Nat.add_comm] using h_poly_comp
  rw [h_poly_comp']
  simp only [Polynomial.eval_comp]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- The evaluation of qMap on an element from sDomain i belongs to sDomain (i+1).
This is a key property that qMap maps between successive domains. -/
lemma qMap_eval_mem_sDomain_succ (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    (qMap 𝔽q β i (by omega)).eval (x.val : L) ∈
      sDomain 𝔽q β h_ℓ_add_R_rate destIdx := by
  have h_x_mem := x.property
  unfold sDomain at h_x_mem
  simp only [Submodule.mem_map] at h_x_mem
  obtain ⟨u, hu_mem, hu_eq⟩ := h_x_mem
  -- Use the fact that qMap maps sDomain i to sDomain (i+1)
  have h_maps := qMap_maps_sDomain 𝔽q β h_ℓ_add_R_rate i (by omega)
  rw! [h_destIdx.symm] at h_maps
  rw [←h_maps]
  simp only [polyEvalLinearMap, Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk]
  use x
  constructor
  · simp only [SetLike.coe_mem] -- x ∈ sDomain i
  · rfl

omit [DecidableEq 𝔽q] hF₂ in
/-- When k = 1, iteratedQuotientMap reduces to evaluating qMap directly.
This shows that iteratedQuotientMap with k = 1 is equivalent to the single-step quotient map. -/
theorem iteratedQuotientMap_k_eq_1_is_qMap (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := 1) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) x : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    = ⟨(qMap 𝔽q β i (by omega)).eval (x.val : L),
      qMap_eval_mem_sDomain_succ 𝔽q β h_ℓ_add_R_rate i h_destIdx x⟩ := by
  unfold iteratedQuotientMap
  simp only
  have h_intermediate_eq_qMap : intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := 1) (h_k := by omega) = qMap 𝔽q β i (by omega) := by
    unfold intermediateNormVpoly
    simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    simp only [add_zero, comp_X]
  -- We need to show that the two expressions are equal
  -- The first component is the evaluation, which we can rewrite
  congr 1
  · rw [h_intermediate_eq_qMap]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
lemma getSDomainBasisCoeff_of_sum_repr [NeZero R_rate] (i : Fin r) (h_i : i ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (x_coeffs : Fin (ℓ + R_rate - i) → 𝔽q)
    (hx : x = ∑ j_x, (x_coeffs j_x) • (sDomain_basis 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only; apply Nat.lt_add_of_pos_right_of_le; omega) j_x).val) :
    ∀ (j: Fin (ℓ + R_rate - i)), ((sDomain_basis 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only; apply Nat.lt_add_of_pos_right_of_le; omega)).repr x) j = x_coeffs j := by
  simp only
  intro j
  set b := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (h_i := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
  -- By definition of a basis, `x` can also be written as a sum using its `repr` coefficients.
  have h_sum_repr : x.val = ∑ j', ((b.repr x) j') • (b j').val := by
    have hx := (b.sum_repr x).symm
    conv_lhs =>
      rw [hx]; rw [Submodule.coe_sum] -- move the Subtype.val embedding into the function body
    congr
  have h_sums_equal : ∑ j', ((b.repr x) j') • (b j').val = ∑ j_x, (x_coeffs j_x) • (b j_x).val := by
    rw [←h_sum_repr]
    exact hx
  -- The basis vectors `.val` are linearly independent in the ambient space `L`.
  have h_li : LinearIndependent 𝔽q (fun j' => (b j').val) := by
    change LinearIndependent 𝔽q (Subtype.val ∘ b)
    exact b.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
  -- Since the basis vectors are linearly independent, the representation of `x.val` as a
  -- linear combination is unique. Therefore, the coefficients must be equal.
  have h_coeffs_eq : b.repr x = Finsupp.equivFunOnFinite.symm x_coeffs := by
    classical
    -- `repr` on basis vectors is Kronecker: repr (b j_x) = Finsupp.single j_x 1
    have h_repr_basis :
        ∀ j_x, b.repr (b j_x) = Finsupp.single j_x (1 : 𝔽q) := by
      intro j_x; simp only [Basis.repr_self]
    -- Reduce the RHS sum at coordinate j to the unique matching index
    have hx_at_j_simplified :
        (∑ j_x, x_coeffs j_x • (b.repr (b j_x))) j = x_coeffs j := by
      simp only [h_repr_basis, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_finsetSum,
        Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    -- The hypothesis `hx_val` gives `x.val` as a sum. We need to lift this to an
    -- equality of elements in the submodule `C_i`.
    let x_coeffs_fs := Finsupp.equivFunOnFinite.symm x_coeffs
    -- Let's construct the sum on the right-hand side
      -- of `hx_val` as an element of the submodule `C_i`.
    let rhs_sum := ∑ j_x, (x_coeffs_fs j_x) • (b j_x)
    -- Now, show that `x` is equal to this `rhs_sum`.
      -- We do this by showing their `.val`'s are equal.
    have h_x_eq_rhs_sum : x = rhs_sum := by
      apply Subtype.ext -- Two elements of a subtype are equal if their values are equal.
      -- The value of `rhs_sum` is a sum of the values of its components.
      have h_rhs_sum_val : rhs_sum.val = ∑ j_x, (x_coeffs_fs j_x) • (b j_x).val := by
        rw [Submodule.coe_sum]; apply Finset.sum_congr rfl; intro j_x _; rw [Submodule.coe_smul]
      -- We started with `hx_val`, which we can rewrite with the Finsupp `x_coeffs_fs`.
      have hx_val_fs : x.val = ∑ j_x, (x_coeffs_fs j_x) • (b j_x).val := by
        simp only [hx]
        congr
      -- Since `x.val` and `rhs_sum.val` are equal to the same sum, they are equal.
      rw [hx_val_fs, h_rhs_sum_val]
    -- Now we can rewrite `x` in our goal.
    rw [h_x_eq_rhs_sum]
    -- The goal is now `b.repr (∑ j_x, ... • b j_x) = x_coeffs_fs`.
    -- This is exactly what `Basis.repr_sum_self` states.
    have h_coe_eq := b.repr_sum_self x_coeffs_fs
    -- h : ⇑(b.repr (∑ i_1, x_coeffs_fs i_1 • b i_1)) = ⇑x_coeffs_fs
    have h_eq: b.repr (∑ i_1, x_coeffs_fs i_1 • b i_1) = x_coeffs_fs := by
      simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.univ_sum_single]
    rw [h_eq]
  -- Applying `j` to both sides of the `Finsupp` equality gives the goal.
  rw [h_coeffs_eq]
  -- ⊢ (Finsupp.equivFunOnFinite.symm x_coeffs) j = x_coeffs j
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply]

omit [DecidableEq 𝔽q] hF₂ in
lemma getSDomainBasisCoeff_of_iteratedQuotientMap
    [NeZero R_rate] (i : Fin r) (k : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx = i.val + k) (h_destIdx_le : destIdx.val ≤ ℓ)
    (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i) :
    let y : (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := i) (k:=k) (h_destIdx:=h_destIdx) (h_destIdx_le:=h_destIdx_le) (x:=x)
    ∀ (j: Fin (ℓ + R_rate - destIdx)),
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by
      apply Nat.lt_add_of_pos_right_of_le; omega)).repr y) j =
    ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i)
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)).repr x) ⟨j + k, by omega⟩:= by
  simp only
  intro j -- Let's define our bases and coefficient maps for clarity.
  let basis_source := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := i) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  let basis_target := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := destIdx) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  let x_coeffs := basis_source.repr x
  set y : (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
    (i := i) (k:=k) (h_destIdx:=h_destIdx) (h_destIdx_le:=h_destIdx_le) (x:=x)
  let y_coeffs := basis_target.repr y
  -- The proof relies on the uniqueness of basis representation
  have hx_sum : x.val = ∑ j_x, (x_coeffs j_x) • (basis_source j_x).val := by
    simp only [x_coeffs]
    conv_lhs => rw [← basis_source.sum_repr x]; rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul]
  have hy_sum : y.val = ∑ j_y, (y_coeffs j_y) • (basis_target j_y).val := by
    simp only [y_coeffs]
    conv_lhs => rw [← basis_target.sum_repr y]; rw [Submodule.coe_sum]
    simp_rw [Submodule.coe_smul]
  -- Derive y's expression from the definition of `iteratedQuotientMap`.
  have hy_sum_from_x : y = ∑ j_x, (x_coeffs j_x) •
      ((intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
        (k := k) (h_k := by omega)).eval (basis_source j_x).val) := by
    -- Start with `y = eval(x)`
    have hy_eval : y.val = (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      (i := i) (k := k) (h_k := by omega)).eval x.val := by rfl
    rw [hx_sum] at hy_eval
    -- simp only at hy_eval
    rw [hy_eval]
    have h_res: eval (∑ x : Fin (ℓ + R_rate - i), x_coeffs x • (basis_source x).val)
      (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega))
      = ∑ j_x : Fin (ℓ + R_rate - i), x_coeffs j_x • eval ((basis_source j_x).val)
          (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega)) := by
      have eval_interW_IsLinearMap :
        IsLinearMap 𝔽q (fun x : L =>
          (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
            (i := i) (k := k) (h_k := by omega)).eval x) := by
        exact intermediateNormVpoly_eval_is_linear_map 𝔽q β h_ℓ_add_R_rate
          (i := i) (k:=k) (h_k := by omega)
      let eval_interW_LinearMap := polyEvalLinearMap (intermediateNormVpoly 𝔽q β
        h_ℓ_add_R_rate (i := i) (k := k) (h_k := by omega)) eval_interW_IsLinearMap
      -- Use map_sum with a LinearMap (not a plain function)
      change eval_interW_LinearMap (∑ x_1 : Fin (ℓ + R_rate - i),
        x_coeffs x_1 • (basis_source x_1).val) = _
      rw [map_sum (g:=eval_interW_LinearMap) (s:=(Finset.univ : Finset (Fin (ℓ + R_rate - i))))]
      simp_rw [eval_interW_LinearMap.map_smul]
      rfl
    rw [h_res]
  -- Now, we simplify the term inside the second sum to show it's a basis vector of `basis_target`.
  have h_eval_basis_i : ∀ j_x, (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
    (i := i) (k:=k) (h_k := by omega)).eval (basis_source j_x).val
      = (normalizedW 𝔽q β destIdx).eval (β ⟨i.val + j_x.val, by omega⟩) := by
      -- TODO: how to make this cleaner?
    intro j_x
    let interW_i_k := intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k:=k) (h_k := by omega)
    let W_i := normalizedW 𝔽q β i
    let W_i_add_k := normalizedW 𝔽q β destIdx
    have h_comp_eq : interW_i_k.comp W_i = W_i_add_k := by
      have hi := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=i) (h_k := by omega)
      have hi_add_k := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (k:=destIdx) (h_k := by omega)
      simp_rw [W_i, W_i_add_k, interW_i_k, ←hi, ←hi_add_k]
      have h_interW_comp := intermediateNormVpoly_comp 𝔽q β h_ℓ_add_R_rate
        (i := 0) (k:=i) (l:=k) (destIdx := i) (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (h_k := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
        (h_l := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; omega)
      rw! [←h_destIdx] at h_interW_comp
      -- simp only [Fin.mk_zero'] at h_interW_comp
      rw [h_interW_comp]
    rw [get_sDomain_basis, ←Polynomial.eval_comp, h_comp_eq]
  -- Using this, we rewrite `hy_sum_from_x`.
  simp_rw [h_eval_basis_i] at hy_sum_from_x
  -- hy_sum_from_x : ↑y = ∑ x, x_coeffs x • eval (β ⟨↑i + ↑x, ⋯⟩) (normalizedW 𝔽q β ⟨↑i + k, ⋯⟩)
  let final_y_coeffs: Fin (ℓ + R_rate - destIdx) → 𝔽q :=
    fun j_x: Fin (ℓ + R_rate - destIdx) => x_coeffs ⟨j_x + k, by omega⟩
  have final_hy_sum : y = ∑ j_x: Fin (ℓ + R_rate - destIdx),
    (final_y_coeffs j_x) • (basis_target j_x).val := by
    rw [hy_sum_from_x]
    -- ⊢ ∑ x, x_coeffs x • eval (β ⟨↑i + ↑x, ⋯⟩) (normalizedW 𝔽q β ⟨↑i + k, ⋯⟩)
      -- = ∑ j_x, final_y_coeffs j_x • ↑(basis_target j_x)
    let a := k
    let b := ℓ + R_rate - destIdx
    have h_index_add: ℓ + R_rate - ↑i = a + b := by omega
    rw! (castMode := .all) [h_index_add];
    conv_lhs => -- split the sum in LHS into two parts
      rw [Fin.sum_univ_add]
      simp only [Fin.val_castAdd, Fin.val_natAdd]
    -- Eliminate the first sum of LHS
    have hβ: ∀ x: Fin a, β ⟨↑i + x, by omega⟩ ∈ U 𝔽q β (i := destIdx) := by
      intro x
      apply β_lt_mem_U 𝔽q β (i := destIdx) (j:=⟨i.val + x, by omega⟩)
    have h_eval_W_at_β: ∀ x: Fin a, eval (β ⟨↑i + ↑x, by omega⟩)
      (normalizedW 𝔽q β destIdx) = 0 := by
      intro x
      rw [normalizedWᵢ_vanishing 𝔽q β destIdx]
      exact hβ x
    -- simp only [Function.const_apply]
    conv_lhs => simp only [h_eval_W_at_β, smul_zero, Finset.sum_const_zero, zero_add]
    -- Convert the second sum of LHS
    congr
    simp only [b]
    funext j2
    rw [get_sDomain_basis]
    have h: i + k < r := by omega
    have h2: i.val + (a + ↑j2) = i + k + j2 := by omega
    simp_rw [h2]
    congr 1
    · simp only [final_y_coeffs, a]
      rw! (castMode:=.all) [h_index_add.symm];
      -- simp only
      apply congrArg
      rw [eqRec_eq_cast, ←Fin.cast_eq_cast (h := by omega)]
      apply Fin.eq_of_val_eq
      simp only [Fin.val_cast, Fin.val_natAdd];
      rw [Nat.add_comm]
    · simp_rw [h_destIdx]
  rw [getSDomainBasisCoeff_of_sum_repr 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val, by omega⟩) (h_i := by simp only; omega) (x:=x) (hx:=by exact hx_sum)]
  rw [getSDomainBasisCoeff_of_sum_repr 𝔽q β h_ℓ_add_R_rate
    (i := destIdx) (h_i := by omega) (x:=y) (x_coeffs := final_y_coeffs) (hx:=final_hy_sum)]

/-- Lifts a point `y` from a higher-indexed domain `sDomain j` to the canonical
base point of its fiber in a lower-indexed domain `sDomain i`,
by retaining all coeffs for the corresponding basis elements -/
noncomputable def sDomain.lift (i j : Fin r) (h_j : j < ℓ + R_rate) (h_le : i ≤ j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate j) :
    sDomain 𝔽q β h_ℓ_add_R_rate i := by
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := j) (h_i := by exact
    h_j)
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
  let ϑ := j.val - i.val
  let x_coeffs : Fin (ℓ + R_rate - i) → 𝔽q := fun k =>
    if hk: k.val < ϑ then 0
    else
      basis_y.repr y ⟨k.val - ϑ, by omega⟩  -- Shift indices to match y's basis
  exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 in
/-- Applying the forward map to a lifted point returns the original point. -/
theorem basis_repr_of_sDomain_lift (i j : Fin r) (h_j : j < ℓ + R_rate) (h_le : i ≤ j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := j)) :
    let x₀ := sDomain.lift 𝔽q β h_ℓ_add_R_rate i j (by omega) (by omega) y
    ∀ k: Fin (ℓ + R_rate - i),
      (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)).repr x₀ k =
        if hk: k < (j.val - i.val) then 0
        else (sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := j)
          (h_i := by omega)).repr y ⟨k - (j.val - i.val), by omega⟩ := by
  simp only;
  intro k
  simp only [sDomain.lift, Basis.repr_symm_apply, Basis.repr_linearCombination,
    Finsupp.equivFunOnFinite_symm_apply_apply]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- A helper form of `intermediateNormVpoly_comp_qmap` for the strict stage
`i < ℓ` and the remaining basis index `k`. -/
theorem intermediateNormVpoly_comp_qmap_helper (i : Fin r) (h_i : i < ℓ)
    (k : Fin (ℓ - (↑i + 1))) :
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨↑i + 1, by omega⟩ (k:=k) (h_k := by simp only; omega)).comp
        (qMap 𝔽q β ⟨↑i, by omega⟩ (by change i.val + 1 < r; omega)) =
    intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
      ⟨↑i, by omega⟩ (k:=k + 1) (h_k := by simp only; omega):= by
    rw [intermediateNormVpoly_comp_qmap 𝔽q β h_ℓ_add_R_rate (i := i)
      (destIdx := (⟨↑i + 1, by omega⟩ : Fin r)) (h_destIdx := by simp only)
      (k := k) (h_k := by omega)]

/-- ∀ `i` ∈ {0, ..., ℓ}, The `i`-th order novel polynomial basis `Xⱼ⁽ⁱ⁾`.
`Xⱼ⁽ⁱ⁾ := Π_{k=0}^{ℓ-i-1} (Ŵₖ⁽ⁱ⁾)^{jₖ}`, ∀ j ∈ {0, ..., 2^(ℓ-i)-1} -/
noncomputable def intermediateNovelBasisX (i : Fin r) (h_i : i ≤ ℓ)
    (j : Fin (2 ^ (ℓ - i))) : L[X] :=
  (Finset.univ: Finset (Fin (ℓ - i)) ).prod (fun k =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i (k:=k.val) (h_k:=by omega)) ^ (Nat.getBit k j))
-- NOTE: possibly we state some Basis for `(Xⱼ⁽ⁱ⁾)  `

omit [DecidableEq 𝔽q] [DecidableEq L] hF₂ in
-- Xⱼ⁽⁰⁾ = Xⱼ
theorem base_intermediateNovelBasisX (j : Fin (2 ^ ℓ)) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate 0 (h_i := by simp only [Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, zero_le]) j =
    Xⱼ 𝔽q β ℓ (by omega) j := by
  classical
  unfold intermediateNovelBasisX Xⱼ
  simp only [Fin.coe_ofNat_eq_mod]
  have h_res := base_intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate
  conv_lhs =>
    enter [2, x, 1]
    rw [h_res ⟨x, by omega⟩ (h_k := by simp only; omega)]
  congr

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
lemma intermediateNovelBasisX_zero_eq_one (i : Fin r) (h_i : i ≤ ℓ) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i ⟨0, by
      exact Nat.two_pow_pos (ℓ - ↑i)⟩ = 1 := by
  unfold intermediateNovelBasisX
  simp only [Nat.getBit_zero_eq_zero, pow_zero]
  exact Finset.prod_const_one

omit h_Fq_char_prime [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- The degree of an `i`-th order novel polynomial basis element `Xⱼ⁽ⁱ⁾(X)` is exactly `j`.
Somewhat similar to proof of `degree_Xⱼ`. -/
lemma degree_intermediateNovelBasisX (i : Fin r) (h_i : i ≤ ℓ) (j : Fin (2 ^ (ℓ - i))) :
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := h_i) (j := j)).degree = j := by
  rw [intermediateNovelBasisX, degree_prod]
  set rangeL := Fin ℓ
  -- ⊢ ∑ i ∈ rangeL, (normalizedW 𝔽q β i ^ bit (↑i) j).degree = ↑j
  by_cases h_ℓ_0: ℓ = 0
  · have h_ℓ_sub_i : ℓ - i = 0 := by omega
    rw! (castMode:=.all) [h_ℓ_sub_i]
    rw! (castMode:=.all) [h_ℓ_0]
    simp only [Finset.univ_eq_empty, Nat.pow_zero, Fin.val_eq_zero, degree_pow,
      nsmul_eq_mul, Finset.sum_empty, WithBot.coe_zero]
  · push Not at h_ℓ_0
    have deg_each: ∀ (k : Fin (ℓ - i)), ((intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
        (k:=k) (h_k := by omega))^(Nat.getBit k j)).degree
      = if Nat.getBit (k := k.val) (n := j.val) = 1 then (2:ℕ)^k.val else 0 := by
      intro (k : Fin (ℓ - i))
      rw [degree_pow]
      have h_deg_norm_vpoly: (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
        (k:=k) (h_k := by omega)).degree = 2 ^ k.val := by rw [degree_intermediateNormVpoly]
      rw [h_deg_norm_vpoly]
      simp only [nsmul_eq_mul, Nat.cast_ite, Nat.cast_pow,
        Nat.cast_ofNat, CharP.cast_eq_zero]
      have h_get_bit_lt_2 := Nat.getBit_lt_2 (k:=k.val) (n:=j.val)
      by_cases h: Nat.getBit (k := k.val) (n := j.val) = 1
      · simp only [h, Nat.cast_one, one_mul, ↓reduceIte]
      · simp only [h, ↓reduceIte, mul_eq_zero, Nat.cast_eq_zero, pow_eq_zero_iff',
        OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
        omega
    simp_rw [deg_each]
    -- ⊢ ∑ x, ↑(if (↑x).getBit ↑j = 1 then 2 ^ ↑i else 0) = ↑↑j
    set f:= fun x: ℕ => if Nat.getBit x j = 1 then (2: ℕ) ^ (x: ℕ) else 0
    simp only [Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, CharP.cast_eq_zero]
    conv_rhs =>
      rw [Nat.getBit_repr_univ (ℓ := ℓ - i) (j := j.val) (by omega)]
    simp only [WithBot.coe_sum, WithBot.coe_mul, WithBot.coe_pow, WithBot.coe_ofNat]
    congr 1
    funext (x : Fin (ℓ - i))
    have h_getBit_lt_2 := Nat.getBit_lt_2 (k:=x) (n:=j.val)
    by_cases h: Nat.getBit (k := x) (n := j.val) = 1
    · simp only [h, ↓reduceIte, WithBot.coe_one, one_mul]
    · simp only [h, ↓reduceIte, zero_eq_mul, WithBot.coe_eq_zero, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]; omega

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- `X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` for `i < ℓ` and
`j < 2^(ℓ - i - 1)`. -/
lemma even_index_intermediate_novel_basis_decomposition (i : Fin r)
    (h_i : i < ℓ) (j : Fin (2 ^ (ℓ - i - 1))) :
  intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2, by
    apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩  = (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
  ⟩).comp (qMap 𝔽q β i (by omega)) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j)ₖ) = ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]
  conv_rhs =>
    enter [2, x]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q (h_i := h_i)]
  -- ⊢ ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ Nat.getBit (↑x) (↑j * 2) =
  -- ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ Nat.getBit ↑x ↑j
  set fleft := fun x : Fin (ℓ - ↑i) =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := x) (h_k := by omega)) ^ Nat.getBit (↑x) (↑j * 2)
  have h_n_shift: ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift: Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
  Fin.prod_univ_succ (M:=L[X]) (n:=ℓ - (↑i + 1)) (f:=fun x => fleft ⟨x, by omega⟩)
  have h_lhs_prod_eq: ∏ x : Fin (ℓ - ↑i),
    fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)
  rw [←h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]
  have fleft_0_eq_0: fleft ⟨(0: Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = 1 := by
    unfold fleft
    simp only
    have h_exp: Nat.getBit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2) = 0 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      have res := Nat.getBit_zero_of_two_mul (n:=j.val)
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
  have h_exp_eq: Nat.getBit (↑x + 1) (↑j * 2) = Nat.getBit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two (k:=↑x) (n:=↑j)
  rw [h_exp_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- `X₂ⱼ₊₁⁽ⁱ⁾ = X * Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` for `i < ℓ` and
`j < 2^(ℓ - i - 1)`. -/
lemma odd_index_intermediate_novel_basis_decomposition
    (i : Fin r) (h_i : i < ℓ) (j : Fin (2 ^ (ℓ - i - 1))) :
    intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
    ⟩  = X * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, by
      apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
    ⟩).comp (qMap 𝔽q β i (by omega)) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j₊₁)ₖ)
  -- = X * ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]
  conv_rhs =>
    enter [2]
    enter [2, x, 1]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q β h_ℓ_add_R_rate
      (i := i) (h_i := by omega) (k := ⟨x, by omega⟩)]
  -- ⊢ ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ Nat.getBit (↑x) (↑j * 2 + 1) =
  -- X * ∏ x, intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ Nat.getBit ↑x ↑j
  set fleft := fun x : Fin (ℓ - ↑i) =>
    (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate (i := i) (k := x)
      (h_k := by omega)) ^ Nat.getBit (↑x) (↑j * 2 + 1)
  have h_n_shift: ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift: Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
  Fin.prod_univ_succ (M:=L[X]) (n:=ℓ - (↑i + 1)) (f:=fun x => fleft ⟨x, by omega⟩)
  have h_lhs_prod_eq: ∏ x : Fin (ℓ - ↑i),
    fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)
  rw [←h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]
  have fleft_0_eq_X: fleft ⟨(0: Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = X := by
    unfold fleft
    simp only
    have h_exp: Nat.getBit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2 + 1) = 1 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      unfold Nat.getBit
      simp only [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_add_mod_self_right, Nat.mod_succ]
    rw [h_exp]
    simp only [pow_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero]
  rw [fleft_0_eq_X]
  congr -- apply Finset.prod_congr rfl
  funext x
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq: Nat.getBit (↑x + 1) (↑j * 2 + 1) = Nat.getBit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two_add_one (k:=↑x) (n:=↑j)
  rw [h_exp_eq]

/-- ∀ `i` ∈ {0, ..., ℓ}, The `i`-th order evaluation polynomial
`P⁽ⁱ⁾(X) := ∑_{j=0}^{2^(ℓ-i)-1} coeffsⱼ ⋅ Xⱼ⁽ⁱ⁾(X)` over the domain `S⁽ⁱ⁾`.
  where the polynomial `P⁽⁰⁾(X)` over the domain `S⁽⁰⁾` is exactly the original
  polynomial `P(X)` we need to evaluate,
  and `coeffs` is the list of `2^(ℓ-i)` coefficients of the polynomial.
-/
noncomputable def intermediateEvaluationPoly (i : Fin r) (h_i : i ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (j: Fin (2^(ℓ-i))), C (coeffs j) *
    (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i j)

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
lemma degree_intermediateEvaluationPoly_lt (i : Fin r) (h_i : i ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
  (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate i h_i coeffs).degree < 2 ^ (ℓ - i) := by
  rw [intermediateEvaluationPoly]
  -- simp only
  apply (Polynomial.degree_sum_le Finset.univ (fun (j : Fin (2^(ℓ-i))) => C (coeffs ⟨j, by omega⟩)
    * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i (h_i := h_i) ⟨j, by omega⟩))).trans_lt
  apply (Finset.sup_lt_iff ?_).mpr ?_
  · -- ⊢ ⊥ < 2 ^ ℓ
    exact compareOfLessAndEq_eq_lt.mp rfl
  · -- ∀ b ∈ univ, (C (a b) * Xⱼ 𝔽q β ℓ h_ℓ b).degree < 2 ^ ℓ
    intro (j : Fin (2 ^ (ℓ - ↑i))) _
    -- ⊢ (C (a j) * Xⱼ 𝔽q β ℓ h_ℓ j).degree < 2 ^ ℓ
    calc (C (coeffs ⟨j, by omega⟩) * intermediateNovelBasisX 𝔽q β
      h_ℓ_add_R_rate i h_i ⟨j, by omega⟩).degree
      _ ≤ (C (coeffs ⟨j, by omega⟩)).degree + (intermediateNovelBasisX 𝔽q β
        h_ℓ_add_R_rate i h_i ⟨j, by omega⟩).degree := by apply Polynomial.degree_mul_le
      _ ≤ 0 + (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i ⟨j, by omega⟩).degree := by
        gcongr; exact Polynomial.degree_C_le
      _ = ↑j.val := by
        rw [degree_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i ⟨j, by omega⟩];
        simp only [zero_add]; rfl
      _ < ↑(2^(ℓ-i)) := by
        exact WithBot.coe_lt_coe.mpr j.isLt

section IntermediateNovelPolynomialBasis

/-- The basis vectors for the intermediate level `i`. -/
noncomputable def intermediateBasisVectors (i : Fin r) (h_i : i ≤ ℓ) :
  Fin (2 ^ (ℓ - i)) → L⦃<2^(ℓ - i)⦄[X] :=
  fun j => ⟨intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i j, by
    apply Polynomial.mem_degreeLT.mpr
    rw [degree_intermediateNovelBasisX]
    -- Proof that j < 2^(ℓ-i)
    change (j.val: WithBot ℕ) < ((2: WithBot ℕ) ^ (ℓ - i))
    exact WithBot.coe_lt_coe.mpr j.isLt
  ⟩

/-- The vector space of coefficients for polynomials of degree < 2^(ℓ-i). -/
abbrev IntermediateCoeffVecSpace (i : Fin r) := Fin (2^(ℓ - i)) → L

/-- The linear map from polynomials (in the subtype) to their coefficient vectors at level `i`. -/
def intermediateToCoeffsVec (i : Fin r) : -- (h_i : i ≤ ℓ)
    L⦃<2^(ℓ - i)⦄[X] →ₗ[L] IntermediateCoeffVecSpace (L := L) (ℓ := ℓ) i where
  toFun := fun p => fun k => p.val.coeff k.val
  map_add' := fun p q => by ext k; simp [coeff_add]
  map_smul' := fun c p => by ext k; simp [coeff_smul, smul_eq_mul]

/-- The Change-of-Basis Matrix from the Intermediate Novel Basis to the Monomial Basis.
    A_jk = coeff of X^k in intermediate basis vector X_j. -/
noncomputable def intermediateChangeOfBasisMatrix (i : Fin r) (h_i : i ≤ ℓ) :
    Matrix (Fin (2 ^ (ℓ - i))) (Fin (2 ^ (ℓ - i))) L :=
  fun j k => (intermediateToCoeffsVec (L := L) i
    (intermediateBasisVectors 𝔽q β h_ℓ_add_R_rate i h_i j)) k

omit h_Fq_char_prime [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
theorem intermediateChangeOfBasisMatrix_lower_triangular (i : Fin r) (h_i : i ≤ ℓ) :
    (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i).BlockTriangular
      ⇑OrderDual.toDual := by
  intro j k h_jk
  simp only [OrderDual.toDual_lt_toDual] at h_jk
  dsimp [intermediateChangeOfBasisMatrix, intermediateToCoeffsVec, intermediateBasisVectors]
  -- We need coeff(X_j, k) = 0 when j < k
  -- This holds because deg(X_j) = j < k
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [Polynomial.natDegree_eq_of_degree_eq_some
    (degree_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i (by omega) j)]
  exact h_jk

omit h_Fq_char_prime [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
theorem intermediateChangeOfBasisMatrix_diag_ne_zero (i : Fin r) (h_i : i ≤ ℓ) :
    (∀ j, (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i) j j ≠ 0) := by
  intro j
  dsimp [intermediateChangeOfBasisMatrix, intermediateToCoeffsVec, intermediateBasisVectors]
  -- The diagonal entry is the leading coefficient
  apply Polynomial.coeff_ne_zero_of_eq_degree
  exact degree_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate i h_i j

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
theorem intermediateChangeOfBasisMatrix_det_ne_zero (i : Fin r) (h_i : i ≤ ℓ) :
    (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj_mem_univ
    let res := intermediateChangeOfBasisMatrix_diag_ne_zero 𝔽q β h_ℓ_add_R_rate i h_i j
    exact res
  · exact intermediateChangeOfBasisMatrix_lower_triangular 𝔽q β h_ℓ_add_R_rate i h_i

/-- The intermediate change-of-basis matrix is invertible. -/
@[reducible] noncomputable def intermediateChangeOfBasisMatrix_invertible
    (i : Fin r) (h_i : i ≤ ℓ) :
    Invertible (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i) := by
  refine Matrix.invertibleOfIsUnitDet _ ?_
  exact Ne.isUnit (intermediateChangeOfBasisMatrix_det_ne_zero 𝔽q β h_ℓ_add_R_rate i h_i)

/-- Convert monomial coefficients to novel coefficients at level `i`.
    n = m * A⁻¹ -/
noncomputable def monomialToINovelCoeffs (i : Fin r) (h_i : i ≤ ℓ)
    (monomial_coeffs : Fin (2 ^ (ℓ - i)) → L) : Fin (2 ^ (ℓ - i)) → L :=
  let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i
  letI : Invertible A := intermediateChangeOfBasisMatrix_invertible 𝔽q β h_ℓ_add_R_rate i h_i
  Matrix.vecMul monomial_coeffs (⅟A)

/-- Convert novel coefficients to monomial coefficients at level `i`.
    m = n * A -/
noncomputable def iNovelToMonomialCoeffs (i : Fin r) (h_i : i ≤ ℓ)
    (novel_coeffs : Fin (2 ^ (ℓ - i)) → L) : Fin (2 ^ (ℓ - i)) → L :=
  let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i
  Matrix.vecMul novel_coeffs A

noncomputable def getINovelCoeffs (i : Fin r) (h_i : i ≤ ℓ)
    (P : L[X]) : Fin (2 ^ (ℓ - i.val)) → L :=
  let mono_coefs : Fin (2 ^ (ℓ - i.val)) → L := fun k => P.coeff k.val
  monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i mono_coefs

omit h_Fq_char_prime [DecidableEq L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Round trip inverse property: Monomial -> Novel -> Monomial -/
theorem monomialToINovel_iNovelToMonomial_inverse (i : Fin r) (h_i : i ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
    iNovelToMonomialCoeffs 𝔽q β h_ℓ_add_R_rate i h_i
      (monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i coeffs) = coeffs := by
  letI : Invertible (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i) :=
    intermediateChangeOfBasisMatrix_invertible 𝔽q β h_ℓ_add_R_rate i h_i
  unfold monomialToINovelCoeffs iNovelToMonomialCoeffs
  dsimp
  rw [Matrix.vecMul_vecMul]
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.inv_mul_of_invertible, Matrix.vecMul_one]

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
theorem iNovelToMonomial_monomialToINovel_inverse (i : Fin r) (h_i : i ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
    monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i
      (iNovelToMonomialCoeffs 𝔽q β h_ℓ_add_R_rate i h_i coeffs) = coeffs := by
  letI : Invertible (intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i) :=
    intermediateChangeOfBasisMatrix_invertible 𝔽q β h_ℓ_add_R_rate i h_i
  unfold monomialToINovelCoeffs iNovelToMonomialCoeffs
  dsimp
  rw [Matrix.vecMul_vecMul]
  simp only [Matrix.invOf_eq_nonsing_inv, Matrix.mul_inv_of_invertible, Matrix.vecMul_one]

-- TODO: intermediate counterpart of `novelPolynomialBasis` for arbitrary subspace level `i`

omit [DecidableEq L] [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- **Reconstruction Lemma**:
    If `P` has degree < 2^(ℓ-i), and we convert its coefficients to the intermediate novel basis,
    the resulting `intermediateEvaluationPoly` is exactly `P`.
-/
lemma intermediateEvaluationPoly_from_inovel_coeffs_eq_self
    (i : Fin r) (h_i : i ≤ ℓ) (P : L[X])
    (hP_deg : P.degree < 2 ^ (ℓ - i.val)) :
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := h_i)
      (coeffs := getINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i P) = P := by
  -- 1. Apply extensionality (two polys are equal if all coeffs are equal)
  apply Polynomial.ext
  intro k
  let N := 2 ^ (ℓ - i.val)
  set novel_coeffs := getINovelCoeffs 𝔽q β h_ℓ_add_R_rate i h_i P
  -- 2. Case Analysis on k
  by_cases hk : k < N
  · let k_fin : Fin N := ⟨k, hk⟩
    -- LHS expansion
    conv_lhs => rw [intermediateEvaluationPoly]
    -- coeff (∑ C * X_basis) = ∑ coeff (C * X_basis) = ∑ C * coeff (X_basis)
    simp only [finsetSum_coeff, coeff_C_mul]
    -- Crucial Step: Recognize this sum as Matrix Multiplication
    -- ∑_j (novel_j * coeff(Basis_j, k)) is exactly the k-th component of (novel * A)
    -- where A is the intermediateChangeOfBasisMatrix.
    let A := intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate i h_i
    -- By definition of A, A_jk = coeff(Basis_j, k)
    have h_matrix_def : ∀ j, (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i)
      (h_i := h_i) (j := j)).coeff k = A j k_fin := fun j => by
      dsimp only [intermediateChangeOfBasisMatrix, intermediateToCoeffsVec,
        intermediateBasisVectors, LinearMap.coe_mk, AddHom.coe_mk, A]
    simp_rw [h_matrix_def]
    -- `⊢ ∑ x, novel_coeffs x * A x k_fin = P.coeff k`, which is (vecMul novel_coeffs A) k_fin
    have h_left_eq : ∑ x, novel_coeffs x * A x k_fin = Matrix.vecMul novel_coeffs A k_fin := by
      dsimp only [Matrix.vecMul, dotProduct]
    conv_lhs => rw [h_left_eq] -- change to vecMul notation
    -- Apply the Inversion Logic
    -- novel_coeffs was defined as (monomial * A⁻¹)
    -- So we have (monomial * A⁻¹) * A
    unfold novel_coeffs getINovelCoeffs monomialToINovelCoeffs
    -- We need to unfold the let binding inside the goal
    -- It is easier to rewrite the vector multiplication: (v * A⁻¹) * A = v * (A⁻¹ * A) = v * I = v
    rw [Matrix.vecMul_vecMul]
    rw [invOf_mul_self]
    rw [Matrix.vecMul_one]
  · -- Case k >= N (Out of bounds)
    push Not at hk
    -- RHS is 0 because P has degree < N
    rw [Polynomial.coeff_eq_zero_of_degree_lt (n := k) (p := intermediateEvaluationPoly 𝔽q β
      h_ℓ_add_R_rate i h_i novel_coeffs) (h := by
      let res := degree_intermediateEvaluationPoly_lt 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) h_i (coeffs := novel_coeffs)
      have hk' : (2 : ℕ) ^ (ℓ - i.val) ≤ k := hk
      have hpow : ∀ m : ℕ, (2 : WithBot ℕ) ^ m = ((2 ^ m : ℕ) : WithBot ℕ) := by
        intro m; induction m with
        | zero => simp
        | succ j ih => rw [pow_succ, pow_succ, ih]; push_cast; ring
      have hle : (2 : WithBot ℕ) ^ (ℓ - i.val) ≤ (k : WithBot ℕ) := by
        rw [hpow]; exact_mod_cast hk'
      exact lt_of_lt_of_le res hle
    )]
    rw [Polynomial.coeff_eq_zero_of_degree_lt (n := k) (p := P) (h := by
      have hk' : (2 : ℕ) ^ (ℓ - i.val) ≤ k := hk
      have hpow : ∀ m : ℕ, (2 : WithBot ℕ) ^ m = ((2 ^ m : ℕ) : WithBot ℕ) := by
        intro m; induction m with
        | zero => simp
        | succ j ih => rw [pow_succ, pow_succ, ih]; push_cast; ring
      have hle : (2 : WithBot ℕ) ^ (ℓ - i.val) ≤ (k : WithBot ℕ) := by
        rw [hpow]; exact_mod_cast hk'
      exact lt_of_lt_of_le hP_deg hle
    )]

end IntermediateNovelPolynomialBasis


/-- The even and odd refinements of `P⁽ⁱ⁾(X)` which are polynomials in the `(i+1)`-th basis.
`P₀⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)`
`P₁⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j+1} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)` -/
noncomputable def evenRefinement (i : Fin r) (h_i : i < ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
  ⟩) * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, hj⟩)

noncomputable def oddRefinement (i : Fin r) (h_i : i < ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2+1, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
  ⟩) * (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
    (h_i := by simp only; omega) ⟨j, hj⟩)

omit [DecidableEq 𝔽q] [DecidableEq L] h_Fq_char_prime hF₂ hβ_lin_indep h_β₀_eq_1 in
/-- **Key Polynomial Identity (Equation 39)**. This identity is the foundation for the
butterfly operation in the Additive NTT. It relates a polynomial in the `i`-th basis to
its even and odd parts expressed in the `(i+1)`-th basis via the quotient map `q⁽ⁱ⁾`.
`∀ i ∈ {0, ..., ℓ-1}, P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` -/
theorem evaluation_poly_split_identity (i : Fin r) (h_i : i < ℓ)
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
  let P_i: L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) coeffs
  let P_even_i_plus_1: L[X] := evenRefinement 𝔽q β h_ℓ_add_R_rate i h_i coeffs
  let P_odd_i_plus_1: L[X] := oddRefinement 𝔽q β h_ℓ_add_R_rate i h_i coeffs
  let q_i: L[X] := qMap 𝔽q β i (by omega)
  P_i = (P_even_i_plus_1.comp q_i) + X * (P_odd_i_plus_1.comp q_i) := by
  simp only [intermediateEvaluationPoly]
  simp only [evenRefinement, Fin.eta, sum_comp, mul_comp, C_comp, oddRefinement]
  set leftEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩
  set leftOddTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j * 2 + 1, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
  ⟩
  have h_split_P_i: ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i)), C (coeffs ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i) (ℓ-i) (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) ⟨j, by omega⟩ =
    leftEvenTerm + leftOddTerm := by
    unfold leftEvenTerm leftOddTerm
    simp only [Fin.eta]
    -- ⊢ ∑ k ∈ Fin (2 ^ (ℓ - ↑i)), C (coeffsₖ) * Xₖ⁽ⁱ⁾(X) = -- just pure even odd split
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs₂ₖ) * X₂ₖ⁽ⁱ⁾(X) +
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs₂ₖ+1) * X₂ₖ+1⁽ⁱ⁾(X)
    set f1 := fun x: ℕ => -- => use a single function to represent the sum
      if hx: x < 2 ^ (ℓ - ↑i) then
        C (coeffs ⟨x, hx⟩) *
          intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
            (j := ⟨x, by omega⟩)
      else 0
    have h_x: ∀ x: Fin (2 ^ (ℓ - ↑i)), f1 x.val =
      C (coeffs ⟨x.val, by omega⟩) *
        intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
          (j := ⟨x.val, by omega⟩) := by
      intro x
      unfold f1
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    conv_lhs =>
      enter [2, x]
      rw [←h_x x]
    have h_x_2: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2) =
      C (coeffs ⟨x.val * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (j := ⟨x.val * 2, by
          exact mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
        ⟩) := by
      intro x
      unfold f1
      -- simp only
      have h_x_lt_2_pow_i_minus_1 :=
        mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
      simp only [add_zero] at h_x_lt_2_pow_i_minus_1
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]
    conv_rhs =>
      enter [1, 2, x]
      rw [←h_x_2 x]
    have h_x_3: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2+1) =
      C (coeffs ⟨x.val * 2 + 1, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
          (j := ⟨x.val * 2 + 1, by
          exact mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
        ⟩) := by
      intro x
      unfold f1
      -- simp only
      have h_x_lt_2_pow_i_minus_1 := mul_two_add_bit_lt_two_pow x.val
        (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]
    conv_rhs =>
      enter [2, 2, x]
      rw [←h_x_3 x]
    -- ⊢ ∑ x, f1 ↑x = ∑ x, f1 (↑x * 2) + ∑ x, f1 (↑x * 2 + 1)
    have res := sum_univ_odd_even (f := f1) (n := ℓ - ↑i - 1)
    rw [show (2:ℕ) ^ (ℓ - ↑i) = 2 ^ (ℓ - ↑i - 1 + 1) from by congr 1; omega]
    rw [res]
    congr 1
    · exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])
    · exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])
  conv_lhs => rw [h_split_P_i]
  set rightEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
      C (coeffs ⟨j * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
          (h_i := by simp only; omega) ⟨j, by
          apply lt_two_pow_of_lt_two_pow_exp_le (x:=j)
            (i := ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
        ⟩).comp (qMap 𝔽q β i (by omega))
  set rightOddTerm :=
    X *
      ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
        C (coeffs ⟨j * 2 + 1, by
          calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
            _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
        ⟩) *
          (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val+1, by omega⟩)
            (h_i := by simp only; omega) ⟨j, by
            apply lt_two_pow_of_lt_two_pow_exp_le (x:=j)
              (i := ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
              ⟩).comp (qMap 𝔽q β i (by omega))
  conv_rhs => change rightEvenTerm + rightOddTerm
  have h_right_even_term: leftEvenTerm = rightEvenTerm := by
    unfold rightEvenTerm leftEvenTerm
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.eta, mul_eq_mul_left_iff, map_eq_zero]
    --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∨ a₂ⱼ = 0
    by_cases h_a_j_eq_0: coeffs ⟨j * 2, by
      calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
        _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
    ⟩ = 0
    · simp only [h_a_j_eq_0, or_true]
    · simp only [h_a_j_eq_0, or_false]
      --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))
      exact even_index_intermediate_novel_basis_decomposition (L := L)
        𝔽q β h_ℓ_add_R_rate (i := i) (h_i := h_i) j
  have h_right_odd_term: rightOddTerm = leftOddTerm := by
    unfold rightOddTerm leftOddTerm
    simp only [Fin.eta]
    conv_rhs =>
      simp only [Fin.is_lt, Fin.eta]
      enter [2, x];
      rw [odd_index_intermediate_novel_basis_decomposition 𝔽q β (h_i := h_i)]
      rw [mul_comm (a:=X)]
    rw [Finset.mul_sum]
    congr
    funext x
    ring_nf -- just associativity and commutativity of multiplication in L[X]
    rfl
  rw [h_right_even_term, h_right_odd_term]

omit [DecidableEq 𝔽q] [DecidableEq L] hF₂ in
-- P⁽⁰⁾(X) = P(X)
lemma intermediate_poly_P_base (h_ℓ : ℓ ≤ r) (coeffs : Fin (2 ^ ℓ) → L) :
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := 0)
    (h_i := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_le]) coeffs =
    polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ coeffs := by
  unfold polynomialFromNovelCoeffs intermediateEvaluationPoly
  simp only [Fin.coe_ofNat_eq_mod]
  conv_rhs =>
    enter [2, j]
    rw [←base_intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate j]
  congr

end IntermediateStructures
end AdditiveNTT
