/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.AdditiveNTT.Algorithm
import CompPoly.Fields.Binary.AdditiveNTT.Impl

/-!
# Additive NTT Correctness

The stage-wise correctness argument and the final correctness theorem for the
Additive NTT.
-/

open Polynomial AdditiveNTT Module
namespace AdditiveNTT

section ImplementationEquivalence

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable {𝔽q : Type} [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
variable [hFq_card : Fact (Fintype.card 𝔽q = 2)]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
variable [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ R_rate : ℕ} (h_ℓ_add_R_rate : ℓ + R_rate < r)

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- The `bitsToU` mapping is a bijection: showing that iterating bits corresponds
exactly to the linear span. -/
theorem bitsToU_bijective (i : Fin r) :
    Function.Bijective (bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate) i) := by
  -- A map between finite sets of the same size is bijective iff it is injective.
  apply (Fintype.bijective_iff_injective_and_card
    (f := bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := R_rate) i)).mpr ?_
  constructor
  -- Part A: Injectivity (Linear Independence)
  · intro k1 k2 h_eq
    unfold bitsToU at h_eq
    simp only [Subtype.mk.injEq] at h_eq
    -- We define the coefficients c_j based on the bits of k
    let c (k : ℕ) (j : Fin i) : 𝔽q :=
      if (Nat.getBit (n := k) (k := j.val) == 1) then 1 else 0
    -- The sum can be rewritten as a linear combination with coefficients in Fq
    have h_sum (k : Fin (2^i.val)) :
      (Finset.univ.sum fun (j : Fin i) =>
        if (Nat.getBit (n := k.val) (k := j.val) == 1) then
          β ⟨j, by omega⟩
        else (0 : L)) =
      Finset.univ.sum fun j => (c k.val j) • β ⟨j, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [c]
      split_ifs <;> simp
    rw [h_sum k1, h_sum k2] at h_eq
    -- 1. Move everything to LHS: sum (c1 - c2) * beta = 0
    rw [←sub_eq_zero] at h_eq
    rw [←Finset.sum_sub_distrib] at h_eq
    simp_rw [←sub_smul] at h_eq
    rw [←sub_eq_zero] at h_eq
    -- 2. Establish that the first `i` basis elements are Linearly Independent
    have h_lin_indep := hβ_lin_indep.out
    -- We restrict the global independence (Fin r) to the subset (Fin i)
    have h_indep_restricted := LinearIndependent.comp h_lin_indep
      (Fin.castLE (Nat.le_of_lt_succ (by omega)) : Fin i → Fin r)
      (Fin.castLE_injective _)
    -- 3. Apply Linear Independence to show every coefficient is 0
    -- This gives us: ∀ j, c k1 j - c k2 j = 0
    simp only [sub_zero] at h_eq
    have h_coeffs_zero : ∀ j : Fin i, j ∈ Finset.univ → c k1.val j - c k2.val j = 0 :=
      linearIndependent_iff'.mp h_indep_restricted
        (Finset.univ)
        (fun j => c k1.val j - c k2.val j)
        h_eq
    -- 4. Prove k1 = k2 by showing all bits are equal
    ext
    apply Nat.eq_iff_eq_all_getBits.mpr
    intro n
    have h_bit_k1_lt_2 := Nat.getBit_lt_2 (n := k1) (k := n)
    have h_bit_k2_lt_2 := Nat.getBit_lt_2 (n := k2) (k := n)
    if hn : n < i.val then
      let j : Fin i := ⟨n, hn⟩
      have h_c_diff_zero := h_coeffs_zero j (Finset.mem_univ j)
      simp only [sub_eq_zero] at h_c_diff_zero
      dsimp only [beq_iff_eq, c] at h_c_diff_zero
      interval_cases hk1: Nat.getBit (n := k1) (k := j)
      · interval_cases hk2: Nat.getBit (n := k2) (k := j)
        · rfl;
        · simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, BEq.rfl,
          zero_ne_one] at h_c_diff_zero;
      · interval_cases hk2: Nat.getBit (n := k2) (k := j)
        · simp only [BEq.rfl, ↓reduceIte, Nat.reduceBEq, Bool.false_eq_true,
          one_ne_zero] at h_c_diff_zero;
        · rfl
    else
      have h_k1 := Nat.getBit_of_lt_two_pow (n := i) (a := k1) (k := n)
      have h_k2 := Nat.getBit_of_lt_two_pow (n := i) (a := k2) (k := n)
      simp only [hn, ↓reduceIte] at h_k1 h_k2
      rw [h_k1, h_k2]
  -- Part B: Cardinality (Surjectivity check)
  · -- ⊢ Fintype.card (Fin (2 ^ ↑i)) = Fintype.card ↥(U i)
    rw [Fintype.card_fin]
    rw [AdditiveNTT.U_card (𝔽q := 𝔽q)
      (β := β) (i := i)]
    rw [hFq_card.out]

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `evalWAt` equals the standard definition of `W_i(x)`. -/
theorem evalWAt_eq_W (i : Fin r) (x : L) :
    evalWAt (β := β) (ℓ := ℓ) (R_rate := R_rate) (i := i) x =
    (W (𝔽q := 𝔽q) (β := β) (i := i)).eval x := by
  -- 1. Convert implementation to mathematical product over Fin(2^i)
  unfold evalWAt getUElements
  rw [List.map_map]
  rw [List.prod_finRange_eq_finset_prod]
  -- 2. Prepare RHS
  rw [AdditiveNTT.W, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- 3. Use Finset.prod_bij to show equality via the bijection
  apply Finset.prod_bij (s := ((Finset.univ (α := (Fin (2^(i.val)))))))
    (t := (Finset.univ : Finset (U 𝔽q β i)))
    (i := fun k _ =>
      bitsToU (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (r := r) (R_rate := R_rate) (L := L) (i := i) k)
    (hi := by
      intro a _
      exact Finset.mem_univ _)
    (i_inj := by
      intro a₁ _ a₂ _ h_eq
      exact (bitsToU_bijective (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (r := r) (R_rate := R_rate) (L := L) (i := i)).1 h_eq)
    (i_surj := by
      intro b _
      obtain ⟨a, ha_eq⟩ := (bitsToU_bijective (𝔽q := 𝔽q)
        (β := β) (ℓ := ℓ) (r := r) (R_rate := R_rate) (L := L) (i := i)).2 b
      use a
      constructor
      · exact ha_eq
      · exact Finset.mem_univ a
    )
    (h := by
      intro a ha_univ
      rfl
    )

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `evalNormalizedWAt` equals the standard definition of `Ŵ_i(x)`. -/
theorem evalNormalizedWAt_eq_normalizedW (i : Fin r) (x : L) :
    evalNormalizedWAt (β := β) (ℓ := ℓ) (R_rate := R_rate) (i := i) x
    = (normalizedW (𝔽q := 𝔽q) (β := β) (i := i)).eval x := by
  unfold evalNormalizedWAt
  rw [evalWAt_eq_W (r := r) (L := L) (𝔽q := 𝔽q) (β := β) i x]
  simp only
  rw [evalWAt_eq_W (r := r) (L := L) (𝔽q := 𝔽q) (β := β) i (β i)]
  rw [AdditiveNTT.normalizedW]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp only [one_div]
  apply mul_comm

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `computableTwiddleFactor` equals the standard definition of `twiddleFactor`. -/
theorem computableTwiddleFactor_eq_twiddleFactor (i : Fin ℓ) :
    computableTwiddleFactor (r := r) (ℓ := ℓ) (β := β) (L := L)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) =
  twiddleFactor (𝔽q := 𝔽q) (L := L) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) := by
  unfold computableTwiddleFactor twiddleFactor
  simp_rw [evalNormalizedWAt_eq_normalizedW (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (i := ⟨i, by omega⟩)]

omit [DecidableEq 𝔽q] h_Fq_char_prime h_β₀_eq_1 in
/-- Prove that `computableNTTStage` equals the standard definition of `NTTStage`. -/
theorem computableNTTStage_eq_NTTStage (i : Fin ℓ) :
    computableNTTStage (𝔽q := 𝔽q) (r := r) (L := L) (ℓ := ℓ) (β := β) (R_rate := R_rate)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) =
  NTTStage (𝔽q := 𝔽q) (L := L) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) := by
  unfold computableNTTStage NTTStage
  simp only [Fin.eta]
  simp_rw [computableTwiddleFactor_eq_twiddleFactor (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (i := ⟨i, by omega⟩)]

omit [DecidableEq 𝔽q] [Fact (Nat.Prime (ringChar 𝔽q))] [Fact (β 0 = 1)] in
/-- The proof-oriented computable additive NTT agrees with the abstract
additive NTT specification. -/
theorem computableAdditiveNTT_eq_additiveNTT (a : Fin (2 ^ ℓ) → L) :
    computableAdditiveNTT (𝔽q := 𝔽q) (L := L) (r := r) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a) =
    additiveNTT (𝔽q := 𝔽q) (L := L) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a) := by
  unfold computableAdditiveNTT additiveNTT
  simp only
  congr
  funext current_b i
  rw [computableNTTStage_eq_NTTStage (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ - 1 - i, by omega⟩)]

/-- The pure `StateT` specialization of the fast additive NTT is extensionally
equal to the proof-oriented computable implementation after converting its
output array to a `Fin`-indexed function.

This is the preferred proof boundary for the fast path: once this theorem is
proved, correctness against the abstract additive NTT specification follows from
`computableAdditiveNTT_eq_additiveNTT`. The ST-backed runtime path shares the
same monadic core, but `ST.Ref` itself is opaque, so this transparent `StateT`
specialization is the kernel-checkable correctness surface. -/
theorem computableAdditiveNTTFastState_eq_computableAdditiveNTT (a : Fin (2 ^ ℓ) → L) :
    AdditiveNTT.arrayToFinFunction (2^(ℓ + R_rate))
      (computableAdditiveNTTFastState (L := L) (r := r) (β := β)
        (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a)) =
    computableAdditiveNTT (𝔽q := 𝔽q) (L := L) (r := r) (β := β)
      (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a) := by
  sorry

/-- The pure `StateT` specialization of the fast additive NTT is correct against
the abstract additive NTT specification after converting its output array to a
`Fin`-indexed function. -/
theorem computableAdditiveNTTFastState_eq_additiveNTT (a : Fin (2 ^ ℓ) → L) :
    AdditiveNTT.arrayToFinFunction (2^(ℓ + R_rate))
      (computableAdditiveNTTFastState (L := L) (r := r) (β := β)
        (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a)) =
    additiveNTT (𝔽q := 𝔽q) (L := L) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a) := by
  rw [computableAdditiveNTTFastState_eq_computableAdditiveNTT (𝔽q := 𝔽q) (β := β)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a)]
  exact computableAdditiveNTT_eq_additiveNTT (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
    (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (a := a)

end ImplementationEquivalence

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
    push Not at h_b_bit_eq_0
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
    Nat.pow_zero, Nat.getLowBits_zero_eq_zero (n := j.val), Fin.isValue] at res
  simp only [←
    intermediate_poly_P_base 𝔽q β h_ℓ_add_R_rate
      h_ℓ original_coeffs,
    Fin.zero_eta]
  erw [base_coeffsBySuffix] at res
  erw [← res]
  simp_rw [Nat.sub_right_comm]

end AlgorithmCorrectness

end AdditiveNTT
