/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.BF128Ghash.Basic

/-! # BF128Ghash Computable Specification (GF(2^128))

We define the field operations using computable `BitVec`.
We verify them by proving isomorphism to `GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)`.

## Main Definitions

- `ConcreteBF128Ghash`: The type of `GF(2^128)` elements represented as `BitVec 128`
- `instFieldConcreteBF128Ghash`: The field instance for `ConcreteBF128Ghash`
- `toQuot`: The canonical map from `ConcreteBF128Ghash` to `AdjoinRoot ghashPoly`
- `reduce_clMul`: The reduction of the carry-less multiplication
- `inv_itoh_tsujii`: The Itoh-Tsujii inversion algorithm
- `toQuot_inv_itoh_tsujii`: The lemma that `inv_itoh_tsujii` computes `a^(2^128 - 2)`

## References
* [NIST-SP-800-38D] Dworkin, M. Recommendation for Block Cipher Modes of Operation:
  Galois/Counter Mode (GCM) and GMAC. NIST Special Publication 800-38D.
  https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

-/

namespace BF128Ghash

set_option maxRecDepth 1500

open BitVec Polynomial Ideal BF128Ghash AdjoinRoot

@[reducible]
def ConcreteBF128Ghash : Type := B128

lemma ConcreteBF128Ghash_eq_BitVec : ConcreteBF128Ghash = BitVec 128 := rfl

section CarryLessMultiplicationReduction

/-- Folding Constant R = X^7 + X^2 + X + 1.
  Since P = X^128 + R, we have X^128 ≡ R (mod P). -/
def R_val : B128 := 135#128

lemma R_val_eq_ghashTail : toPoly R_val = ghashTail := by
  have h_val : R_val = (1 <<< 7) ^^^ (1 <<< 2) ^^^ (1 <<< 1) ^^^ 1 := rfl
  rw [h_val, ghashTail]
  simp only [toPoly_xor]
  rw [toPoly_one_shiftLeft 7 (by omega), toPoly_one_shiftLeft 2 (by omega),
      toPoly_one_shiftLeft 1 (by omega)]
  simp only [pow_one, ofNat_eq_ofNat, add_right_inj]
  simp_rw [toPoly_one_eq_one (w := 128) (h_w_pos := by omega)]

/-- Decomposition: x = h * X^128 + l where h and l are the high and low 128-bit parts. -/
lemma toPoly_split_256 (x : B256) :
    let h := x.extractLsb 255 128
    let l := x.extractLsb 127 0
    toPoly x = (toPoly h) * X^128 + (toPoly l) := by
  let h := x.extractLsb 255 128
  let l := x.extractLsb 127 0
  have h_h_lt_2_pow_128 : (to256 h).toNat < 2 ^ 128 := by
    rw [to256_toNat, BitVec.extractLsb_toNat]
    have h_exp: 255 - 128 + 1 = 128 := by omega
    rw [h_exp]
    apply Nat.mod_lt
    simp only [Nat.reducePow, gt_iff_lt, Nat.ofNat_pos]
  have h_recon : x = (to256 h <<< 128) ^^^ (to256 l) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor]
    · rw [BitVec.toNat_shiftLeft, to256_toNat, to256_toNat]
      trans (x.toNat >>> 128) * 2 ^ 128 + (x.toNat % 2 ^ 128)
      · apply Eq.symm; rw [Nat.shiftRight_eq_div_pow]
        conv_lhs => rw [mul_comm]; rw [Nat.div_add_mod]
      · have h_h_eq_getHighBits : h.toNat = Nat.getHighBits_no_shl 128 x.toNat := by
          rw [BitVec.extractLsb_toNat]
          have h_shift_lt : x.toNat >>> 128 < 2^128 := by
            rw [Nat.shiftRight_eq_div_pow]
            apply Nat.div_lt_of_lt_mul
            rw [←Nat.pow_add (a := 2) (m := 128) (n := 128)]
            exact BitVec.isLt x
          have h_size : 255 - 128 + 1 = 128 := by omega
          rw [h_size, Nat.mod_eq_of_lt h_shift_lt, Nat.getHighBits_no_shl]
        have h_l_eq_getLowBits : l.toNat = Nat.getLowBits 128 x.toNat := by
          rw [BitVec.extractLsb_toNat]
          simp only [Nat.sub_zero]
          rw [Nat.shiftRight_zero, Nat.getLowBits_eq_mod_two_pow]
        have h_h_shift_eq : h.toNat <<< 128 = Nat.getHighBits 128 x.toNat := by
          rw [Nat.shiftLeft_eq, h_h_eq_getHighBits]
          rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq]
        rw [h_h_shift_eq, h_l_eq_getLowBits]
        have h_lhs_eq_x : (x.toNat >>> 128) * 2^128 + x.toNat % 2^128 = x.toNat := by
          rw [Nat.shiftRight_eq_div_pow, mul_comm, Nat.div_add_mod]
        have h_high_lt : Nat.getHighBits 128 x.toNat < 2^256 := by
          rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq]; omega
        rw [Nat.mod_eq_of_lt h_high_lt]
        conv_lhs => rw [h_lhs_eq_x]
        rw [←Nat.num_eq_highBits_xor_lowBits (n := x.toNat) (numLowBits := 128)]
  rw [h_recon, toPoly_xor]
  simp only [Nat.reduceSub, Nat.reduceAdd, Nat.sub_zero]
  rw [BF128Ghash.toPoly_shiftLeft_no_overflow (a := to256 h) (shift := 128)
    (d := 128) (w := 256)
    (ha := h_h_lt_2_pow_128) (h_no_overflow := by omega)]
  rw [toPoly_128_extend_256];
  have h_extractH_eq_h : extractLsb 255 128 (to256 h <<< 128 ^^^ to256 l) = h := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb_toNat]
    simp only [BitVec.toNat_xor, BitVec.toNat_shiftLeft, to256_toNat]
    have h_h_lt : h.toNat < 2^128 := BitVec.isLt h
    have h_shift_mod : (h.toNat <<< 128) % 2^256 = h.toNat <<< 128 := by
      apply Nat.mod_eq_of_lt
      rw [Nat.shiftLeft_eq]; omega
    rw [h_shift_mod]
    have h_shift_xor : ((h.toNat <<< 128) ^^^ l.toNat) >>> 128 =
                       ((h.toNat <<< 128) >>> 128) ^^^ (l.toNat >>> 128) := by
      rw [Nat.shiftRight_xor_distrib]
    rw [h_shift_xor]
    have h_shift_roundtrip : (h.toNat <<< 128) >>> 128 = h.toNat := by
      rw [Nat.shiftLeft_shiftRight]
    have h_l_lt : l.toNat < 2^128 := BitVec.isLt l
    have h_l_shift_zero : l.toNat >>> 128 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    rw [h_shift_roundtrip, h_l_shift_zero]
    simp only [Nat.xor_zero]
    exact Nat.mod_eq_of_lt h_h_lt
  have h_extractL_eq_l : extractLsb 127 0 (to256 h <<< 128 ^^^ to256 l) = l := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb_toNat]
    simp only [BitVec.toNat_xor, BitVec.toNat_shiftLeft, to256_toNat]
    have h_h_lt : h.toNat < 2^128 := BitVec.isLt h
    have h_shift_mod_256 : (h.toNat <<< 128) % 2^256 = h.toNat <<< 128 := by
      apply Nat.mod_eq_of_lt
      rw [Nat.shiftLeft_eq]; omega
    rw [h_shift_mod_256]
    simp only [Nat.shiftRight_zero]
    have h_shift_mod_128 : (h.toNat <<< 128) % 2^128 = 0 := by
      rw [Nat.mod_eq_zero_of_dvd]
      use h.toNat
      rw [Nat.shiftLeft_eq, mul_comm]
    have h_mod_xor : ((h.toNat <<< 128) ^^^ l.toNat) % 2^128 =
                     ((h.toNat <<< 128) % 2^128) ^^^ (l.toNat % 2^128) := by
      rw [Nat.xor_mod_two_pow (n := 128)]
    rw [h_mod_xor, h_shift_mod_128]
    simp only [Nat.zero_xor]
    have h_l_lt : l.toNat < 2^128 := BitVec.isLt l
    exact Nat.mod_eq_of_lt h_l_lt
  rw [h_extractH_eq_h, h_extractL_eq_l]
  rw [toPoly_128_extend_256]

/-- The Algebraic Identity: A * X^128 ≡ A * R (mod P) -/
lemma poly_reduce_step (A : Polynomial (ZMod 2)) :
    (A * X^128) % ghashPoly = (A * ghashTail) % ghashPoly := by
  have h_add_eq : X^128 = ghashPoly + ghashTail := by
    rw [ghashPoly_eq_X_pow_add_tail, add_assoc]
    rw [ZMod2Poly.add_self_cancel, add_zero]
  conv_lhs => rw [h_add_eq]
  -- rw [mul_add (x := A) (y := ghashPoly) (z := ghashTail)]
  have h_mul_add_left : A * (ghashPoly + ghashTail) = A * ghashPoly + A * ghashTail := by
    rw [left_distrib]
  rw [h_mul_add_left]
  rw [CanonicalEuclideanDomain.add_mod_eq (hn := ghashPoly_ne_zero)]
  conv_lhs =>
    rw (occs := .pos [1]) [mul_comm A ghashPoly]
    rw [CanonicalEuclideanDomain.mul_mod_eq_zero_of_mod_dvd (hn := ghashPoly_ne_zero)
      (h_mod_eq_zero := by rw [EuclideanDomain.mod_self])]
    rw [zero_add]
    rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := ghashPoly_ne_zero)]

def fold_step (prod : B256) : B256 :=
  let h := prod.extractLsb 255 128
  let l := prod.extractLsb 127 0
  clMul (to256 h) (to256 R_val) ^^^ (to256 l)

/-- Modular Reduction using Folding (Algebraic).
  Fast O(1) reduction replacing long division.
  Uses the property X^128 ≡ X^7 + X^2 + X + 1 (mod P). -/
def reduce_clMul (prod : B256) : B128 :=
  let acc := fold_step prod
  let res := fold_step acc
  res.extractLsb 127 0

/-- One fold preserves the value modulo P. -/
lemma fold_step_mod_eq (x : B256) :
    toPoly (fold_step x) % ghashPoly = toPoly x % ghashPoly := by
  unfold fold_step
  let h := x.extractLsb 255 128
  let l := x.extractLsb 127 0
  rw [toPoly_xor]
  rw [toPoly_clMul_no_overflow (da := 128) (db := 8)]
  · rw [toPoly_128_extend_256, toPoly_128_extend_256, R_val_eq_ghashTail, toPoly_128_extend_256]
    rw [toPoly_split_256 x]
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := ghashPoly_ne_zero)]
    conv_rhs => rw [CanonicalEuclideanDomain.add_mod_eq (hn := ghashPoly_ne_zero)]
    have h_first_eq : (toPoly (extractLsb 255 128 x) * ghashTail) % ghashPoly =
                      (toPoly (extractLsb 255 128 x) * X^128) % ghashPoly := by
      symm; apply poly_reduce_step
    grind
  · rw [to256_toNat]; omega
  · rw [to256_toNat]; dsimp only [R_val, reduceToNat, Nat.reducePow]; omega
  · norm_num

/-- Main Theorem: reduce_clMul correctly computes modulo P. -/
lemma reduce_clMul_correct (prod : B256) :
    toPoly (reduce_clMul prod) = toPoly prod % ghashPoly := by
  dsimp [reduce_clMul]
  have h_equiv : toPoly (fold_step (fold_step prod)) % ghashPoly = toPoly prod % ghashPoly := by
    rw [fold_step_mod_eq, fold_step_mod_eq]
  let acc := fold_step prod
  let res := fold_step acc
  have h_acc_bound : acc.toNat < 2^135 := by
    dsimp only [acc]
    unfold fold_step
    let h := prod.extractLsb 255 128
    let l := prod.extractLsb 127 0
    have h_toPoly_l_deg_lt := toPoly_degree_lt_w (by omega) l
    let term1 := clMul (to256 h) (to256 R_val)
    have h_term1_deg : (toPoly term1).degree < 135 := by
      rw [toPoly_clMul_no_overflow (da := 128) (db := 8)]
      · apply (Polynomial.degree_mul_le _ _).trans_lt
        rw [toPoly_128_extend_256, toPoly_128_extend_256]
        have deg_h : (toPoly h).degree < 128 := toPoly_degree_lt_w (by omega) h
        have deg_R : (toPoly R_val).degree < 8 := by
          apply toPoly_degree_of_lt_two_pow;
          dsimp only [R_val, reduceToNat, Nat.reducePow]
          omega
        have h_deg_h_le : (toPoly h).degree ≤ (127 : WithBot ℕ) := by
          have h_deg_h_nat : (toPoly h).degree < (128 : WithBot ℕ) := deg_h
          by_cases h_deg_bot : (toPoly h).degree = ⊥
          · rw [h_deg_bot]; exact bot_le
          · obtain ⟨n, h_n_eq⟩ := WithBot.ne_bot_iff_exists.mp h_deg_bot
            rw [←h_n_eq] at h_deg_h_nat
            norm_cast at h_deg_h_nat
            rw [h_n_eq.symm]
            change (n : WithBot ℕ) ≤ (127 : ℕ)
            change (n : WithBot ℕ) < (128 : ℕ) at h_deg_h_nat
            norm_cast at h_deg_h_nat ⊢
            exact Nat.le_of_lt_succ h_deg_h_nat
        have h_deg_R_le : (toPoly R_val).degree ≤ (7 : WithBot ℕ) := by
          have h_deg_R_nat : (toPoly R_val).degree < (8 : WithBot ℕ) := deg_R
          by_cases h_deg_bot : (toPoly R_val).degree = ⊥
          · rw [h_deg_bot]; exact bot_le
          · obtain ⟨n, h_n_eq⟩ := WithBot.ne_bot_iff_exists.mp h_deg_bot
            rw [←h_n_eq] at h_deg_R_nat
            rw [h_n_eq.symm]
            change (n : WithBot ℕ) ≤ (7 : ℕ)
            change (n : WithBot ℕ) < (8 : ℕ) at h_deg_R_nat
            norm_cast at h_deg_R_nat ⊢
            exact Nat.le_of_lt_succ h_deg_R_nat
        apply lt_of_le_of_lt (add_le_add h_deg_h_le h_deg_R_le)
        norm_cast
      · rw [to256_toNat]; apply BitVec.toNat_lt_twoPow_of_le (by omega)
      · rw [to256_toNat]; simp only [R_val, toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        Nat.reduceLT]
      · norm_num
    have h_term1_lt : term1.toNat < 2^135 := by
      apply BitVec_lt_two_pow_of_toPoly_degree_lt term1 h_term1_deg
    have h_acc_deg : (toPoly (term1 ^^^ to256 l)).degree < 135 := by
      rw [toPoly_xor]
      apply (Polynomial.degree_add_le _ _).trans_lt
      rw [max_lt_iff]
      constructor
      · exact h_term1_deg
      · rw [toPoly_128_extend_256]
        by_cases h_deg_bot : (toPoly l).degree = ⊥
        · rw [h_deg_bot]
          exact bot_lt_of_lt h_term1_deg
        · -- ⊢ (toPoly l).degree < 135
          obtain ⟨n, h_n_eq⟩ := WithBot.ne_bot_iff_exists.mp h_deg_bot
          rw [←h_n_eq] at h_toPoly_l_deg_lt ⊢
          change (n : WithBot ℕ) < (135 : ℕ)
          change (n : WithBot ℕ) < (128 : ℕ) at h_toPoly_l_deg_lt
          norm_cast at ⊢ h_toPoly_l_deg_lt
          apply Nat.lt_trans h_toPoly_l_deg_lt (by omega)
    apply BitVec_lt_two_pow_of_toPoly_degree_lt (term1 ^^^ to256 l) h_acc_deg
  have h_h2_bound : (acc.extractLsb 255 128).toNat < 2^7 := by
    rw [BitVec.extractLsb_toNat]
    apply Nat.mod_lt_of_lt
    · rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      rw [←Nat.pow_add]; apply lt_of_lt_of_le h_acc_bound; norm_num
  have h_res_lt_128 : (toPoly res).degree < 128 := by
    dsimp only [acc, res]
    unfold fold_step
    let h2 := acc.extractLsb 255 128
    let l2 := acc.extractLsb 127 0
    let term2 := clMul (to256 h2) (to256 R_val)

    rw [toPoly_xor, toPoly_clMul_no_overflow (da := 7) (db := 8)]
    · apply (Polynomial.degree_add_le _ _).trans_lt
      rw [max_lt_iff]
      constructor
      · apply (Polynomial.degree_mul_le _ _).trans_lt
        rw [toPoly_128_extend_256, toPoly_128_extend_256]
        have deg_h2 : (toPoly h2).degree < 7 := toPoly_degree_of_lt_two_pow _ h_h2_bound
        have deg_R : (toPoly R_val).degree < 8 := by
          apply toPoly_degree_of_lt_two_pow; dsimp only [R_val, reduceToNat, Nat.reducePow]; omega
        have h_deg_h2_le : (toPoly h2).degree ≤ (6 : WithBot ℕ) := by
          by_cases h_deg_bot : (toPoly h2).degree = ⊥
          · rw [h_deg_bot]; exact bot_le
          · obtain ⟨n, h_n_eq⟩ := WithBot.ne_bot_iff_exists.mp h_deg_bot
            rw [←h_n_eq] at deg_h2
            norm_cast at deg_h2
            rw [h_n_eq.symm]
            change (n : WithBot ℕ) ≤ (6 : ℕ)
            change (n : WithBot ℕ) < (7 : ℕ) at deg_h2
            norm_cast at deg_h2 ⊢
            exact Nat.le_of_lt_succ deg_h2
        have h_deg_R_le : (toPoly R_val).degree ≤ (7 : WithBot ℕ) := by
          by_cases h_deg_bot : (toPoly R_val).degree = ⊥
          · rw [h_deg_bot]; exact bot_le
          · obtain ⟨n, h_n_eq⟩ := WithBot.ne_bot_iff_exists.mp h_deg_bot
            rw [←h_n_eq] at deg_R
            rw [h_n_eq.symm]
            change (n : WithBot ℕ) ≤ (7 : ℕ)
            change (n : WithBot ℕ) < (8 : ℕ) at deg_R
            norm_cast at deg_R ⊢
            exact Nat.le_of_lt_succ deg_R
        apply lt_of_le_of_lt (add_le_add h_deg_h2_le h_deg_R_le)
        norm_cast
      · rw [toPoly_128_extend_256]
        apply toPoly_degree_of_lt_two_pow
        exact BitVec.isLt l2
    · rw [to256_toNat]; exact h_h2_bound
    · rw [to256_toNat]; dsimp only [R_val, reduceToNat, Nat.reducePow]; omega
    · norm_num
  have h_extract : toPoly (res.extractLsb 127 0) = toPoly res := by
    have h_res_eq : res = to256 (res.extractLsb 127 0) := by
      dsimp only [to256]
      refine eq_of_toNat_eq ?_
      simp only [truncate_eq_setWidth, toNat_setWidth, extractLsb_toNat, Nat.shiftRight_zero,
        tsub_zero, Nat.reduceAdd]
      rw [Nat.mod_eq_of_lt (h := by omega)]
      symm
      apply Nat.mod_eq_of_lt (h := by
        apply BitVec_lt_two_pow_of_toPoly_degree_lt
        exact h_res_lt_128
      )
    conv_rhs => rw [h_res_eq]
    rw [toPoly_128_extend_256]
  rw [h_extract]
  have h_mod_id : toPoly res % ghashPoly = toPoly res := by
    rw [Polynomial.mod_eq_self_iff (hq0 := ghashPoly_ne_zero)]
    rw [ghashPoly_degree]
    exact h_res_lt_128
  rw [←h_mod_id, h_equiv]

end CarryLessMultiplicationReduction

section AddCommGroupInstance

instance : Zero ConcreteBF128Ghash where zero := 0#128
instance : One ConcreteBF128Ghash where one := 1#128
instance : Add ConcreteBF128Ghash where add a b := a ^^^ b
instance : Neg ConcreteBF128Ghash where neg a := a
instance : Sub ConcreteBF128Ghash where sub a b := a ^^^ b

instance : Mul ConcreteBF128Ghash where
  mul a b :=
    let prod := clMul (to256 a) (to256 b)
    reduce_clMul prod

-- -----------------------------------------------------------------------------
-- 4. AddCommGroup Instance
-- -----------------------------------------------------------------------------

lemma add_assoc (a b c : ConcreteBF128Ghash) : a + b + c = a + (b + c) := by
  exact BitVec.xor_assoc a b c

lemma add_comm (a b : ConcreteBF128Ghash) : a + b = b + a := by
  exact BitVec.xor_comm a b

lemma add_zero (a : ConcreteBF128Ghash) : a + 0 = a := by
  apply BitVec.xor_zero (w := 128)

lemma zero_add (a : ConcreteBF128Ghash) : 0 + a = a := by
  rw [add_comm]
  apply BitVec.xor_zero (w := 128)

lemma neg_add_cancel (a : ConcreteBF128Ghash) : -a + a = 0 := by
  change a ^^^ a = 0
  apply BitVec.xor_self

lemma add_self_cancel (a : ConcreteBF128Ghash) : a + a = 0 := by
  apply BitVec.xor_self

lemma nsmul_succ (n : ℕ) (x : ConcreteBF128Ghash) :
    (if (n + 1) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = (if n % 2 = 0 then (0 : ConcreteBF128Ghash) else x) + x := by
  have h_mod : (n + 1) % 2 = (n % 2 + 1) % 2 := Nat.add_mod n 1 2
  by_cases h : n % 2 = 0
  · rw [h, Nat.zero_add] at h_mod
    rw [h]; simp only [ofNat_eq_ofNat, ↓reduceIte]
    have h_mod: (n + 1) % 2 = 1 := by omega
    rw [h_mod]; simp only [one_ne_zero, ↓reduceIte]
    dsimp only [HAdd.hAdd, Add.add]
    exact Eq.symm BitVec.zero_xor
  · have h1 : n % 2 = 1 := by
      have := Nat.mod_two_eq_zero_or_one n
      exact Nat.mod_two_ne_zero.mp h
    rw [h1] at h_mod ⊢
    have h_mod: (n + 1) % 2 = 0 := by omega
    rw [h_mod]; simp only [↓reduceIte, ofNat_eq_ofNat, one_ne_zero]
    dsimp only [HAdd.hAdd, Add.add]; simp only [BitVec.xor_self]

lemma zsmul_succ (n : ℕ) (x : ConcreteBF128Ghash) :
    (if (n + 1 : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = (if (n : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x) + x := by
  norm_cast
  exact nsmul_succ n x

lemma int_neg_mod_two (n : ℤ) : (-n) % 2 = n % 2 := by
  simp only [Int.neg_emod_two]

lemma zsmul_neg (n : ℕ) (x : ConcreteBF128Ghash) :
    (if (Int.negSucc n) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = -(if (n + 1 : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x) := by
  have h_neg : Int.negSucc n = - (n + 1 : ℤ) := rfl
  rw [h_neg]
  rw [int_neg_mod_two (n + 1)]
  simp
  rfl

/-- In characteristic 2, `n • x = x` if `n` is odd, and `n • x = 0` if `n` is even.
This is because `2 • x = x + x = 0` in any ring of characteristic 2. -/
instance : AddCommGroup ConcreteBF128Ghash where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  nsmul := fun n x => if n % 2 = 0 then 0 else x
  zsmul := fun n x => if n % 2 = 0 then 0 else x
  nsmul_zero := fun x => by
    simp only [Nat.zero_mod, ↓reduceIte, ofNat_eq_ofNat]
  nsmul_succ := nsmul_succ
  zsmul_zero' := fun x => by
    simp only [EuclideanDomain.zero_mod, ↓reduceIte, ofNat_eq_ofNat]
  zsmul_succ' := zsmul_succ
  zsmul_neg' := zsmul_neg

instance : Mul ConcreteBF128Ghash where
  mul a b :=
    let prod := clMul (to256 a) (to256 b)
    reduce_clMul prod

end AddCommGroupInstance

section RingInstance_and_PolyQuotient

abbrev PolyQuot := AdjoinRoot ghashPoly

noncomputable def toQuot (a : ConcreteBF128Ghash) : PolyQuot :=
  AdjoinRoot.mk ghashPoly (toPoly a)

/-- Frobenius property: a^(2^128) = a in GF(2^128). -/
lemma toQuot_pow_card (a : ConcreteBF128Ghash) : (toQuot a)^(2^128) = toQuot a := by
  rw [←BF128Ghash_card]
  rw [FiniteField.pow_card (toQuot a)]

/-- Injectivity of `toQuot`.
  If two elements map to the same quotient value, they must be equal.
  Proof uses deg(toPoly a) < 128 and P has degree 128. -/
lemma toQuot_injective : Function.Injective toQuot := by
  intro a b h
  unfold toQuot at h
  have h_sub : toPoly a - toPoly b = toPoly (a ^^^ b) := by
    rw [toPoly_xor]
    ring_nf
    exact ZMod2Poly.sub_eq_add (toPoly a) (toPoly b)
  let diff := a ^^^ b
  have h_deg : (toPoly diff).degree < 128 := by
    apply toPoly_degree_lt_w (w:=128) (by norm_num)
  have h_dvd : ghashPoly ∣ (toPoly a - toPoly b) := by
    rw [AdjoinRoot.mk_eq_mk] at h
    exact h
  have h_zero : toPoly diff = 0 := by
    by_contra h_nz
    have h_diff_nz : toPoly a - toPoly b ≠ 0 := by
      rw [h_sub]; exact h_nz
    have h_deg_poly : ghashPoly.degree ≤ (toPoly a - toPoly b).degree :=
      Polynomial.degree_le_of_dvd (h1 := h_dvd) (h2 := h_diff_nz)
    have h_eq_deg : (toPoly a - toPoly b).degree = (toPoly diff).degree := by
      rw [h_sub.symm]
    rw [ghashPoly_degree] at h_deg_poly
    rw [h_eq_deg] at h_deg_poly
    exact not_le_of_gt h_deg h_deg_poly
  have h_diff_eq_zero : diff = 0 := by
    by_contra h_nz
    have h_diff_ne_zero : diff ≠ 0 := by omega
    rw [←toPoly_ne_zero_iff_ne_zero (v := diff)] at h_diff_ne_zero
    exact h_diff_ne_zero h_zero
  exact eq_of_sub_eq_zero h_diff_eq_zero

lemma toQuot_add (a b : ConcreteBF128Ghash) : toQuot (a + b) = toQuot a + toQuot b := by
  unfold toQuot
  have h_add_eq_xor : a + b = a ^^^ b := rfl
  rw [h_add_eq_xor, toPoly_xor]
  exact map_add (AdjoinRoot.mk ghashPoly) (toPoly a) (toPoly b)

lemma toQuot_zero : toQuot 0 = 0 := by
  simp [toQuot, toPoly_zero_eq_zero]

lemma toQuot_one : toQuot 1 = 1 := by
  have h_pos : 128 > 0 := by norm_num
  simp [toQuot, toPoly_one_eq_one h_pos, map_one]

lemma eq_of_toQuot_eq {a b : ConcreteBF128Ghash} (h : toQuot a = toQuot b) : a = b :=
  toQuot_injective h

lemma toQuot_ne_zero (a : ConcreteBF128Ghash) (h_a_ne_zero : a ≠ 0) : toQuot a ≠ 0 := by
  by_contra h
  rw [← toQuot_zero] at h
  let h_a_eq_0 := eq_of_toQuot_eq (h := h)
  exact h_a_ne_zero h_a_eq_0

/-- Multiplication homomorphism: `clMul + reduce_clMul` implements polynomial multiplication
mod P. -/
lemma toQuot_mul (a b : ConcreteBF128Ghash) : toQuot (a * b) = toQuot a * toQuot b := by
  unfold toQuot
  have h_clMul : toPoly (clMul (to256 a) (to256 b)) = toPoly (to256 a) * toPoly (to256 b) := by
    apply toPoly_clMul_no_overflow (da := 128) (db := 128)
    · rw [to256_toNat]; exact BitVec.toNat_lt_twoPow_of_le (n := 128) (by omega)
    · rw [to256_toNat]; exact BitVec.toNat_lt_twoPow_of_le (n := 128) (by omega)
    · norm_num
  rw [toPoly_128_extend_256, toPoly_128_extend_256] at h_clMul
  have h_reduce : toPoly (reduce_clMul (clMul (to256 a) (to256 b))) =
                  toPoly (clMul (to256 a) (to256 b)) % ghashPoly := by
    apply reduce_clMul_correct
  change AdjoinRoot.mk ghashPoly (toPoly (reduce_clMul (clMul (to256 a) (to256 b)))) =
         AdjoinRoot.mk ghashPoly (toPoly a) * AdjoinRoot.mk ghashPoly (toPoly b)
  rw [h_reduce, h_clMul, ← map_mul (AdjoinRoot.mk ghashPoly), AdjoinRoot.mk_eq_mk]
  have h_div : ghashPoly ∣ ((toPoly a * toPoly b) % ghashPoly) - (toPoly a * toPoly b) := by
    apply dvd_sub_comm.mp
    apply CanonicalEuclideanDomain.dvd_sub_mod (b := ghashPoly)
  grind

-- Ring axioms verified via toQuot isomorphism
lemma mul_assoc (a b c : ConcreteBF128Ghash) : a * b * c = a * (b * c) := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_mul, toQuot_mul, toQuot_mul]
  apply _root_.mul_assoc

lemma one_mul (a : ConcreteBF128Ghash) : 1 * a = a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  exact _root_.one_mul (toQuot a)

lemma mul_one (a : ConcreteBF128Ghash) : a * 1 = a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  exact _root_.mul_one (toQuot a)

lemma left_distrib (a b c : ConcreteBF128Ghash) : a * (b + c) = a * b + a * c := by
  apply toQuot_injective
  rw [toQuot_add, toQuot_mul, toQuot_add, toQuot_mul, toQuot_mul]
  rw [←mul_add (a := toQuot a) (b := toQuot b) (c := toQuot c)]

lemma right_distrib (a b c : ConcreteBF128Ghash) : (a + b) * c = a * c + b * c := by
  apply toQuot_injective
  rw [toQuot_add, toQuot_mul, toQuot_add, toQuot_mul, toQuot_mul]
  rw [←add_mul (a := toQuot a) (b := toQuot b) (c := toQuot c)]

lemma zero_mul (a : ConcreteBF128Ghash) : 0 * a = 0 := by
  apply toQuot_injective
  simp only [toQuot_mul, toQuot_zero]
  simp only [MulZeroClass.zero_mul]

lemma mul_zero (a : ConcreteBF128Ghash) : a * 0 = 0 := by
  apply toQuot_injective
  simp only [toQuot_mul, toQuot_zero, MulZeroClass.mul_zero]

-- Natural number casting: even numbers → 0, odd numbers → 1
def natCast (n : ℕ) : ConcreteBF128Ghash := if n % 2 = 0 then 0 else 1

instance : NatCast ConcreteBF128Ghash where
  natCast := natCast

@[simp] lemma natCast_eq (n : ℕ) : (↑n : ConcreteBF128Ghash) = natCast n := rfl

lemma natCast_zero : natCast 0 = 0 := by simp [natCast]

lemma natCast_succ (n : ℕ) : natCast (n + 1) = natCast n + 1 := by
  simp [natCast]
  by_cases h : n % 2 = 0
  · -- If n is even, then n+1 is odd
    have h_succ : (n + 1) % 2 = 1 := by omega
    simp [h, h_succ]
  · -- If n is odd, then n+1 is even
    have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [h, h_succ]; norm_num;
    rw [add_self_cancel]; rfl

-- Integer casting: same as natural casting (mod 2)
def intCast (n : ℤ) : ConcreteBF128Ghash := if n % 2 = 0 then 0 else 1

instance : IntCast ConcreteBF128Ghash where
  intCast := intCast

lemma intCast_ofNat (n : ℕ) : intCast (n : ℤ) = natCast n := by
  simp [intCast, natCast]
  by_cases h : n % 2 = 0
  · have h_int : (n : ℤ) % 2 = 0 := by norm_cast;
    simp [h, h_int]
  · have h_n : n % 2 = 1 := by omega
    have h_int : (n : ℤ) % 2 = 1 := by norm_cast;
    simp only [h_n, one_ne_zero, ↓reduceIte, ite_eq_right_iff, zero_eq_one_iff, OfNat.ofNat_ne_zero,
      imp_false, Int.two_dvd_ne_zero, h_int]

lemma intCast_negSucc (n : ℕ) : intCast (Int.negSucc n) = -(↑(n + 1) : ConcreteBF128Ghash) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · have h_neg : ( - (n + 1 : ℤ)) % 2 = 0 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ, h_neg]
    have h_nat : (↑(n + 1) : ConcreteBF128Ghash) = (0 : ConcreteBF128Ghash) := by
      simp only [natCast_eq, natCast, h_mod]; rfl
    rw [h_nat]; rfl
  · have h_neg : ( - (n + 1 : ℤ)) % 2 = 1 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ, h_neg, if_neg (by simp)]
    have h_nat : (↑(n + 1) : ConcreteBF128Ghash) = (1 : ConcreteBF128Ghash) := by
      simp only [natCast_eq, natCast, h_mod]; rfl
    rw [h_nat]; rfl

instance : Ring ConcreteBF128Ghash where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  natCast := natCast
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  intCast := intCast
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc

end RingInstance_and_PolyQuotient

section ItohTsujiiInversion

/-- Squaring in GF(2^128). -/
def square (a : B128) : B128 := a * a

/-- Computes a^(2^k) by repeated squaring. -/
def pow_2k (a : B128) (k : Nat) : B128 :=
  match k with
  | 0 => a
  | n + 1 => pow_2k (square a) n

/-- Inversion using Itoh-Tsujii Algorithm.
  Computes a^-1 = a^(2^128 - 2) = (a^(2^127 - 1))^2.
  We use an addition chain for 127 = 2^7 - 1. -/
def inv_itoh_tsujii (a : B128) : B128 :=
  if a.toNat = 0 then 0#128 else
    -- Addition chain for 127:
    -- 1 -> 2 -> 3 -> 6 -> 7 -> 14 -> 15 -> 30 -> 31 -> 62 -> 63 -> 126 -> 127
    let u1 := a                         -- 2^1 - 1
    let u2 := (pow_2k u1 1) * u1        -- 2^2 - 1
    let u3 := (pow_2k u2 1) * u1        -- 2^3 - 1
    let u6 := (pow_2k u3 3) * u3        -- 2^6 - 1
    let u7 := (pow_2k u6 1) * u1        -- 2^7 - 1
    let u14 := (pow_2k u7 7) * u7       -- 2^14 - 1
    let u15 := (pow_2k u14 1) * u1      -- 2^15 - 1
    let u30 := (pow_2k u15 15) * u15    -- 2^30 - 1
    let u31 := (pow_2k u30 1) * u1      -- 2^31 - 1
    let u62 := (pow_2k u31 31) * u31    -- 2^62 - 1
    let u63 := (pow_2k u62 1) * u1      -- 2^63 - 1
    let u126 := (pow_2k u63 63) * u63   -- 2^126 - 1
    let u127 := (pow_2k u126 1) * u1    -- 2^127 - 1
    square u127                         -- 2^128 - 2

instance : Inv ConcreteBF128Ghash where
  inv a := inv_itoh_tsujii a

lemma inv_zero : (0 : ConcreteBF128Ghash)⁻¹ = 0 := by
  simp [Inv.inv]
  unfold inv_itoh_tsujii
  simp
lemma toQuot_square (a : ConcreteBF128Ghash) : toQuot (square a) = (toQuot a)^2 := by
  unfold square
  rw [toQuot_mul]; exact Eq.symm (pow_two (toQuot a))

lemma toQuot_pow_2k (a : ConcreteBF128Ghash) (k : Nat) :
    toQuot (pow_2k a k) = (toQuot a)^(2^k) := by
  induction k generalizing a with
  | zero =>
    simp only [pow_2k, pow_zero, pow_one]
  | succ n ih =>
    simp only [pow_2k]
    rw [ih, toQuot_square]
    rw [← pow_mul, pow_succ, mul_comm]

/-- The target value for step k: a^(2^k - 1) -/
noncomputable def target_val (a : PolyQuot) (k : ℕ) : PolyQuot := a ^ (2^k - 1)

/-- Fundamental Itoh-Tsujii Step Lemma:
  If `x = a^(2^n - 1)` and `y = a^(2^m - 1)`, then `(x^(2^m)) * y = a^(2^(n+m) - 1)`.
  This corresponds to the code `(pow_2k u_n m) * u_m`. -/
lemma itoh_tsujii_step {a x y : PolyQuot} {n m : ℕ}
    (hn : n > 0) (hm : m > 0) (hx : x = target_val a n) (hy : y = target_val a m) :
    x^(2^m) * y = target_val a (n + m) := by
  rw [hx, hy, target_val, target_val]
  rw [←pow_mul]
  by_cases ha : a = 0
  · simp only [ha, target_val]
    have h_pos_left1 : (2^n - 1) * 2^m ≠ 0 := by
      apply Nat.mul_ne_zero
      · apply Nat.sub_ne_zero_of_lt
        have h_one_lt_n : 1 < 2^n := by
          apply Nat.one_lt_pow;
          · omega
          · norm_num
        exact h_one_lt_n
      · norm_num
    have h_pos_left2 : 2^m - 1 ≠ 0 := by
      apply Nat.sub_ne_zero_of_lt
      have h_one_lt_m : 1 < 2^m := by
        apply Nat.one_lt_pow
        · omega
        · norm_num
      exact h_one_lt_m
    have h_pos_right : 2^(n+m) - 1 ≠ 0 := by
      apply Nat.sub_ne_zero_of_lt
      have h_one_lt : 1 < 2^(n+m) := by
        apply Nat.one_lt_pow
        · omega
        · norm_num
      exact h_one_lt
    simp only [zero_pow h_pos_left1, zero_pow h_pos_left2, MulZeroClass.mul_zero,
      zero_pow h_pos_right]
  · rw [←pow_add]
    congr 1
    rw [pow_add, Nat.sub_mul, Nat.one_mul]
    have h_one_le_2_pow_m : 1 ≤ 2 ^ m := by
      exact Nat.one_le_two_pow
    conv_lhs => rw [←Nat.add_sub_assoc (h := h_one_le_2_pow_m)]
    have h_le : 2 ^ m ≤ 2 ^ n * 2 ^ m := by
      conv_lhs => rw [←Nat.one_mul (2 ^ m)]
      apply Nat.mul_le_mul_right
      exact Nat.one_le_two_pow
    rw [Nat.sub_add_cancel (h := h_le)]

lemma toQuot_inv_itoh_tsujii (a : ConcreteBF128Ghash) (h_ne : a ≠ 0) :
    toQuot (inv_itoh_tsujii a) = (toQuot a)^(2^128 - 2) := by
  unfold inv_itoh_tsujii
  let q := toQuot a
  have h_u1 : toQuot a = target_val q 1 := by
    simp only [target_val, pow_one, Nat.add_one_sub_one]; rfl
  have h_u2 : toQuot ((pow_2k a 1) * a) = target_val q 2 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u1 h_u1
  let u2 := (pow_2k a 1) * a
  have h_u3 : toQuot ((pow_2k u2 1) * a) = target_val q 3 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u2 h_u1
  let u3 := (pow_2k u2 1) * a
  have h_u6 : toQuot ((pow_2k u3 3) * u3) = target_val q 6 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u3 h_u3
  let u6 := (pow_2k u3 3) * u3
  have h_u7 : toQuot ((pow_2k u6 1) * a) = target_val q 7 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u6 h_u1
  let u7 := (pow_2k u6 1) * a
  have h_u14 : toQuot ((pow_2k u7 7) * u7) = target_val q 14 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u7 h_u7
  let u14 := (pow_2k u7 7) * u7
  have h_u15 : toQuot ((pow_2k u14 1) * a) = target_val q 15 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u14 h_u1
  let u15 := (pow_2k u14 1) * a
  have h_u30 : toQuot ((pow_2k u15 15) * u15) = target_val q 30 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u15 h_u15
  let u30 := (pow_2k u15 15) * u15
  have h_u31 : toQuot ((pow_2k u30 1) * a) = target_val q 31 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u30 h_u1
  let u31 := (pow_2k u30 1) * a
  have h_u62 : toQuot ((pow_2k u31 31) * u31) = target_val q 62 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u31 h_u31
  let u62 := (pow_2k u31 31) * u31
  have h_u63 : toQuot ((pow_2k u62 1) * a) = target_val q 63 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u62 h_u1
  let u63 := (pow_2k u62 1) * a
  have h_u126 : toQuot ((pow_2k u63 63) * u63) = target_val q 126 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u63 h_u63
  let u126 := (pow_2k u63 63) * u63
  have h_u127 : toQuot ((pow_2k u126 1) * a) = target_val q 127 := by
    simp only [toQuot_mul, toQuot_pow_2k]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u126 h_u1
  let u127 := (pow_2k u126 1) * a
  have h_toNat_ne_zero : a.toNat ≠ 0 := by
    by_contra h_eq_zero
    have h_a_eq_zero : a = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [h_eq_zero, ofNat_eq_ofNat, toNat_ofNat, Nat.reducePow, Nat.zero_mod]
    exact h_ne h_a_eq_zero
  simp only [if_neg h_toNat_ne_zero]
  rw [toQuot_square, h_u127]
  unfold target_val
  rw [←pow_mul]
  congr 1

end ItohTsujiiInversion

section DivisionRing_Field_Instances

lemma exists_pair_ne : ∃ x y : ConcreteBF128Ghash, x ≠ y :=
  ⟨0#128, 1#128, by simp only [ne_eq, zero_eq_one_iff, OfNat.ofNat_ne_zero, not_false_eq_true]⟩

lemma mul_inv_cancel (a : ConcreteBF128Ghash) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  have h_inv : a⁻¹ = inv_itoh_tsujii a := rfl
  rw [h_inv, toQuot_inv_itoh_tsujii a h]
  rw [←pow_succ']
  have h_exp_eq : 2 ^ 128 - 2 + 1 = 2 ^ 128 - 1 := by omega
  rw [h_exp_eq]
  have h_pow_pred_eq : toQuot a ^ (2 ^ 128 - 1) = (toQuot a)^(2^128) * (toQuot a)⁻¹ := by
    rw [pow_sub₀ (a := toQuot a) (m := 2 ^ 128) (n := 1) (ha := toQuot_ne_zero a h) (h := by omega)]
    rw [pow_one]
  rw [h_pow_pred_eq, toQuot_pow_card]
  have h_quot_ne_zero : toQuot a ≠ 0 := by
    contrapose! h
    rw [← toQuot_zero] at h
    exact toQuot_injective h
  field_simp [h_quot_ne_zero]

instance instDivConcreteBF128Ghash : Div (ConcreteBF128Ghash) where
  div a b := a * (Inv.inv b)

instance instHDivConcreteBF128Ghash : HDiv (ConcreteBF128Ghash) (ConcreteBF128Ghash)
  (ConcreteBF128Ghash) where hDiv a b := a * (Inv.inv b)

lemma div_eq_mul_inv (a b : ConcreteBF128Ghash) : a / b = a * b⁻¹ := by rfl

instance : DivisionRing ConcreteBF128Ghash where
  toRing := inferInstance
  inv := Inv.inv
  exists_pair_ne := exists_pair_ne
  mul_inv_cancel := mul_inv_cancel
  inv_zero := inv_zero
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)
  toDiv := instDivConcreteBF128Ghash

lemma mul_comm (a b : ConcreteBF128Ghash) : a * b = b * a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_mul]
  exact _root_.mul_comm (toQuot a) (toQuot b)

instance instFieldConcreteBF128Ghash : Field ConcreteBF128Ghash where
  toDivisionRing := inferInstance
  mul_comm := mul_comm

end DivisionRing_Field_Instances

end BF128Ghash
