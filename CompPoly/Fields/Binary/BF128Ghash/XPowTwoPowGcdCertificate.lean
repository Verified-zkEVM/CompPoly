/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.BF128Ghash.XPowTwoPowModCertificate

/-!
# XPowTwoPow Gcd Certificate

Certificates for gcd conditions in the BF128Ghash field.
-/

namespace BF128Ghash
open Polynomial

set_option maxRecDepth 1500

@[reducible]
def gcd_a_0_val : B256 := BitVec.ofNat 256 340282366920938463463374607431768211591
@[reducible]
def gcd_b_0_val : B256 := BitVec.ofNat 256 129460184901158119860735353079755610612

lemma toPoly_gcd_b_0_val_mod_ghashPoly_eq_gcd_b_0_val :
    (toPoly gcd_b_0_val) % ghashPoly = toPoly gcd_b_0_val := by
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact ghashPoly_ne_zero)]
  rw [toPoly]; simp_rw [BitVec.getLsb]
  have h_gcd_b_0_val_lt : 129460184901158119860735353079755610612 < 2^128 := by omega
  have h_256_eq: 256 = 128 + 128 := by rfl
  conv_lhs => rw! (castMode:=.all) [h_256_eq]
  rw [Fin.sum_univ_add]
  conv_rhs => rw [ghashPoly_degree]
  -- conv_lhs => rw [←Finset.sum_add_distrib]
  simp only [Nat.reduceAdd, Fin.coe_castAdd, Fin.natAdd_eq_addNat, Fin.coe_addNat]
  have h_lt: (BitVec.toNat gcd_b_0_val) < 2^128 := by apply h_gcd_b_0_val_lt
  -- ∑ ... + ∑ ... < 128 => the second sum is actually 0
  have h_2_pow_x_gt_0: ∀ x, 2^x > 0 := fun x => by simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos]
  conv_lhs =>
    enter [1, 2, 2, x];
    rw [Nat.testBit_lt_two_pow (x := BitVec.toNat gcd_b_0_val) (i := x + 128)
      (lt := by
        apply lt_of_lt_of_le h_lt
        rw [pow_add, mul_comm];
        simp only [Nat.reducePow, Nat.ofNat_pos, le_mul_iff_one_le_right];
        exact h_2_pow_x_gt_0 ↑x
      )]
    simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [Finset.sum_const_zero, add_zero]
  -- ⊢ (∑ x, if (BitVec.toNat gcd_b_0_val).testBit ↑x = true then X ^ ↑x else 0).degree < 128
  have h_bitVec_toNat: BitVec.toNat gcd_b_0_val
    = BitVec.toNat 129460184901158119860735353079755610612#128 := by rfl
  simp_rw [h_bitVec_toNat]
  change (toPoly 129460184901158119860735353079755610612#128).degree < 128
  exact toPoly_degree_lt_w (w := 128) (h_w_pos := by omega) (v := _)

lemma gcd_start_reduction :
    EuclideanDomain.gcd ((X^(2^64)) + X) ghashPoly =
  EuclideanDomain.gcd ghashPoly (toPoly gcd_b_0_val) := by
  -- 1. Swap order: gcd(A, B) = gcd(B, A)
  rw [ZMod2Poly.euclidean_gcd_comm]
  -- 2. Reduce LHS mod RHS: gcd(B, A) = gcd(B % A, A)
  rw [EuclideanDomain.gcd_val]
  -- 3. Simplify (X^(2^64) + X) % P
  --    = (X^(2^64) % P + X % P) % P
  --    Since deg(X) < 128, X % P =  X
  --    We rely on the calculated value of r64 being correct.
  have h_r64 : X^(2^64) % ghashPoly =
    toPoly (BitVec.ofNat 128 129460184901158119860735353079755610614) := by
    rw [X_pow_2_pow_64_eq];
  conv_lhs =>
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := by exact ghashPoly_ne_zero), h_r64]
    rw [ZMod2Poly.euclidean_gcd_comm]
  rw [X_mod_ghashPoly, ←X_ZMod2Poly_eq_X, X_ZMod2Poly, ←toPoly_xor]
  dsimp only [X_val, BitVec.reduceXOr]
  rw [←toPoly_gcd_b_0_val_mod_ghashPoly_eq_gcd_b_0_val]
  conv_rhs => dsimp only [gcd_b_0_val]
  have h_toPoly_eq: toPoly 129460184901158119860735353079755610612#128
    = toPoly 129460184901158119860735353079755610612#256 := by
    rw [←toPoly_128_extend_256]; rfl
  rw [h_toPoly_eq]

-- GCD Step 1
@[reducible] def gcd_a_1_val : B256 := BitVec.ofNat 256 340282366920938463463374607431768211591
@[reducible] def gcd_b_1_val : B256 := BitVec.ofNat 256 129460184901158119860735353079755610612
@[reducible] def gcd_q_1_val : B256 := BitVec.ofNat 256 7
@[reducible] def gcd_r_1_val : B256 := BitVec.ofNat 256 50818948151962160907779168764081065291
lemma gcd_step_1 : toPoly gcd_a_1_val
    = (toPoly gcd_q_1_val) * (toPoly gcd_b_1_val) + (toPoly gcd_r_1_val) := by
  apply verify_div_step gcd_a_1_val gcd_q_1_val gcd_b_1_val gcd_r_1_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 2
@[reducible] def gcd_a_2_val : B256 := BitVec.ofNat 256 129460184901158119860735353079755610612
@[reducible] def gcd_b_2_val : B256 := BitVec.ofNat 256 50818948151962160907779168764081065291
@[reducible] def gcd_q_2_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_2_val : B256 := BitVec.ofNat 256 14834378446449568495759002342740250153
lemma gcd_step_2 : toPoly gcd_a_2_val
    = (toPoly gcd_q_2_val) * (toPoly gcd_b_2_val) + (toPoly gcd_r_2_val) := by
  apply verify_div_step gcd_a_2_val gcd_q_2_val gcd_b_2_val gcd_r_2_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 3
@[reducible] def gcd_a_3_val : B256 := BitVec.ofNat 256 50818948151962160907779168764081065291
@[reducible] def gcd_b_3_val : B256 := BitVec.ofNat 256 14834378446449568495759002342740250153
@[reducible] def gcd_q_3_val : B256 := BitVec.ofNat 256 5
@[reducible] def gcd_r_3_val : B256 := BitVec.ofNat 256 2244969371547412454183282353422089158
lemma gcd_step_3 : toPoly gcd_a_3_val
    = (toPoly gcd_q_3_val) * (toPoly gcd_b_3_val) + (toPoly gcd_r_3_val) := by
  apply verify_div_step gcd_a_3_val gcd_q_3_val gcd_b_3_val gcd_r_3_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 4
@[reducible] def gcd_a_4_val : B256 := BitVec.ofNat 256 14834378446449568495759002342740250153
@[reducible] def gcd_b_4_val : B256 := BitVec.ofNat 256 2244969371547412454183282353422089158
@[reducible] def gcd_q_4_val : B256 := BitVec.ofNat 256 12
@[reducible] def gcd_r_4_val : B256 := BitVec.ofNat 256 557629265461671673499413449821519617
lemma gcd_step_4 : toPoly gcd_a_4_val
    = (toPoly gcd_q_4_val) * (toPoly gcd_b_4_val) + (toPoly gcd_r_4_val) := by
  apply verify_div_step gcd_a_4_val gcd_q_4_val gcd_b_4_val gcd_r_4_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 5
@[reducible] def gcd_a_5_val : B256 := BitVec.ofNat 256 2244969371547412454183282353422089158
@[reducible] def gcd_b_5_val : B256 := BitVec.ofNat 256 557629265461671673499413449821519617
@[reducible] def gcd_q_5_val : B256 := BitVec.ofNat 256 4
@[reducible] def gcd_r_5_val : B256 := BitVec.ofNat 256 154662442172327929744185287128238018
lemma gcd_step_5 : toPoly gcd_a_5_val
    = (toPoly gcd_q_5_val) * (toPoly gcd_b_5_val) + (toPoly gcd_r_5_val) := by
  apply verify_div_step gcd_a_5_val gcd_q_5_val gcd_b_5_val gcd_r_5_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 6
@[reducible] def gcd_a_6_val : B256 := BitVec.ofNat 256 557629265461671673499413449821519617
@[reducible] def gcd_b_6_val : B256 := BitVec.ofNat 256 154662442172327929744185287128238018
@[reducible] def gcd_q_6_val : B256 := BitVec.ofNat 256 5
@[reducible] def gcd_r_6_val : B256 := BitVec.ofNat 256 7981563795128874392098572882880459
lemma gcd_step_6 : toPoly gcd_a_6_val
    = (toPoly gcd_q_6_val) * (toPoly gcd_b_6_val) + (toPoly gcd_r_6_val) := by
  apply verify_div_step gcd_a_6_val gcd_q_6_val gcd_b_6_val gcd_r_6_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 7
@[reducible] def gcd_a_7_val : B256 := BitVec.ofNat 256 154662442172327929744185287128238018
@[reducible] def gcd_b_7_val : B256 := BitVec.ofNat 256 7981563795128874392098572882880459
@[reducible] def gcd_q_7_val : B256 := BitVec.ofNat 256 22
@[reducible] def gcd_r_7_val : B256 := BitVec.ofNat 256 2032880347484984862837781768793032
lemma gcd_step_7 : toPoly gcd_a_7_val
    = (toPoly gcd_q_7_val) * (toPoly gcd_b_7_val) + (toPoly gcd_r_7_val) := by
  apply verify_div_step gcd_a_7_val gcd_q_7_val gcd_b_7_val gcd_r_7_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 8
@[reducible] def gcd_a_8_val : B256 := BitVec.ofNat 256 7981563795128874392098572882880459
@[reducible] def gcd_b_8_val : B256 := BitVec.ofNat 256 2032880347484984862837781768793032
@[reducible] def gcd_q_8_val : B256 := BitVec.ofNat 256 4
@[reducible] def gcd_r_8_val : B256 := BitVec.ofNat 256 515875961085681014451648089721067
lemma gcd_step_8 : toPoly gcd_a_8_val
    = (toPoly gcd_q_8_val) * (toPoly gcd_b_8_val) + (toPoly gcd_r_8_val) := by
  apply verify_div_step gcd_a_8_val gcd_q_8_val gcd_b_8_val gcd_r_8_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 9
@[reducible] def gcd_a_9_val : B256 := BitVec.ofNat 256 2032880347484984862837781768793032
@[reducible] def gcd_b_9_val : B256 := BitVec.ofNat 256 515875961085681014451648089721067
@[reducible] def gcd_q_9_val : B256 := BitVec.ofNat 256 4
@[reducible] def gcd_r_9_val : B256 := BitVec.ofNat 256 31025928961721470692497869457508
lemma gcd_step_9 : toPoly gcd_a_9_val
    = (toPoly gcd_q_9_val) * (toPoly gcd_b_9_val) + (toPoly gcd_r_9_val) := by
  apply verify_div_step gcd_a_9_val gcd_q_9_val gcd_b_9_val gcd_r_9_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 10
@[reducible] def gcd_a_10_val : B256 := BitVec.ofNat 256 515875961085681014451648089721067
@[reducible] def gcd_b_10_val : B256 := BitVec.ofNat 256 31025928961721470692497869457508
@[reducible] def gcd_q_10_val : B256 := BitVec.ofNat 256 17
@[reducible] def gcd_r_10_val : B256 := BitVec.ofNat 256 11527041598507992604534878848719
lemma gcd_step_10 : toPoly gcd_a_10_val
    = (toPoly gcd_q_10_val) * (toPoly gcd_b_10_val) + (toPoly gcd_r_10_val) := by
  apply verify_div_step gcd_a_10_val gcd_q_10_val gcd_b_10_val gcd_r_10_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 11
@[reducible] def gcd_a_11_val : B256 := BitVec.ofNat 256 31025928961721470692497869457508
@[reducible] def gcd_b_11_val : B256 := BitVec.ofNat 256 11527041598507992604534878848719
@[reducible] def gcd_q_11_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_11_val : B256 := BitVec.ofNat 256 4128545831373579762429170320181
lemma gcd_step_11 : toPoly gcd_a_11_val
    = (toPoly gcd_q_11_val) * (toPoly gcd_b_11_val) + (toPoly gcd_r_11_val) := by
  apply verify_div_step gcd_a_11_val gcd_q_11_val gcd_b_11_val gcd_r_11_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 12
@[reducible] def gcd_a_12_val : B256 := BitVec.ofNat 256 11527041598507992604534878848719
@[reducible] def gcd_b_12_val : B256 := BitVec.ofNat 256 4128545831373579762429170320181
@[reducible] def gcd_q_12_val : B256 := BitVec.ofNat 256 7
@[reducible] def gcd_r_12_val : B256 := BitVec.ofNat 256 2310540288466179836243071651652
lemma gcd_step_12 : toPoly gcd_a_12_val
    = (toPoly gcd_q_12_val) * (toPoly gcd_b_12_val) + (toPoly gcd_r_12_val) := by
  apply verify_div_step gcd_a_12_val gcd_q_12_val gcd_b_12_val gcd_r_12_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 13
@[reducible] def gcd_a_13_val : B256 := BitVec.ofNat 256 4128545831373579762429170320181
@[reducible] def gcd_b_13_val : B256 := BitVec.ofNat 256 2310540288466179836243071651652
@[reducible] def gcd_q_13_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_13_val : B256 := BitVec.ofNat 256 1133809605732934664004237335997
lemma gcd_step_13 : toPoly gcd_a_13_val
    = (toPoly gcd_q_13_val) * (toPoly gcd_b_13_val) + (toPoly gcd_r_13_val) := by
  apply verify_div_step gcd_a_13_val gcd_q_13_val gcd_b_13_val gcd_r_13_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 14
@[reducible] def gcd_a_14_val : B256 := BitVec.ofNat 256 2310540288466179836243071651652
@[reducible] def gcd_b_14_val : B256 := BitVec.ofNat 256 1133809605732934664004237335997
@[reducible] def gcd_q_14_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_14_val : B256 := BitVec.ofNat 256 135806516263750130080402961470
lemma gcd_step_14 : toPoly gcd_a_14_val
    = (toPoly gcd_q_14_val) * (toPoly gcd_b_14_val) + (toPoly gcd_r_14_val) := by
  apply verify_div_step gcd_a_14_val gcd_q_14_val gcd_b_14_val gcd_r_14_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 15
@[reducible] def gcd_a_15_val : B256 := BitVec.ofNat 256 1133809605732934664004237335997
@[reducible] def gcd_b_15_val : B256 := BitVec.ofNat 256 135806516263750130080402961470
@[reducible] def gcd_q_15_val : B256 := BitVec.ofNat 256 10
@[reducible] def gcd_r_15_val : B256 := BitVec.ofNat 256 46012289710668085427033297969
lemma gcd_step_15 : toPoly gcd_a_15_val
    = (toPoly gcd_q_15_val) * (toPoly gcd_b_15_val) + (toPoly gcd_r_15_val) := by
  apply verify_div_step gcd_a_15_val gcd_q_15_val gcd_b_15_val gcd_r_15_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 16
@[reducible] def gcd_a_16_val : B256 := BitVec.ofNat 256 135806516263750130080402961470
@[reducible] def gcd_b_16_val : B256 := BitVec.ofNat 256 46012289710668085427033297969
@[reducible] def gcd_q_16_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_16_val : B256 := BitVec.ofNat 256 3447930063552334952284883053
lemma gcd_step_16 : toPoly gcd_a_16_val
    = (toPoly gcd_q_16_val) * (toPoly gcd_b_16_val) + (toPoly gcd_r_16_val) := by
  apply verify_div_step gcd_a_16_val gcd_q_16_val gcd_b_16_val gcd_r_16_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 17
@[reducible] def gcd_a_17_val : B256 := BitVec.ofNat 256 46012289710668085427033297969
@[reducible] def gcd_b_17_val : B256 := BitVec.ofNat 256 3447930063552334952284883053
@[reducible] def gcd_q_17_val : B256 := BitVec.ofNat 256 21
@[reducible] def gcd_r_17_val : B256 := BitVec.ofNat 256 416710647572715943453195064
lemma gcd_step_17 : toPoly gcd_a_17_val
    = (toPoly gcd_q_17_val) * (toPoly gcd_b_17_val) + (toPoly gcd_r_17_val) := by
  apply verify_div_step gcd_a_17_val gcd_q_17_val gcd_b_17_val gcd_r_17_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 18
@[reducible] def gcd_a_18_val : B256 := BitVec.ofNat 256 3447930063552334952284883053
@[reducible] def gcd_b_18_val : B256 := BitVec.ofNat 256 416710647572715943453195064
@[reducible] def gcd_q_18_val : B256 := BitVec.ofNat 256 9
@[reducible] def gcd_r_18_val : B256 := BitVec.ofNat 256 223883668442446206699055765
lemma gcd_step_18 : toPoly gcd_a_18_val
    = (toPoly gcd_q_18_val) * (toPoly gcd_b_18_val) + (toPoly gcd_r_18_val) := by
  apply verify_div_step gcd_a_18_val gcd_q_18_val gcd_b_18_val gcd_r_18_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 19
@[reducible] def gcd_a_19_val : B256 := BitVec.ofNat 256 416710647572715943453195064
@[reducible] def gcd_b_19_val : B256 := BitVec.ofNat 256 223883668442446206699055765
@[reducible] def gcd_q_19_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_19_val : B256 := BitVec.ofNat 256 51773711108765668752666130
lemma gcd_step_19 : toPoly gcd_a_19_val
    = (toPoly gcd_q_19_val) * (toPoly gcd_b_19_val) + (toPoly gcd_r_19_val) := by
  apply verify_div_step gcd_a_19_val gcd_q_19_val gcd_b_19_val gcd_r_19_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 20
@[reducible] def gcd_a_20_val : B256 := BitVec.ofNat 256 223883668442446206699055765
@[reducible] def gcd_b_20_val : B256 := BitVec.ofNat 256 51773711108765668752666130
@[reducible] def gcd_q_20_val : B256 := BitVec.ofNat 256 4
@[reducible] def gcd_r_20_val : B256 := BitVec.ofNat 256 22361585846914830736200413
lemma gcd_step_20 : toPoly gcd_a_20_val
    = (toPoly gcd_q_20_val) * (toPoly gcd_b_20_val) + (toPoly gcd_r_20_val) := by
  apply verify_div_step gcd_a_20_val gcd_q_20_val gcd_b_20_val gcd_r_20_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 21
@[reducible] def gcd_a_21_val : B256 := BitVec.ofNat 256 51773711108765668752666130
@[reducible] def gcd_b_21_val : B256 := BitVec.ofNat 256 22361585846914830736200413
@[reducible] def gcd_q_21_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_21_val : B256 := BitVec.ofNat 256 17142144078143291622919080
lemma gcd_step_21 : toPoly gcd_a_21_val
    = (toPoly gcd_q_21_val) * (toPoly gcd_b_21_val) + (toPoly gcd_r_21_val) := by
  apply verify_div_step gcd_a_21_val gcd_q_21_val gcd_b_21_val gcd_r_21_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 22
@[reducible] def gcd_a_22_val : B256 := BitVec.ofNat 256 22361585846914830736200413
@[reducible] def gcd_b_22_val : B256 := BitVec.ofNat 256 17142144078143291622919080
@[reducible] def gcd_q_22_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_22_val : B256 := BitVec.ofNat 256 43543347038566396595749
lemma gcd_step_22 : toPoly gcd_a_22_val
    = (toPoly gcd_q_22_val) * (toPoly gcd_b_22_val) + (toPoly gcd_r_22_val) := by
  apply verify_div_step gcd_a_22_val gcd_q_22_val gcd_b_22_val gcd_r_22_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 23
@[reducible] def gcd_a_23_val : B256 := BitVec.ofNat 256 17142144078143291622919080
@[reducible] def gcd_b_23_val : B256 := BitVec.ofNat 256 43543347038566396595749
@[reducible] def gcd_q_23_val : B256 := BitVec.ofNat 256 511
@[reducible] def gcd_r_23_val : B256 := BitVec.ofNat 256 24851375044413967190091
lemma gcd_step_23 : toPoly gcd_a_23_val
    = (toPoly gcd_q_23_val) * (toPoly gcd_b_23_val) + (toPoly gcd_r_23_val) := by
  apply verify_div_step gcd_a_23_val gcd_q_23_val gcd_b_23_val gcd_r_23_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 24
@[reducible] def gcd_a_24_val : B256 := BitVec.ofNat 256 43543347038566396595749
@[reducible] def gcd_b_24_val : B256 := BitVec.ofNat 256 24851375044413967190091
@[reducible] def gcd_q_24_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_24_val : B256 := BitVec.ofNat 256 17673812864467471867571
lemma gcd_step_24 : toPoly gcd_a_24_val
    = (toPoly gcd_q_24_val) * (toPoly gcd_b_24_val) + (toPoly gcd_r_24_val) := by
  apply verify_div_step gcd_a_24_val gcd_q_24_val gcd_b_24_val gcd_r_24_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 25
@[reducible] def gcd_a_25_val : B256 := BitVec.ofNat 256 24851375044413967190091
@[reducible] def gcd_b_25_val : B256 := BitVec.ofNat 256 17673812864467471867571
@[reducible] def gcd_q_25_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_25_val : B256 := BitVec.ofNat 256 7103845695541120199582
lemma gcd_step_25 : toPoly gcd_a_25_val
    = (toPoly gcd_q_25_val) * (toPoly gcd_b_25_val) + (toPoly gcd_r_25_val) := by
  apply verify_div_step gcd_a_25_val gcd_q_25_val gcd_b_25_val gcd_r_25_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 26
@[reducible] def gcd_a_26_val : B256 := BitVec.ofNat 256 17673812864467471867571
@[reducible] def gcd_b_26_val : B256 := BitVec.ofNat 256 7103845695541120199582
@[reducible] def gcd_q_26_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_26_val : B256 := BitVec.ofNat 256 3471032095735008807311
lemma gcd_step_26 : toPoly gcd_a_26_val
    = (toPoly gcd_q_26_val) * (toPoly gcd_b_26_val) + (toPoly gcd_r_26_val) := by
  apply verify_div_step gcd_a_26_val gcd_q_26_val gcd_b_26_val gcd_r_26_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 27
@[reducible] def gcd_a_27_val : B256 := BitVec.ofNat 256 7103845695541120199582
@[reducible] def gcd_b_27_val : B256 := BitVec.ofNat 256 3471032095735008807311
@[reducible] def gcd_q_27_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_27_val : B256 := BitVec.ofNat 256 1280312745950178324751
lemma gcd_step_27 : toPoly gcd_a_27_val
    = (toPoly gcd_q_27_val) * (toPoly gcd_b_27_val) + (toPoly gcd_r_27_val) := by
  apply verify_div_step gcd_a_27_val gcd_q_27_val gcd_b_27_val gcd_r_27_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 28
@[reducible] def gcd_a_28_val : B256 := BitVec.ofNat 256 3471032095735008807311
@[reducible] def gcd_b_28_val : B256 := BitVec.ofNat 256 1280312745950178324751
@[reducible] def gcd_q_28_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_28_val : B256 := BitVec.ofNat 256 1012692363197241961361
lemma gcd_step_28 : toPoly gcd_a_28_val
    = (toPoly gcd_q_28_val) * (toPoly gcd_b_28_val) + (toPoly gcd_r_28_val) := by
  apply verify_div_step gcd_a_28_val gcd_q_28_val gcd_b_28_val gcd_r_28_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 29
@[reducible] def gcd_a_29_val : B256 := BitVec.ofNat 256 1280312745950178324751
@[reducible] def gcd_b_29_val : B256 := BitVec.ofNat 256 1012692363197241961361
@[reducible] def gcd_q_29_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_29_val : B256 := BitVec.ofNat 256 558724060067374124476
lemma gcd_step_29 : toPoly gcd_a_29_val
    = (toPoly gcd_q_29_val) * (toPoly gcd_b_29_val) + (toPoly gcd_r_29_val) := by
  apply verify_div_step gcd_a_29_val gcd_q_29_val gcd_b_29_val gcd_r_29_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 30
@[reducible] def gcd_a_30_val : B256 := BitVec.ofNat 256 1012692363197241961361
@[reducible] def gcd_b_30_val : B256 := BitVec.ofNat 256 558724060067374124476
@[reducible] def gcd_q_30_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_30_val : B256 := BitVec.ofNat 256 192995914958414524649
lemma gcd_step_30 : toPoly gcd_a_30_val
    = (toPoly gcd_q_30_val) * (toPoly gcd_b_30_val) + (toPoly gcd_r_30_val) := by
  apply verify_div_step gcd_a_30_val gcd_q_30_val gcd_b_30_val gcd_r_30_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 31
@[reducible] def gcd_a_31_val : B256 := BitVec.ofNat 256 558724060067374124476
@[reducible] def gcd_b_31_val : B256 := BitVec.ofNat 256 192995914958414524649
@[reducible] def gcd_q_31_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_31_val : B256 := BitVec.ofNat 256 15219864640684399751
lemma gcd_step_31 : toPoly gcd_a_31_val
    = (toPoly gcd_q_31_val) * (toPoly gcd_b_31_val) + (toPoly gcd_r_31_val) := by
  apply verify_div_step gcd_a_31_val gcd_q_31_val gcd_b_31_val gcd_r_31_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 32
@[reducible] def gcd_a_32_val : B256 := BitVec.ofNat 256 192995914958414524649
@[reducible] def gcd_b_32_val : B256 := BitVec.ofNat 256 15219864640684399751
@[reducible] def gcd_q_32_val : B256 := BitVec.ofNat 256 26
@[reducible] def gcd_r_32_val : B256 := BitVec.ofNat 256 8860595400926930351
lemma gcd_step_32 : toPoly gcd_a_32_val
    = (toPoly gcd_q_32_val) * (toPoly gcd_b_32_val) + (toPoly gcd_r_32_val) := by
  apply verify_div_step gcd_a_32_val gcd_q_32_val gcd_b_32_val gcd_r_32_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 33
@[reducible] def gcd_a_33_val : B256 := BitVec.ofNat 256 15219864640684399751
@[reducible] def gcd_b_33_val : B256 := BitVec.ofNat 256 8860595400926930351
@[reducible] def gcd_q_33_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_33_val : B256 := BitVec.ofNat 256 2799413109594183641
lemma gcd_step_33 : toPoly gcd_a_33_val
    = (toPoly gcd_q_33_val) * (toPoly gcd_b_33_val) + (toPoly gcd_r_33_val) := by
  apply verify_div_step gcd_a_33_val gcd_q_33_val gcd_b_33_val gcd_r_33_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 34
@[reducible] def gcd_a_34_val : B256 := BitVec.ofNat 256 8860595400926930351
@[reducible] def gcd_b_34_val : B256 := BitVec.ofNat 256 2799413109594183641
@[reducible] def gcd_q_34_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_34_val : B256 := BitVec.ofNat 256 1269361152383966660
lemma gcd_step_34 : toPoly gcd_a_34_val
    = (toPoly gcd_q_34_val) * (toPoly gcd_b_34_val) + (toPoly gcd_r_34_val) := by
  apply verify_div_step gcd_a_34_val gcd_q_34_val gcd_b_34_val gcd_r_34_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 35
@[reducible] def gcd_a_35_val : B256 := BitVec.ofNat 256 2799413109594183641
@[reducible] def gcd_b_35_val : B256 := BitVec.ofNat 256 1269361152383966660
@[reducible] def gcd_q_35_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_35_val : B256 := BitVec.ofNat 256 424140013905865809
lemma gcd_step_35 : toPoly gcd_a_35_val
    = (toPoly gcd_q_35_val) * (toPoly gcd_b_35_val) + (toPoly gcd_r_35_val) := by
  apply verify_div_step gcd_a_35_val gcd_q_35_val gcd_b_35_val gcd_r_35_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 36
@[reducible] def gcd_a_36_val : B256 := BitVec.ofNat 256 1269361152383966660
@[reducible] def gcd_b_36_val : B256 := BitVec.ofNat 256 424140013905865809
@[reducible] def gcd_q_36_val : B256 := BitVec.ofNat 256 5
@[reducible] def gcd_r_36_val : B256 := BitVec.ofNat 256 284870577651974353
lemma gcd_step_36 : toPoly gcd_a_36_val
    = (toPoly gcd_q_36_val) * (toPoly gcd_b_36_val) + (toPoly gcd_r_36_val) := by
  apply verify_div_step gcd_a_36_val gcd_q_36_val gcd_b_36_val gcd_r_36_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 37
@[reducible] def gcd_a_37_val : B256 := BitVec.ofNat 256 424140013905865809
@[reducible] def gcd_b_37_val : B256 := BitVec.ofNat 256 284870577651974353
@[reducible] def gcd_q_37_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_37_val : B256 := BitVec.ofNat 256 143809319762881826
lemma gcd_step_37 : toPoly gcd_a_37_val
    = (toPoly gcd_q_37_val) * (toPoly gcd_b_37_val) + (toPoly gcd_r_37_val) := by
  apply verify_div_step gcd_a_37_val gcd_q_37_val gcd_b_37_val gcd_r_37_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 38
@[reducible] def gcd_a_38_val : B256 := BitVec.ofNat 256 284870577651974353
@[reducible] def gcd_b_38_val : B256 := BitVec.ofNat 256 143809319762881826
@[reducible] def gcd_q_38_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_38_val : B256 := BitVec.ofNat 256 2748671768582805
lemma gcd_step_38 : toPoly gcd_a_38_val
    = (toPoly gcd_q_38_val) * (toPoly gcd_b_38_val) + (toPoly gcd_r_38_val) := by
  apply verify_div_step gcd_a_38_val gcd_q_38_val gcd_b_38_val gcd_r_38_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 39
@[reducible] def gcd_a_39_val : B256 := BitVec.ofNat 256 143809319762881826
@[reducible] def gcd_b_39_val : B256 := BitVec.ofNat 256 2748671768582805
@[reducible] def gcd_q_39_val : B256 := BitVec.ofNat 256 58
@[reducible] def gcd_r_39_val : B256 := BitVec.ofNat 256 2027184292558672
lemma gcd_step_39 : toPoly gcd_a_39_val
    = (toPoly gcd_q_39_val) * (toPoly gcd_b_39_val) + (toPoly gcd_r_39_val) := by
  apply verify_div_step gcd_a_39_val gcd_q_39_val gcd_b_39_val gcd_r_39_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 40
@[reducible] def gcd_a_40_val : B256 := BitVec.ofNat 256 2748671768582805
@[reducible] def gcd_b_40_val : B256 := BitVec.ofNat 256 2027184292558672
@[reducible] def gcd_q_40_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_40_val : B256 := BitVec.ofNat 256 166286717207397
lemma gcd_step_40 : toPoly gcd_a_40_val
    = (toPoly gcd_q_40_val) * (toPoly gcd_b_40_val) + (toPoly gcd_r_40_val) := by
  apply verify_div_step gcd_a_40_val gcd_q_40_val gcd_b_40_val gcd_r_40_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 41
@[reducible] def gcd_a_41_val : B256 := BitVec.ofNat 256 2027184292558672
@[reducible] def gcd_b_41_val : B256 := BitVec.ofNat 256 166286717207397
@[reducible] def gcd_q_41_val : B256 := BitVec.ofNat 256 15
@[reducible] def gcd_r_41_val : B256 := BitVec.ofNat 256 123028348445763
lemma gcd_step_41 : toPoly gcd_a_41_val
    = (toPoly gcd_q_41_val) * (toPoly gcd_b_41_val) + (toPoly gcd_r_41_val) := by
  apply verify_div_step gcd_a_41_val gcd_q_41_val gcd_b_41_val gcd_r_41_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 42
@[reducible] def gcd_a_42_val : B256 := BitVec.ofNat 256 166286717207397
@[reducible] def gcd_b_42_val : B256 := BitVec.ofNat 256 123028348445763
@[reducible] def gcd_q_42_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_42_val : B256 := BitVec.ofNat 256 42957922578336
lemma gcd_step_42 : toPoly gcd_a_42_val
    = (toPoly gcd_q_42_val) * (toPoly gcd_b_42_val) + (toPoly gcd_r_42_val) := by
  apply verify_div_step gcd_a_42_val gcd_q_42_val gcd_b_42_val gcd_r_42_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 43
@[reducible] def gcd_a_43_val : B256 := BitVec.ofNat 256 123028348445763
@[reducible] def gcd_b_43_val : B256 := BitVec.ofNat 256 42957922578336
@[reducible] def gcd_q_43_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_43_val : B256 := BitVec.ofNat 256 7520384504995
lemma gcd_step_43 : toPoly gcd_a_43_val
    = (toPoly gcd_q_43_val) * (toPoly gcd_b_43_val) + (toPoly gcd_r_43_val) := by
  apply verify_div_step gcd_a_43_val gcd_q_43_val gcd_b_43_val gcd_r_43_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 44
@[reducible] def gcd_a_44_val : B256 := BitVec.ofNat 256 42957922578336
@[reducible] def gcd_b_44_val : B256 := BitVec.ofNat 256 7520384504995
@[reducible] def gcd_q_44_val : B256 := BitVec.ofNat 256 15
@[reducible] def gcd_r_44_val : B256 := BitVec.ofNat 256 1678400792017
lemma gcd_step_44 : toPoly gcd_a_44_val
    = (toPoly gcd_q_44_val) * (toPoly gcd_b_44_val) + (toPoly gcd_r_44_val) := by
  apply verify_div_step gcd_a_44_val gcd_q_44_val gcd_b_44_val gcd_r_44_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 45
@[reducible] def gcd_a_45_val : B256 := BitVec.ofNat 256 7520384504995
@[reducible] def gcd_b_45_val : B256 := BitVec.ofNat 256 1678400792017
@[reducible] def gcd_q_45_val : B256 := BitVec.ofNat 256 4
@[reducible] def gcd_r_45_val : B256 := BitVec.ofNat 256 884095730663
lemma gcd_step_45 : toPoly gcd_a_45_val
    = (toPoly gcd_q_45_val) * (toPoly gcd_b_45_val) + (toPoly gcd_r_45_val) := by
  apply verify_div_step gcd_a_45_val gcd_q_45_val gcd_b_45_val gcd_r_45_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 46
@[reducible] def gcd_a_46_val : B256 := BitVec.ofNat 256 1678400792017
@[reducible] def gcd_b_46_val : B256 := BitVec.ofNat 256 884095730663
@[reducible] def gcd_q_46_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_46_val : B256 := BitVec.ofNat 256 126568833567
lemma gcd_step_46 : toPoly gcd_a_46_val
    = (toPoly gcd_q_46_val) * (toPoly gcd_b_46_val) + (toPoly gcd_r_46_val) := by
  apply verify_div_step gcd_a_46_val gcd_q_46_val gcd_b_46_val gcd_r_46_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 47
@[reducible] def gcd_a_47_val : B256 := BitVec.ofNat 256 884095730663
@[reducible] def gcd_b_47_val : B256 := BitVec.ofNat 256 126568833567
@[reducible] def gcd_q_47_val : B256 := BitVec.ofNat 256 11
@[reducible] def gcd_r_47_val : B256 := BitVec.ofNat 256 6722827582
lemma gcd_step_47 : toPoly gcd_a_47_val
    = (toPoly gcd_q_47_val) * (toPoly gcd_b_47_val) + (toPoly gcd_r_47_val) := by
  apply verify_div_step gcd_a_47_val gcd_q_47_val gcd_b_47_val gcd_r_47_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 48
@[reducible] def gcd_a_48_val : B256 := BitVec.ofNat 256 126568833567
@[reducible] def gcd_b_48_val : B256 := BitVec.ofNat 256 6722827582
@[reducible] def gcd_q_48_val : B256 := BitVec.ofNat 256 23
@[reducible] def gcd_r_48_val : B256 := BitVec.ofNat 256 2155280965
lemma gcd_step_48 : toPoly gcd_a_48_val
    = (toPoly gcd_q_48_val) * (toPoly gcd_b_48_val) + (toPoly gcd_r_48_val) := by
  apply verify_div_step gcd_a_48_val gcd_q_48_val gcd_b_48_val gcd_r_48_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 49
@[reducible] def gcd_a_49_val : B256 := BitVec.ofNat 256 6722827582
@[reducible] def gcd_b_49_val : B256 := BitVec.ofNat 256 2155280965
@[reducible] def gcd_q_49_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_49_val : B256 := BitVec.ofNat 256 271399921
lemma gcd_step_49 : toPoly gcd_a_49_val
    = (toPoly gcd_q_49_val) * (toPoly gcd_b_49_val) + (toPoly gcd_r_49_val) := by
  apply verify_div_step gcd_a_49_val gcd_q_49_val gcd_b_49_val gcd_r_49_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 50
@[reducible] def gcd_a_50_val : B256 := BitVec.ofNat 256 2155280965
@[reducible] def gcd_b_50_val : B256 := BitVec.ofNat 256 271399921
@[reducible] def gcd_q_50_val : B256 := BitVec.ofNat 256 8
@[reducible] def gcd_r_50_val : B256 := BitVec.ofNat 256 18818509
lemma gcd_step_50 : toPoly gcd_a_50_val
    = (toPoly gcd_q_50_val) * (toPoly gcd_b_50_val) + (toPoly gcd_r_50_val) := by
  apply verify_div_step gcd_a_50_val gcd_q_50_val gcd_b_50_val gcd_r_50_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 51
@[reducible] def gcd_a_51_val : B256 := BitVec.ofNat 256 271399921
@[reducible] def gcd_b_51_val : B256 := BitVec.ofNat 256 18818509
@[reducible] def gcd_q_51_val : B256 := BitVec.ofNat 256 17
@[reducible] def gcd_r_51_val : B256 := BitVec.ofNat 256 12600044
lemma gcd_step_51 : toPoly gcd_a_51_val
    = (toPoly gcd_q_51_val) * (toPoly gcd_b_51_val) + (toPoly gcd_r_51_val) := by
  apply verify_div_step gcd_a_51_val gcd_q_51_val gcd_b_51_val gcd_r_51_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 52
@[reducible] def gcd_a_52_val : B256 := BitVec.ofNat 256 18818509
@[reducible] def gcd_b_52_val : B256 := BitVec.ofNat 256 12600044
@[reducible] def gcd_q_52_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_52_val : B256 := BitVec.ofNat 256 6284025
lemma gcd_step_52 : toPoly gcd_a_52_val
    = (toPoly gcd_q_52_val) * (toPoly gcd_b_52_val) + (toPoly gcd_r_52_val) := by
  apply verify_div_step gcd_a_52_val gcd_q_52_val gcd_b_52_val gcd_r_52_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 53
@[reducible] def gcd_a_53_val : B256 := BitVec.ofNat 256 12600044
@[reducible] def gcd_b_53_val : B256 := BitVec.ofNat 256 6284025
@[reducible] def gcd_q_53_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_53_val : B256 := BitVec.ofNat 256 2123239
lemma gcd_step_53 : toPoly gcd_a_53_val
    = (toPoly gcd_q_53_val) * (toPoly gcd_b_53_val) + (toPoly gcd_r_53_val) := by
  apply verify_div_step gcd_a_53_val gcd_q_53_val gcd_b_53_val gcd_r_53_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 54
@[reducible] def gcd_a_54_val : B256 := BitVec.ofNat 256 6284025
@[reducible] def gcd_b_54_val : B256 := BitVec.ofNat 256 2123239
@[reducible] def gcd_q_54_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_54_val : B256 := BitVec.ofNat 256 2042167
lemma gcd_step_54 : toPoly gcd_a_54_val
    = (toPoly gcd_q_54_val) * (toPoly gcd_b_54_val) + (toPoly gcd_r_54_val) := by
  apply verify_div_step gcd_a_54_val gcd_q_54_val gcd_b_54_val gcd_r_54_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 55
@[reducible] def gcd_a_55_val : B256 := BitVec.ofNat 256 2123239
@[reducible] def gcd_b_55_val : B256 := BitVec.ofNat 256 2042167
@[reducible] def gcd_q_55_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_55_val : B256 := BitVec.ofNat 256 73406
lemma gcd_step_55 : toPoly gcd_a_55_val
    = (toPoly gcd_q_55_val) * (toPoly gcd_b_55_val) + (toPoly gcd_r_55_val) := by
  apply verify_div_step gcd_a_55_val gcd_q_55_val gcd_b_55_val gcd_r_55_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 56
@[reducible] def gcd_a_56_val : B256 := BitVec.ofNat 256 2042167
@[reducible] def gcd_b_56_val : B256 := BitVec.ofNat 256 73406
@[reducible] def gcd_q_56_val : B256 := BitVec.ofNat 256 30
@[reducible] def gcd_r_56_val : B256 := BitVec.ofNat 256 28835
lemma gcd_step_56 : toPoly gcd_a_56_val
    = (toPoly gcd_q_56_val) * (toPoly gcd_b_56_val) + (toPoly gcd_r_56_val) := by
  apply verify_div_step gcd_a_56_val gcd_q_56_val gcd_b_56_val gcd_r_56_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 57
@[reducible] def gcd_a_57_val : B256 := BitVec.ofNat 256 73406
@[reducible] def gcd_b_57_val : B256 := BitVec.ofNat 256 28835
@[reducible] def gcd_q_57_val : B256 := BitVec.ofNat 256 6
@[reducible] def gcd_r_57_val : B256 := BitVec.ofNat 256 15732
lemma gcd_step_57 : toPoly gcd_a_57_val
    = (toPoly gcd_q_57_val) * (toPoly gcd_b_57_val) + (toPoly gcd_r_57_val) := by
  apply verify_div_step gcd_a_57_val gcd_q_57_val gcd_b_57_val gcd_r_57_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 58
@[reducible] def gcd_a_58_val : B256 := BitVec.ofNat 256 28835
@[reducible] def gcd_b_58_val : B256 := BitVec.ofNat 256 15732
@[reducible] def gcd_q_58_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_58_val : B256 := BitVec.ofNat 256 2635
lemma gcd_step_58 : toPoly gcd_a_58_val
    = (toPoly gcd_q_58_val) * (toPoly gcd_b_58_val) + (toPoly gcd_r_58_val) := by
  apply verify_div_step gcd_a_58_val gcd_q_58_val gcd_b_58_val gcd_r_58_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 59
@[reducible] def gcd_a_59_val : B256 := BitVec.ofNat 256 15732
@[reducible] def gcd_b_59_val : B256 := BitVec.ofNat 256 2635
@[reducible] def gcd_q_59_val : B256 := BitVec.ofNat 256 6
@[reducible] def gcd_r_59_val : B256 := BitVec.ofNat 256 206
lemma gcd_step_59 : toPoly gcd_a_59_val
    = (toPoly gcd_q_59_val) * (toPoly gcd_b_59_val) + (toPoly gcd_r_59_val) := by
  apply verify_div_step gcd_a_59_val gcd_q_59_val gcd_b_59_val gcd_r_59_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 60
@[reducible] def gcd_a_60_val : B256 := BitVec.ofNat 256 2635
@[reducible] def gcd_b_60_val : B256 := BitVec.ofNat 256 206
@[reducible] def gcd_q_60_val : B256 := BitVec.ofNat 256 25
@[reducible] def gcd_r_60_val : B256 := BitVec.ofNat 256 21
lemma gcd_step_60 : toPoly gcd_a_60_val
    = (toPoly gcd_q_60_val) * (toPoly gcd_b_60_val) + (toPoly gcd_r_60_val) := by
  apply verify_div_step gcd_a_60_val gcd_q_60_val gcd_b_60_val gcd_r_60_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 61
@[reducible] def gcd_a_61_val : B256 := BitVec.ofNat 256 206
@[reducible] def gcd_b_61_val : B256 := BitVec.ofNat 256 21
@[reducible] def gcd_q_61_val : B256 := BitVec.ofNat 256 15
@[reducible] def gcd_r_61_val : B256 := BitVec.ofNat 256 13
lemma gcd_step_61 : toPoly gcd_a_61_val
    = (toPoly gcd_q_61_val) * (toPoly gcd_b_61_val) + (toPoly gcd_r_61_val) := by
  apply verify_div_step gcd_a_61_val gcd_q_61_val gcd_b_61_val gcd_r_61_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 62
@[reducible] def gcd_a_62_val : B256 := BitVec.ofNat 256 21
@[reducible] def gcd_b_62_val : B256 := BitVec.ofNat 256 13
@[reducible] def gcd_q_62_val : B256 := BitVec.ofNat 256 3
@[reducible] def gcd_r_62_val : B256 := BitVec.ofNat 256 2
lemma gcd_step_62 : toPoly gcd_a_62_val
    = (toPoly gcd_q_62_val) * (toPoly gcd_b_62_val) + (toPoly gcd_r_62_val) := by
  apply verify_div_step gcd_a_62_val gcd_q_62_val gcd_b_62_val gcd_r_62_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 63
@[reducible] def gcd_a_63_val : B256 := BitVec.ofNat 256 13
@[reducible] def gcd_b_63_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_q_63_val : B256 := BitVec.ofNat 256 6
@[reducible] def gcd_r_63_val : B256 := BitVec.ofNat 256 1
lemma gcd_step_63 : toPoly gcd_a_63_val
    = (toPoly gcd_q_63_val) * (toPoly gcd_b_63_val) + (toPoly gcd_r_63_val) := by
  apply verify_div_step gcd_a_63_val gcd_q_63_val gcd_b_63_val gcd_r_63_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

-- GCD Step 64
@[reducible] def gcd_a_64_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_b_64_val : B256 := BitVec.ofNat 256 1
@[reducible] def gcd_q_64_val : B256 := BitVec.ofNat 256 2
@[reducible] def gcd_r_64_val : B256 := BitVec.ofNat 256 0
lemma gcd_step_64 : toPoly gcd_a_64_val
    = (toPoly gcd_q_64_val) * (toPoly gcd_b_64_val) + (toPoly gcd_r_64_val) := by
  apply verify_div_step gcd_a_64_val gcd_q_64_val gcd_b_64_val gcd_r_64_val
    (hq := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
    (hb := by simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT])
  rfl

lemma rabin_gcd_condition_gHashPoly : EuclideanDomain.gcd ((X^(2^64)) + X) ghashPoly = 1 := by
  rw [gcd_start_reduction]
  change EuclideanDomain.gcd (ghashPoly) (toPoly gcd_b_1_val) = 1
  have h_ghashPoly_eq : ghashPoly = toPoly gcd_a_1_val := by rw [ghashPoly_eq_P_val, P_val]; rfl
  rw [h_ghashPoly_eq]

  -- Step 1: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_1)]
  -- Step 2: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_2)]
  -- Step 3: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_3)]
  -- Step 4: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_4)]
  -- Step 5: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_5)]
  -- Step 6: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_6)]
  -- Step 7: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_7)]
  -- Step 8: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_8)]
  -- Step 9: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_9)]
  -- Step 10: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_10)]
  -- Step 11: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_11)]
  -- Step 12: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_12)]
  -- Step 13: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_13)]
  -- Step 14: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_14)]
  -- Step 15: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_15)]
  -- Step 16: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_16)]
  -- Step 17: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_17)]
  -- Step 18: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_18)]
  -- Step 19: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_19)]
  -- Step 20: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_20)]
  -- Step 21: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_21)]
  -- Step 22: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_22)]
  -- Step 23: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_23)]
  -- Step 24: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_24)]
  -- Step 25: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_25)]
  -- Step 26: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_26)]
  -- Step 27: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_27)]
  -- Step 28: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_28)]
  -- Step 29: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_29)]
  -- Step 30: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_30)]
  -- Step 31: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_31)]
  -- Step 32: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_32)]
  -- Step 33: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_33)]
  -- Step 34: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_34)]
  -- Step 35: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_35)]
  -- Step 36: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_36)]
  -- Step 37: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_37)]
  -- Step 38: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_38)]
  -- Step 39: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_39)]
  -- Step 40: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_40)]
  -- Step 41: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_41)]
  -- Step 42: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_42)]
  -- Step 43: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_43)]
  -- Step 44: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_44)]
  -- Step 45: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_45)]
  -- Step 46: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_46)]
  -- Step 47: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_47)]
  -- Step 48: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_48)]
  -- Step 49: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_49)]
  -- Step 50: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_50)]
  -- Step 51: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_51)]
  -- Step 52: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_52)]
  -- Step 53: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_53)]
  -- Step 54: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_54)]
  -- Step 55: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_55)]
  -- Step 56: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_56)]
  -- Step 57: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_57)]
  -- Step 58: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_58)]
  -- Step 59: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_59)]
  -- Step 60: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_60)]
  -- Step 61: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_61)]
  -- Step 62: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_62)]
  -- Step 63: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_63)]
  -- Step 64: gcd(0 bit, -1 bit)
  rw [gcd_eq_gcd_next_step (hb := by rw [toPoly_ne_zero_iff_ne_zero]; decide) (h := gcd_step_64)]
  -- Final: gcd(1, 0) = 1
  rw [toPoly_zero_eq_zero, toPoly_one_eq_one (h_w_pos := by omega)]
  exact EuclideanDomain.gcd_one_left 0

end BF128Ghash
