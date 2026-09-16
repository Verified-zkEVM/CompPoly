/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Dimitris Mitsios
-/
module

public import CompPoly.Fields.Binary.BF128Ghash.Arithmetic
public import CompPoly.Fields.Binary.BF128Ghash.Basic

/-! # GHASH Polynomial-Basis Field

The nominal carrier stores polynomial-basis `BitVec 128` coordinates: bit `i` is the
coefficient of `X^i`. Explicit coordinate maps separate this presentation from raw machine
words and other binary fields. Addition, multiplication, and the named inversion algorithm
are executable, with an injective interpretation in
`GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)` proving their algebraic laws.
The `Field` instance uses the same executable operations, with binary exponentiation for
natural and integer powers. These coordinates describe polynomial coefficients; they do not
introduce a byte or wire-format conversion. Import
`CompPoly.Fields.Binary.BF128Ghash.Arithmetic` for the nominal carrier and executable
operations without the quotient or irreducibility certificates.

## Main Definitions

- `ConcreteBF128Ghash`: Nominal elements with `BitVec 128` polynomial coordinates
- `ofBitVec`, `ConcreteBF128Ghash.toBitVec`: Explicit inverse coordinate maps
- `instFieldConcreteBF128Ghash`: The field instance for `ConcreteBF128Ghash`
- `toQuot`: The canonical map from `ConcreteBF128Ghash` to `AdjoinRoot ghashPoly`
- `reduce_clMul`: The reduction of the carry-less multiplication
- `powTwoPow`: Repeated squaring in the nominal field
- `invItohTsujii`: The Itoh-Tsujii inversion algorithm
- `toQuot_invItohTsujii`: The lemma that `invItohTsujii` computes `a^(2^128 - 2)`

## References
* [NIST-SP-800-38D] Dworkin, M. Recommendation for Block Cipher Modes of Operation:
  Galois/Counter Mode (GCM) and GMAC. NIST Special Publication 800-38D.
  https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

-/

@[expose] public section

namespace BF128Ghash

set_option maxRecDepth 1500

open BitVec Polynomial Ideal BF128Ghash AdjoinRoot

/-- The carrier is finite without choosing an enumeration. -/
instance : Finite ConcreteBF128Ghash :=
  Finite.of_equiv (Fin (2 ^ 128))
    { toFun := fun a => ofBitVec (BitVec.ofFin a)
      invFun := fun a => a.toBitVec.toFin
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

section CarryLessMultiplicationReduction

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
    simp only [Nat.reducePow, Nat.ofNat_pos]
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
    rw [ghashPoly_eq_X_pow_add_tail, _root_.add_assoc]
    rw [ZMod2Poly.add_self_cancel, _root_.add_zero]
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
    rw [_root_.zero_add]
    rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := ghashPoly_ne_zero)]

/-- One fold preserves the value modulo P. -/
lemma fold_step_mod_eq (x : B256) :
    toPoly (fold_step x) % ghashPoly = toPoly x % ghashPoly := by
  unfold fold_step
  let h := x.extractLsb 255 128
  let l := x.extractLsb 127 0
  rw [toPoly_xor]
  rw [toPoly_clMul]
  rw [toPoly_128_extend_256, R_val_eq_ghashTail]
  rw [toPoly_split_256 x]
  rw [CanonicalEuclideanDomain.add_mod_eq (hn := ghashPoly_ne_zero)]
  conv_rhs => rw [CanonicalEuclideanDomain.add_mod_eq (hn := ghashPoly_ne_zero)]
  have h_first_eq : (toPoly (extractLsb 255 128 x) * ghashTail) % ghashPoly =
                    (toPoly (extractLsb 255 128 x) * X^128) % ghashPoly := by
    symm; apply poly_reduce_step
  grind

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
    let term1 := clMul h R_val
    have h_term1_deg : (toPoly term1).degree < 135 := by
      rw [toPoly_clMul]
      · apply (Polynomial.degree_mul_le _ _).trans_lt
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
    let term2 := clMul h2  R_val

    rw [toPoly_xor, toPoly_clMul]
    apply (Polynomial.degree_add_le _ _).trans_lt
    rw [max_lt_iff]
    constructor
    · apply (Polynomial.degree_mul_le _ _).trans_lt
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

section RingInstance_and_PolyQuotient

abbrev PolyQuot := AdjoinRoot ghashPoly

/-- Interpret polynomial-basis coordinates in the quotient by the defining polynomial. -/
noncomputable def toQuot (a : ConcreteBF128Ghash) : PolyQuot :=
  AdjoinRoot.mk ghashPoly (toPoly a.toBitVec)

/-- Frobenius property: a^(2^128) = a in GF(2^128). -/
lemma toQuot_pow_card (a : ConcreteBF128Ghash) : (toQuot a)^(2^128) = toQuot a := by
  rw [←BF128Ghash_card]
  rw [FiniteField.pow_card (toQuot a)]

/-- The quotient interpretation is injective: coordinate polynomials have degree below 128,
whereas the defining polynomial has degree 128. -/
lemma toQuot_injective : Function.Injective toQuot := by
  intro a b h
  unfold toQuot at h
  have h_sub : toPoly a.toBitVec - toPoly b.toBitVec = toPoly (a.toBitVec ^^^ b.toBitVec) := by
    rw [toPoly_xor]
    ring_nf
    exact ZMod2Poly.sub_eq_add (toPoly a.toBitVec) (toPoly b.toBitVec)
  let diff := a.toBitVec ^^^ b.toBitVec
  have h_deg : (toPoly diff).degree < 128 := by
    apply toPoly_degree_lt_w (w:=128) (by norm_num)
  have h_dvd : ghashPoly ∣ (toPoly a.toBitVec - toPoly b.toBitVec) := by
    rw [AdjoinRoot.mk_eq_mk] at h
    exact h
  have h_zero : toPoly diff = 0 := by
    by_contra h_nz
    have h_diff_nz : toPoly a.toBitVec - toPoly b.toBitVec ≠ 0 := by
      rw [h_sub]; exact h_nz
    have h_deg_poly : ghashPoly.degree ≤ (toPoly a.toBitVec - toPoly b.toBitVec).degree :=
      Polynomial.degree_le_of_dvd (h1 := h_dvd) (h2 := h_diff_nz)
    have h_eq_deg : (toPoly a.toBitVec - toPoly b.toBitVec).degree = (toPoly diff).degree := by
      rw [h_sub.symm]
    rw [ghashPoly_degree] at h_deg_poly
    rw [h_eq_deg] at h_deg_poly
    exact not_le_of_gt h_deg h_deg_poly
  have h_diff_eq_zero : diff = 0 := by
    by_contra h_nz
    have h_diff_ne_zero : diff ≠ 0 := by omega
    rw [←toPoly_ne_zero_iff_ne_zero (v := diff)] at h_diff_ne_zero
    exact h_diff_ne_zero h_zero
  exact ConcreteBF128Ghash.ext (BitVec.xor_eq_zero_iff.mp h_diff_eq_zero)

lemma toQuot_add (a b : ConcreteBF128Ghash) : toQuot (a + b) = toQuot a + toQuot b := by
  unfold toQuot
  rw [toBitVec_add, toPoly_xor]
  exact map_add (AdjoinRoot.mk ghashPoly) (toPoly a.toBitVec) (toPoly b.toBitVec)

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

/-- Interpreting a reduced carry-less product agrees with multiplication in the quotient. -/
lemma toQuot_mul (a b : ConcreteBF128Ghash) : toQuot (a * b) = toQuot a * toQuot b := by
  unfold toQuot
  have h_clMul : toPoly (clMul a.toBitVec b.toBitVec) =
      toPoly a.toBitVec * toPoly b.toBitVec := toPoly_clMul a.toBitVec b.toBitVec
  have h_reduce : toPoly (reduce_clMul (clMul a.toBitVec b.toBitVec)) =
                  toPoly (clMul a.toBitVec b.toBitVec) % ghashPoly := by
    apply reduce_clMul_correct
  change AdjoinRoot.mk ghashPoly (toPoly (reduce_clMul (clMul a.toBitVec b.toBitVec))) =
         AdjoinRoot.mk ghashPoly (toPoly a.toBitVec) * AdjoinRoot.mk ghashPoly (toPoly b.toBitVec)
  rw [h_reduce, h_clMul, ← map_mul (AdjoinRoot.mk ghashPoly), AdjoinRoot.mk_eq_mk]
  apply dvd_sub_comm.mp
  exact CanonicalEuclideanDomain.dvd_sub_mod
    (a := toPoly a.toBitVec * toPoly b.toBitVec) (b := ghashPoly)

-- Ring axioms follow from the injective quotient interpretation.
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

instance instSemigroupConcreteBF128Ghash : Semigroup ConcreteBF128Ghash where
  mul_assoc := mul_assoc

instance instRingConcreteBF128Ghash : Ring ConcreteBF128Ghash where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  npow := npowBinRecAuto
  npow_zero := npowBinRec_zero
  npow_succ := npowBinRec_succ
  natCast := natCast
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  intCast := intCast
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc

end RingInstance_and_PolyQuotient

section ItohTsujiiInversion

lemma toQuot_square (a : ConcreteBF128Ghash) : toQuot (square a) = (toQuot a)^2 := by
  unfold square
  rw [toQuot_mul]; exact Eq.symm (pow_two (toQuot a))

lemma toQuot_powTwoPow (a : ConcreteBF128Ghash) (k : Nat) :
    toQuot (powTwoPow a k) = (toQuot a)^(2^k) := by
  induction k generalizing a with
  | zero =>
    simp only [powTwoPow, pow_zero, pow_one]
  | succ n ih =>
    simp only [powTwoPow]
    rw [ih, toQuot_square]
    rw [← pow_mul, pow_succ, mul_comm]

/-- The target value for step k: a^(2^k - 1) -/
noncomputable def target_val (a : PolyQuot) (k : ℕ) : PolyQuot := a ^ (2^k - 1)

/-- Fundamental Itoh-Tsujii Step Lemma:
  If `x = a^(2^n - 1)` and `y = a^(2^m - 1)`, then `(x^(2^m)) * y = a^(2^(n+m) - 1)`.
  This corresponds to the code `(powTwoPow u_n m) * u_m`. -/
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

lemma toQuot_invItohTsujii (a : ConcreteBF128Ghash) (h_ne : a ≠ 0) :
    toQuot (invItohTsujii a) = (toQuot a)^(2^128 - 2) := by
  unfold invItohTsujii
  let q := toQuot a
  have h_u1 : toQuot a = target_val q 1 := by
    simp only [target_val, pow_one, Nat.add_one_sub_one]; rfl
  have h_u2 : toQuot ((powTwoPow a 1) * a) = target_val q 2 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u1 h_u1
  let u2 := (powTwoPow a 1) * a
  have h_u3 : toQuot ((powTwoPow u2 1) * a) = target_val q 3 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u2 h_u1
  let u3 := (powTwoPow u2 1) * a
  have h_u6 : toQuot ((powTwoPow u3 3) * u3) = target_val q 6 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u3 h_u3
  let u6 := (powTwoPow u3 3) * u3
  have h_u7 : toQuot ((powTwoPow u6 1) * a) = target_val q 7 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u6 h_u1
  let u7 := (powTwoPow u6 1) * a
  have h_u14 : toQuot ((powTwoPow u7 7) * u7) = target_val q 14 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u7 h_u7
  let u14 := (powTwoPow u7 7) * u7
  have h_u15 : toQuot ((powTwoPow u14 1) * a) = target_val q 15 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u14 h_u1
  let u15 := (powTwoPow u14 1) * a
  have h_u30 : toQuot ((powTwoPow u15 15) * u15) = target_val q 30 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u15 h_u15
  let u30 := (powTwoPow u15 15) * u15
  have h_u31 : toQuot ((powTwoPow u30 1) * a) = target_val q 31 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u30 h_u1
  let u31 := (powTwoPow u30 1) * a
  have h_u62 : toQuot ((powTwoPow u31 31) * u31) = target_val q 62 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u31 h_u31
  let u62 := (powTwoPow u31 31) * u31
  have h_u63 : toQuot ((powTwoPow u62 1) * a) = target_val q 63 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u62 h_u1
  let u63 := (powTwoPow u62 1) * a
  have h_u126 : toQuot ((powTwoPow u63 63) * u63) = target_val q 126 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u63 h_u63
  let u126 := (powTwoPow u63 63) * u63
  have h_u127 : toQuot ((powTwoPow u126 1) * a) = target_val q 127 := by
    simp only [toQuot_mul, toQuot_powTwoPow]
    exact itoh_tsujii_step (by norm_num) (by norm_num) h_u126 h_u1
  let u127 := (powTwoPow u126 1) * a
  have h_toNat_ne_zero : a.toBitVec.toNat ≠ 0 := by
    by_contra h_eq_zero
    have h_a_eq_zero : a = 0 := by
      apply ConcreteBF128Ghash.ext
      apply BitVec.eq_of_toNat_eq
      simpa only [toBitVec_zero, BitVec.toNat_zero] using h_eq_zero
    exact h_ne h_a_eq_zero
  simp only [if_neg h_toNat_ne_zero]
  rw [toQuot_square, h_u127]
  unfold target_val
  rw [←pow_mul]
  congr 1

@[deprecated (since := "2026-09-16")] alias pow_2k := powTwoPow
@[deprecated (since := "2026-09-16")] alias inv_itoh_tsujii := invItohTsujii
@[deprecated (since := "2026-09-16")] alias toQuot_pow_2k := toQuot_powTwoPow
@[deprecated (since := "2026-09-16")] alias toQuot_inv_itoh_tsujii := toQuot_invItohTsujii

end ItohTsujiiInversion

section DivisionRing_Field_Instances

lemma exists_pair_ne : ∃ x y : ConcreteBF128Ghash, x ≠ y :=
  ⟨0, 1, by decide⟩

lemma mul_inv_cancel (a : ConcreteBF128Ghash) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_one]
  have h_inv : a⁻¹ = invItohTsujii a := rfl
  rw [h_inv, toQuot_invItohTsujii a h]
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
  exact _root_.mul_inv_cancel₀ h_quot_ne_zero

lemma mul_comm (a b : ConcreteBF128Ghash) : a * b = b * a := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_mul]
  exact _root_.mul_comm (toQuot a) (toQuot b)

/-! ### Field instance

The field structure retains the explicit arithmetic, including the total inversion chain.
Both natural and integer powers use binary exponentiation.
-/

theorem isField_concrete : IsField ConcreteBF128Ghash where
  exists_pair_ne := exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel := fun {_} h => ⟨Inv.inv _, mul_inv_cancel _ h⟩

/-- The GHASH field with executable inversion, division, and binary exponentiation. -/
instance instFieldConcreteBF128Ghash : Field ConcreteBF128Ghash where
  mul_comm := mul_comm
  inv := invItohTsujii
  div a b := a * invItohTsujii b
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := exists_pair_ne
  mul_inv_cancel := mul_inv_cancel
  inv_zero := inv_zero
  zpow := zpowRec npowBinRecAuto
  zpow_zero' _ := rfl
  zpow_succ' := npowBinRec_succ
  zpow_neg' _ _ := rfl
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- Compatibility name for the division ring inherited from the field. -/
@[deprecated "Use the division ring inherited from the Field instance." (since := "2026-09-16")]
abbrev instDivisionRingConcreteBF128Ghash : DivisionRing ConcreteBF128Ghash :=
  Field.toDivisionRing

/-- Inversion is the total Itoh-Tsujii algorithm, including at zero. -/
theorem inv_def (a : ConcreteBF128Ghash) : a⁻¹ = invItohTsujii a := rfl

/-- Division multiplies by the total Itoh-Tsujii inverse of the denominator. -/
theorem div_def (a b : ConcreteBF128Ghash) : a / b = a * invItohTsujii b := rfl

/-- Natural powers use binary exponentiation. -/
theorem npow_def (a : ConcreteBF128Ghash) (n : ℕ) : a ^ n = npowBinRec n a := rfl

/-- Integer powers use binary exponentiation and invert the result for negative exponents. -/
theorem zpow_def (a : ConcreteBF128Ghash) (n : ℤ) :
    a ^ n = zpowRec npowBinRecAuto n a := rfl

/-- The quotient interpretation preserves inversion, including at zero. -/
theorem toQuot_inv (a : ConcreteBF128Ghash) : toQuot a⁻¹ = (toQuot a)⁻¹ := by
  by_cases h : a = 0
  · simp only [h, toQuot_zero, _root_.inv_zero]
  · apply eq_inv_of_mul_eq_one_right
    rw [← toQuot_mul, mul_inv_cancel a h, toQuot_one]

end DivisionRing_Field_Instances

/-- The polynomial-basis GHASH field has characteristic two. -/
instance : CharP ConcreteBF128Ghash 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 rfl

end BF128Ghash
