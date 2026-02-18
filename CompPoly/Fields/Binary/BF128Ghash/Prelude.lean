/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.Common

/-! # BinaryField128Ghash Prelude

Define GF(2^128) as a single field extension over GF(2) using the GHASH polynomial
from AES-GCM: P(X) = X^128 + X^7 + X^2 + X + 1.

## Main Definitions

### Polynomial Definitions
- `ghashPoly`: The defining polynomial X^128 + X^7 + X^2 + X + 1 over GF(2)
- `ghashTail`: The tail polynomial X^7 + X^2 + X + 1

### Verification Functions
- `checkSquareStep`: Verifies a modular squaring step
- `verify_square_step_correct`: Correctness theorem for square step verification
- `checkDivStep`: Verifies a division step
- `verify_div_step`: Correctness theorem for division step verification

For BitVec operations (`clMul`, `clSq`, `toPoly`) and shared lemmas, see
`ArkLib.Data.FieldTheory.BinaryField.Common`.
-/

namespace BF128Ghash

open Polynomial AdjoinRoot BinaryField

-- Re-export common definitions for convenience
export BinaryField (B128 B256 to256 to256_toNat clMul clSq toPoly clMul_eq_fold
  toPoly_one_eq_one toPoly_zero_eq_zero toPoly_ne_zero_iff_ne_zero
  toPoly_degree_lt_w toPoly_degree_of_lt_two_pow BitVec_lt_two_pow_of_toPoly_degree_lt
  toPoly_xor toPoly_fold_xor toPoly_128_extend_256 toPoly_shiftLeft_no_overflow
  toPoly_clMul_no_overflow gcd_eq_gcd_next_step gcd_one_zero)

section GHASHPolynomial

/-- The GHASH polynomial: P(X) = X^128 + X^7 + X^2 + X + 1 over GF(2).
This is the irreducible polynomial used in AES-GCM. -/
noncomputable def ghashPoly : Polynomial (ZMod 2) :=
  X^128 + X^7 + X^2 + X + 1

/--
The tail of GHASH poly: T(X) = X^7 + X^2 + X + 1
-/
@[reducible]
noncomputable def ghashTail : Polynomial (ZMod 2) := X^7 + X^2 + X + 1

@[simp]
lemma ghashPoly_eq_X_pow_add_tail : ghashPoly = X^128 + ghashTail := by
  unfold ghashPoly ghashTail
  ring

@[simp]
lemma ghashTail_natDegree : ghashTail.natDegree = 7 := by
  unfold ghashTail
  rw [add_assoc, add_assoc]
  rw [natDegree_add_eq_left_of_natDegree_lt (h := by
    simp only [natDegree_pow, natDegree_X, mul_one];
    rw [natDegree_add_eq_left_of_natDegree_lt (h := by
      simp only [natDegree_pow, natDegree_X, mul_one]
      rw [natDegree_add_eq_left_of_natDegree_lt (h := by
        simp only [natDegree_one, natDegree_X, zero_lt_one] )]
      simp only [natDegree_X, Nat.one_lt_ofNat]
    )];
    simp only [natDegree_pow, natDegree_X, mul_one, Nat.reduceLT])]
  simp only [natDegree_pow, natDegree_X, mul_one]

/-- The GHASH polynomial is monic. -/
lemma ghashTail_monic : Monic ghashTail := by
  unfold Monic leadingCoeff
  -- Use our degree lemma to look at the right index
  rw [ghashTail_natDegree]
  unfold ghashTail
  -- coeff (A + B) i = coeff A i + coeff B i
  rw [coeff_add, coeff_add, coeff_add]
  -- coeff (X^n) n = 1
  rw [coeff_X_pow 7, if_pos rfl]
  -- coeff (X^k) 128 = 0 for k < 128
  rw [coeff_X_pow 2, if_neg (by norm_num)]
  rw [coeff_X, if_neg (by norm_num)]
  rw [coeff_one, if_neg (by norm_num)]
  -- 1 + 0 + 0 + 0 + 0 = 1
  simp only [add_zero]

lemma ghashTail_ne_zero : ghashTail ≠ 0 := ghashTail_monic.ne_zero

lemma ghashTail_degree : (ghashTail).degree = 7 := by
  rw [degree_eq_natDegree (hp := ghashTail_ne_zero)]
  simp only [ghashTail_natDegree, Nat.cast_ofNat]

/-- The degree of the GHASH polynomial is 128. -/
lemma ghashPoly_natDegree : (ghashPoly).natDegree = 128 := by
  unfold ghashPoly
  -- The polynomial is of the form A + B.
  -- If deg(B) < deg(A), then deg(A + B) = deg(A).
  rw [add_assoc, add_assoc, add_assoc]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · -- Goal 1: Prove natDegree (X^128) = 128
    exact natDegree_X_pow 128
  · -- Goal 2: Prove natDegree (X^7 + X^2 + X + 1) < natDegree (X^128)
    rw [←add_assoc, ←add_assoc]
    simp only [ghashTail_natDegree, natDegree_pow, natDegree_X, mul_one, Nat.reduceLT]

/-- The GHASH polynomial is monic. -/
lemma ghashPoly_monic : Monic ghashPoly := by
  unfold Monic leadingCoeff
  -- Use our degree lemma to look at the right index
  rw [ghashPoly_natDegree]
  unfold ghashPoly
  -- coeff (A + B) i = coeff A i + coeff B i
  rw [coeff_add, coeff_add, coeff_add, coeff_add]
  -- coeff (X^n) n = 1
  rw [coeff_X_pow 128, if_pos rfl]
  -- coeff (X^k) 128 = 0 for k < 128
  rw [coeff_X_pow 7, if_neg (by norm_num)]
  rw [coeff_X_pow 2, if_neg (by norm_num)]
  rw [coeff_X, if_neg (by norm_num)]
  rw [coeff_one, if_neg (by norm_num)]
  -- 1 + 0 + 0 + 0 + 0 = 1
  simp only [add_zero]

/-- The GHASH polynomial is nonzero. -/
lemma ghashPoly_ne_zero : ghashPoly ≠ 0 := ghashPoly_monic.ne_zero

lemma ghashPoly_degree : (ghashPoly).degree = 128 := by
  rw [degree_eq_natDegree (hp := by exact ghashPoly_ne_zero)]
  simp only [ghashPoly_natDegree, Nat.cast_ofNat]

lemma X_mod_ghashPoly : X % ghashPoly = X := by
  rw [mod_eq_self_iff (hq0 := by exact ghashPoly_ne_zero), ghashPoly_degree]
  simp only [degree_X, Nat.one_lt_ofNat]

/--
Reduction rule: X^128 % ghashPoly = ghashTail
-/
lemma X_pow_128_mod_ghashPoly : X^128 % ghashPoly = ghashTail := by
  have h : X^128 = ghashPoly - ghashTail := by
    rw [ghashPoly_eq_X_pow_add_tail]; simp only [add_sub_cancel_right]
  rw [h]
  rw [CharTwo.sub_eq_add] -- CharP 2 auto inferred from Polynomial.charP
  rw [CanonicalEuclideanDomain.add_mod_eq (hn := by exact ghashPoly_ne_zero)]
  simp only [EuclideanDomain.mod_self, zero_add]
  rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := by exact ghashPoly_ne_zero)]
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact ghashPoly_ne_zero)]
  rw [ghashPoly_degree, ghashTail_degree];
  norm_cast

/--
General reduction step: `(X^k * X^128) % P = (X^k * tail) % P`
This allows reducing terms like `X^130` to `X^2 * tail`.
Actually, we want `X^(128+k) % P = (X^k * tail) % P`.
-/
lemma reduce_degree_step (k : ℕ) : (X^(128+k)) % ghashPoly = (X^k * ghashTail) % ghashPoly := by
  rw [pow_add, CanonicalEuclideanDomain.mul_mod_eq (hn := by exact ghashPoly_ne_zero)]
  rw [X_pow_128_mod_ghashPoly]
  conv_rhs => rw [CanonicalEuclideanDomain.mul_mod_eq_mul_mod_left
    (hn := by exact ghashPoly_ne_zero), mul_comm]

end GHASHPolynomial

section VerificationFunctions

-- The "P" constant (X^128 + X^7 + X^2 + X + 1)
-- We represent it as a 256-bit vector
def P_val : B256 :=
  (1 <<< 128) ^^^ (1 <<< 7) ^^^ (1 <<< 2) ^^^ (1 <<< 1) ^^^ 1

-- Helper: toPoly (1 <<< n) is just X^n
lemma toPoly_one_shiftLeft {w : Nat} (n : Nat) (h : n < w) :
    toPoly (1 <<< n : BitVec w) = X^n := by
  rw [toPoly]
  rw [Finset.sum_eq_single (⟨n, h⟩ : Fin w)]
  -- 1. The Main Term (j = n): Prove it equals X^n
  · simp only
    simp only [BitVec.natCast_eq_ofNat, ite_eq_left_iff, Bool.not_eq_true]
    intro h_getLsb_eq_false
    have h_getLsb_eq_true : (BitVec.ofNat w (1 <<< n)).getLsb ⟨n, h⟩ = true := by
      rw [BitVec.getLsb]
      simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, h, decide_true, Nat.testBit_shiftLeft,
        ge_iff_le, le_refl, tsub_self, Nat.testBit_zero, Nat.mod_succ, Bool.and_self]
    rw [h_getLsb_eq_false] at h_getLsb_eq_true
    absurd h_getLsb_eq_true
    exact Bool.false_ne_true
  -- 2. The Other Terms (j ≠ n): Prove they are 0
  · intro b _ hb_ne_n_fin
    split_ifs with h_lsb
    · -- Contradiction: If bit is set, b must equal n
      exfalso
      have h_getLsb_eq_false : ((1 <<< n) : BitVec w).getLsb b = false := by
        rw [BitVec.getLsb]
        have h_lhs : ((1 <<< n) : BitVec w).toNat = 1 <<< n := by
          simp only [Nat.shiftLeft_eq, one_mul, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
          apply Nat.mod_eq_of_lt
          apply Nat.pow_lt_pow_right (ha := by omega) (h := by omega)
        rw [h_lhs]
        rw [Nat.one_shiftLeft]
        rw [Nat.testBit_two_pow];
        let h_ne := Fin.val_ne_of_ne hb_ne_n_fin
        exact decide_eq_false (id (Ne.symm h_ne))
      rw [h_getLsb_eq_false] at h_lsb
      absurd h_lsb
      exact Bool.false_ne_true
    · rfl -- If bit is not set, result is 0
  -- 3. Universe Check: Prove n is in Finset.univ
  · intro h_absurd
    simp at h_absurd -- Finset.univ contains everything

-- Main Proof
lemma ghashPoly_eq_P_val : ghashPoly = toPoly P_val := by
  rw [ghashPoly, P_val]
  repeat rw [toPoly_xor]
  rw [toPoly_one_shiftLeft (h := by omega), toPoly_one_shiftLeft (h := by omega),
    toPoly_one_shiftLeft (h := by omega), toPoly_one_shiftLeft (h := by omega)]
  rw [(show (1 : B256) = 1 <<< 0 by simp)]
  rw [toPoly_one_shiftLeft 0 (by omega)]
  simp only [pow_zero, pow_one]

def X_val : B128 := BitVec.ofNat 128 2
noncomputable def X_ZMod2Poly : Polynomial (ZMod 2) := toPoly X_val

lemma X_ZMod2Poly_eq_X : X_ZMod2Poly = X := by
  rw [X_ZMod2Poly, X_val]
  unfold toPoly
  -- For BitVec.ofNat 128 2, only bit 1 is set, so only X^1 = X contributes
  let i1 : Fin 128 := ⟨1, by decide⟩
  have h_i1_val : i1.val = 1 := by rfl
  -- Use h_ite pattern: show each term equals if b = i1 then X else 0
  have h_ite: ∀ b : Fin 128, (if (BitVec.ofNat 128 2).getLsb b then
    (X : (ZMod 2)[X])^b.val else 0) = if b = i1 then X else 0 := by
    intro b
    by_cases h_eq : b = i1
    · -- b = i1, so the bit is set and X^1 = X
      simp only [h_eq, BitVec.getLsb_eq_getElem, Fin.getElem_fin, h_i1_val, BitVec.reduceGetElem,
        ↓reduceIte, pow_one]
    · -- b ≠ i1, so b.val ≠ 1, so the bit is not set
      have h_val_ne_one : b.val ≠ 1 := by
        intro h_eq_val
        have h_b_eq_i1 : b = i1 := Fin.ext h_eq_val
        exact h_eq h_b_eq_i1
      simp only [BitVec.getLsb, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, h_eq, ↓reduceIte,
        ite_eq_right_iff, pow_eq_zero_iff', X_ne_zero, ne_eq, Fin.val_eq_zero_iff, Fin.isValue,
        false_and, imp_false, Bool.not_eq_true]
      rw [(show 2 = 2^1 by rfl)]
      rw [Nat.testBit_two_pow]
      simp only [decide_eq_false_iff_not, ne_eq]
      exact id (Ne.symm h_val_ne_one)
  simp only [h_ite]
  rw [Finset.sum_eq_single (a := i1) (h₀ := fun b hb_univ hb_ne_i1 => by
    simp only [hb_ne_i1, ↓reduceIte]
  ) (h₁ := fun h_i1_ne_mem_univ => by
    simp only [Finset.mem_univ, not_true_eq_false] at h_i1_ne_mem_univ
  )]
  simp only [↓reduceIte]

-- The check function (Executes in Kernel)
-- Returns true iff rPrev^2 == q * P + rNext
def checkSquareStep (rPrev : B128) (q : B128) (rNext : B128) : Bool :=
  let lhs := clSq rPrev
  let rhs := (clMul (to256 q) P_val) ^^^ (to256 rNext)
  lhs == rhs

-- The Soundness Theorem
-- This is what you apply in your 128 generated lemmas
theorem verify_square_step_correct (rPrev q rNext : B128) :
    checkSquareStep rPrev q rNext = true →
    (toPoly rPrev)^2 = (toPoly (to256 q)) * (toPoly P_val) + (toPoly rNext) := by
  intro h
  dsimp only [checkSquareStep] at h
  rw [beq_iff_eq] at h
  -- h is now: clSq rPrev = (clMul (to256 q) P_val) ^^^ (to256 rNext)
  -- The huge loop is still "folded" inside clSq/clMul, so it's fast.
  -- 3. Apply the bridge to the BitVec equation
  --    Now we transform the functions using theorems, rather than computing them.
  rw [clSq] at h -- Unfold clSq to clMul (only 1 step)
  apply_fun toPoly at h
  -- 4. Apply your Bridge Lemmas
  rw [toPoly_xor] at h
  have h_res : toPoly rPrev ^ 2 = toPoly (to256 q) * toPoly P_val + toPoly rNext := by
    rw [pow_two]
    rw [toPoly_128_extend_256] at ⊢ h
    have h_rPrev_lt : BitVec.toNat (to256 rPrev) < 2 ^ 128 := by
      rw [to256_toNat];
      exact BitVec.toNat_lt_twoPow_of_le (m := 128) (n := 128) (x := rPrev) (h := by omega)
    have h_q_lt : BitVec.toNat (to256 q) < 2 ^ 128 := by
      rw [to256_toNat];
      exact BitVec.toNat_lt_twoPow_of_le (m := 128) (n := 128) (x := q) (h := by omega)
    have h_P_val_lt : BitVec.toNat P_val < 2 ^ 129 := by
      unfold P_val
      simp only [Nat.reduceShiftLeft, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceXOr,
        BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT]
    conv_lhs at h =>
        rw [toPoly_clMul_no_overflow (da := 128) (db := 128) (ha := by omega)
          (hb := h_rPrev_lt) (h_sum := by omega)]
        rw [toPoly_128_extend_256]
    conv_rhs at h =>
      rw [toPoly_clMul_no_overflow (da := 128) (db := 129) (ha := by
        rw [to256_toNat]; exact h_q_lt) (hb := h_P_val_lt) (h_sum := by omega)]
      rw [toPoly_128_extend_256]
    rw [h]
  exact h_res

/-- Helper lemma to chain the modular squaring steps -/
lemma chain_step {k : ℕ} {prev next : Polynomial (ZMod 2)} {q_val : B128}
    (h_prev : X ^ (2 ^ k) % ghashPoly = prev % ghashPoly)
    (h_step : prev ^ 2 = (toPoly (to256 q_val)) * ghashPoly + next) :
  X^(2^(k+1)) % ghashPoly = next % ghashPoly := by
  rw [pow_succ', pow_mul, ←pow_mul, mul_comm, pow_mul, pow_two]
  rw [CanonicalEuclideanDomain.mul_mod_eq (hn := by exact ghashPoly_ne_zero), h_prev]
  rw [←CanonicalEuclideanDomain.mul_mod_eq (hn := by exact ghashPoly_ne_zero), ←pow_two]
  conv_lhs => rw [h_step, toPoly_128_extend_256]
  conv_lhs => rw [CanonicalEuclideanDomain.add_mod_eq (hn := by exact ghashPoly_ne_zero)]
  conv_lhs => rw [CanonicalEuclideanDomain.mul_mod_eq (hn := by exact ghashPoly_ne_zero)]
  conv_lhs => simp only [EuclideanDomain.mod_self, mul_zero, zero_add]
  conv_lhs => rw [EuclideanDomain.zero_mod, zero_add]
  rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := by exact ghashPoly_ne_zero)]

-- 3. We can reuse 'verify_step_correct' for the division check!
-- Recall: verify_step_correct checks: rPrev^2 = q * P + rNext
-- WE NEED A NEW ONE for simple linear division: A = Q * B + R
def checkDivStep (a : B256) (q : B256) (b : B256) (r : B256) : Bool :=
  let rhs := (clMul q b) ^^^ r
  a == rhs

theorem verify_div_step (a q b r : B256) (hq : q.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) :
  -- for rabin gcd condition
  checkDivStep a q b r = true → -- check q * b + (XOR) r = a
  toPoly a = (toPoly q) * (toPoly b) + (toPoly r) := by
  intro h
  dsimp only [checkDivStep] at h
  rw [beq_iff_eq] at h
  apply_fun toPoly at h
  rw [toPoly_xor] at h
  rw [toPoly_clMul_no_overflow (da := 128) (db := 128) (ha := hq) (hb := hb)
    (h_sum := by omega)] at h
  exact h

end VerificationFunctions

end BF128Ghash
