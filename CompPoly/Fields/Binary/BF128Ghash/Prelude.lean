/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Dimitris Mitsios
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
set_option maxRecDepth 550 -- for ghashPoly_eq_P_val

open Polynomial AdjoinRoot BinaryField

-- Re-export common definitions for convenience
export BinaryField (B128 B256 to256 to256_toNat clMul clSq toPoly clMul_unfold
  toPoly_one_eq_one toPoly_zero_eq_zero toPoly_ne_zero_iff_ne_zero
  toPoly_degree_lt_w toPoly_degree_of_lt_two_pow BitVec_lt_two_pow_of_toPoly_degree_lt
  toPoly_xor toPoly_fold_xor toPoly_128_extend_256 toPoly_shiftLeft_no_overflow
  toPoly_clMul gcd_eq_gcd_next_step gcd_one_zero)

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

end VerificationFunctions

/-! ### Kernel-Efficient Checkers -/

section KernelEfficientCheckers

/-- Carry-less (polynomial) multiply using structural recursion on `n`,
    iterating over bits `0 .. n-1` of `a`.
    Uses only `Nat.testBit`, `Nat.xor`, `Nat.shiftLeft` —
    no `Finset.fold`, no `BitVec`, no `Nat.mod`. -/
def clMulNat (a b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let prev := clMulNat a b n
    if a.testBit n then prev ^^^ (b <<< n) else prev

/-- Carry-less square via `clMulNat`. -/
abbrev clSqNat (a n : Nat) : Nat := clMulNat a a n

/-- Specialized carry-less multiply by `P_val` (the GHASH polynomial
    `P(X) = X^128 + X^7 + X^2 + X + 1`).
    `P_val` has bits set at positions `{0, 1, 2, 7, 128}`, so we hardcode the
    5 XOR-shift operations instead of iterating over all bits. -/
def mulByP_Nat (a : Nat) : Nat :=
  a ^^^ (a <<< 1) ^^^ (a <<< 2) ^^^ (a <<< 7) ^^^ (a <<< 128)

/-- Kernel-efficient version of `checkSquareStep`.
    The public API stays on `B128`, but the internal computation runs on `Nat`
    using `clSqNat` and the specialized `mulByP_Nat` helper. -/
def checkSquareStep (rPrev q rNext : B128) : Bool :=
  let lhs := clSqNat rPrev.toNat 128
  let rhs := mulByP_Nat q.toNat ^^^ rNext.toNat
  lhs == rhs

/-- Kernel-efficient version of `checkDivStep`.
    Preserves the full `B256` semantics of the public checker, but computes via
    `Nat` structural recursion instead of the `BitVec` fold. -/
def checkDivStep (a q b r : B256) : Bool :=
  let rhs := clMulNat q.toNat b.toNat 256 ^^^ r.toNat
  a.toNat == rhs

/-- If `a < 2^m`, then iterating `clMulNat` beyond bit `m-1` is a no-op,
    because `a.testBit i = false` for all `i ≥ m`. -/
theorem clMulNat_high_bits_zero (a b m n : Nat) (hmn : m ≤ n) (ha : a < 2 ^ m) :
    clMulNat a b n = clMulNat a b m := by
  induction n with
  | zero => simp [show m = 0 by omega]
  | succ k ih =>
    by_cases hk : m ≤ k
    · have h_bit : a.testBit k = false :=
        Nat.testBit_lt_two_pow
          (lt_of_lt_of_le ha (pow_le_pow_right' (by omega : 1 ≤ 2) hk))
      have step : clMulNat a b (k + 1) = clMulNat a b k := by
        show (if a.testBit k then (clMulNat a b k) ^^^ (b <<< k)
              else clMulNat a b k) = clMulNat a b k
        simp [h_bit]
      rw [step]; exact ih (by omega)
    · simp [show m = k + 1 by omega]

/-- Reinterpret a bounded `Nat` as the zero-extended 256-bit vector. -/
private theorem ofNat_to256 (x : B128) : (BitVec.ofNat 256 x.toNat : B256) = to256 x := by
  apply BitVec.eq_of_toNat_eq
  rw [to256_toNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt (by omega))

/-- Reinterpret a 256-bit vector's `toNat` back as the original bitvector. -/
private theorem ofNat_toB256 (x : B256) : (BitVec.ofNat 256 x.toNat : B256) = x := by
  simp [BitVec.ofNat_toNat]

/-- `BitVec.ofNat 256` transports `Nat.xor` to `BitVec.xor`. -/
private theorem ofNat_xor_256 (x y : Nat) :
    (BitVec.ofNat 256 (x ^^^ y) : B256) =
      (BitVec.ofNat 256 x : B256) ^^^ (BitVec.ofNat 256 y : B256) := by
  apply BitVec.eq_of_toNat_eq
  change (x ^^^ y) % 2 ^ 256 =
    (((BitVec.ofNat 256 x : B256) ^^^ (BitVec.ofNat 256 y : B256)).toNat)
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.xor_mod_two_pow]

/-- `BitVec.ofNat 256` transports left shift modulo `2^256`. -/
private theorem ofNat_shiftLeft_256 (x n : Nat) :
    (BitVec.ofNat 256 (x <<< n) : B256) =
      ((BitVec.ofNat 256 x : B256) <<< n) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- Bitvector view of `clMulNat`: a `range`-fold using the same xor/shift pattern. -/
private theorem clMulNat_bv_eq_fold_range (a b : Nat) :
    ∀ n,
      (BitVec.ofNat 256 (clMulNat a b n) : B256) =
        (Finset.range n).fold BitVec.xor 0
          (fun i => if a.testBit i then ((BitVec.ofNat 256 b : B256) <<< i) else 0)
  | 0 => by simp [clMulNat]
  | n + 1 => by
      rw [Finset.range_add_one, Finset.fold_insert (by simp)]
      by_cases hbit : a.testBit n
      · simp [clMulNat, hbit, clMulNat_bv_eq_fold_range a b n,
          ofNat_shiftLeft_256, BitVec.xor_comm]
      · simp [clMulNat, hbit, clMulNat_bv_eq_fold_range a b n]

/-- Rewrite `clMul` from a fold over `Fin 128` to a fold over `range 128`. -/
private theorem clMul_eq_fold_range (a b : B128) :
    clMul a b =
      (Finset.range 128).fold BitVec.xor 0
        (fun i => if a.toNat.testBit i then (to256 b) <<< i else 0) := by
      rw [clMul_unfold, fold_range_xor_eq_foldl]
      rfl

/-- The 256-step Nat checker matches `clMul` on all `B256` inputs. -/
private theorem clMulNat_bv_eq_clMul (a b : B128) :
    (BitVec.ofNat 256 (clMulNat a.toNat b.toNat 128) : B256) = clMul a b := by
    rw [ clMulNat_bv_eq_fold_range, clMul_eq_fold_range]
    rw [← to256_toNat b, ofNat_toB256]

private theorem toNat_truncate_of_lt {n m : Nat} (v : BitVec n)
    (hv : v.toNat < 2^m) :
    (v.truncate m).toNat = v.toNat := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt hv

theorem to256_truncate_128 (v : B256) (hv : v.toNat < 2^128) :
    to256 (v.truncate 128) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [to256_toNat, toNat_truncate_of_lt v hv]

theorem toPoly_truncate_128 (v : B256) (hv : v.toNat < 2^128) :
    toPoly (v.truncate 128) = toPoly v := by
  rw [← toPoly_128_extend_256, to256_truncate_128 v hv]

theorem toPoly_clMul_B256 (q b : B256) (hq : q.toNat < 2^128) (hb : b.toNat < 2^128) :
    toPoly (clMul (q.truncate 128) (b.truncate 128)) = toPoly q * toPoly b := by
      rw [toPoly_clMul, toPoly_truncate_128 q hq, toPoly_truncate_128 b hb]

/-- Bitvector semantics of `clSqNat` for a 128-bit input. -/
private theorem clSqNat_bv_eq_clSq (x : B128) :
    (BitVec.ofNat 256 (clSqNat x.toNat 128) : B256) = clSq x := by
  have hx : (to256 x).toNat < 2 ^ 128 := by
    rw [to256_toNat]
    exact x.isLt
  simpa [clSqNat, clSq, to256_toNat] using
    (clMulNat_bv_eq_clMul x x)

/-- Polynomial semantics of `clSqNat` for a 128-bit input. -/
private theorem toPoly_clSqNat_eq_sq (x : B128) :
    toPoly (BitVec.ofNat 256 (clSqNat x.toNat 128)) = (toPoly x) ^ 2 := by
      rw [clSqNat_bv_eq_clSq x, clSq, toPoly_clMul, pow_two]

/-- Shift a 128-bit input inside 256 bits without changing its polynomial meaning. -/
private theorem toPoly_ofNat_shiftLeft_to256 (x : B128) (shift : Nat) (hshift : 128 + shift ≤ 256) :
    toPoly (BitVec.ofNat 256 (x.toNat <<< shift)) = (toPoly (to256 x)) * X ^ shift := by
  have hx : (to256 x).toNat < 2 ^ 128 := by
    rw [to256_toNat]
    exact x.isLt
  have hEq : (BitVec.ofNat 256 (x.toNat <<< shift) : B256) = (to256 x) <<< shift := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, to256_toNat, BitVec.toNat_ofNat]
  rw [hEq]
  exact toPoly_shiftLeft_no_overflow (a := to256 x) hx (shift := shift) hshift

/-- Polynomial semantics of the specialized GHASH multiplication by `P_val`. -/
private theorem toPoly_mulByP_Nat (x : B128) :
    toPoly (BitVec.ofNat 256 (mulByP_Nat x.toNat)) = (toPoly (to256 x)) * (toPoly P_val) := by
  unfold mulByP_Nat
  rw [ofNat_xor_256, ofNat_xor_256, ofNat_xor_256, ofNat_xor_256]
  repeat rw [toPoly_xor]
  rw [ofNat_to256]
  rw [toPoly_ofNat_shiftLeft_to256 x 1 (by omega)]
  rw [toPoly_ofNat_shiftLeft_to256 x 2 (by omega)]
  rw [toPoly_ofNat_shiftLeft_to256 x 7 (by omega)]
  rw [toPoly_ofNat_shiftLeft_to256 x 128 (by omega)]
  rw [← ghashPoly_eq_P_val, ghashPoly]
  ring

/-- Soundness of the kernel-efficient square-step checker. -/
theorem verify_square_step_correct (rPrev q rNext : B128) :
    checkSquareStep rPrev q rNext = true →
    (toPoly rPrev) ^ 2 = (toPoly (to256 q)) * (toPoly P_val) + (toPoly rNext) := by
  intro h
  unfold checkSquareStep at h
  rw [beq_iff_eq] at h
  have hBv : (BitVec.ofNat 256 (clSqNat rPrev.toNat 128) : B256) =
      (BitVec.ofNat 256 (mulByP_Nat q.toNat ^^^ rNext.toNat) : B256) := by
    simpa using congrArg (fun n => (BitVec.ofNat 256 n : B256)) h
  rw [clSqNat_bv_eq_clSq rPrev, ofNat_xor_256, ofNat_to256 rNext] at hBv
  apply_fun toPoly at hBv
  rw [clSq, toPoly_xor, toPoly_mulByP_Nat, toPoly_128_extend_256] at hBv
  have hr : (to256 rPrev).toNat < 2 ^ 128 := by
    rw [to256_toNat]
    exact rPrev.isLt
  rw [toPoly_clMul rPrev rPrev, toPoly_128_extend_256] at hBv
  simpa [pow_two, toPoly_128_extend_256] using hBv

/-- Soundness of the kernel-efficient division-step checker. -/
theorem verify_div_step_bounded (a q b r : B256) (hq : q.toNat < 2 ^ 128)
    (hb : b.toNat < 2 ^ 128) :
    a.toNat = clMulNat q.toNat b.toNat 128 ^^^ r.toNat →
    toPoly a = (toPoly q) * (toPoly b) + (toPoly r) := by
  intro h
  have hBv : (BitVec.ofNat 256 a.toNat : B256) =
      (BitVec.ofNat 256 (clMulNat q.toNat b.toNat 128 ^^^ r.toNat) : B256) := by
    simpa using congrArg (fun n => (BitVec.ofNat 256 n : B256)) h
  rw [ofNat_toB256 a, ofNat_xor_256, ofNat_toB256 r] at hBv
  rw [← toNat_truncate_of_lt q hq, ← toNat_truncate_of_lt b hb,
      clMulNat_bv_eq_clMul (q.truncate 128) (b.truncate 128)] at hBv
  apply_fun toPoly at hBv
  rw [toPoly_xor, toPoly_clMul_B256 q b hq hb] at hBv
  exact hBv

/-- Soundness of the kernel-efficient division-step checker. -/
theorem verify_div_step (a q b r : B256) (hq : q.toNat < 2 ^ 128)
    (hb : b.toNat < 2 ^ 128) :
    checkDivStep a q b r = true →
    toPoly a = (toPoly q) * (toPoly b) + (toPoly r) := by
  intro h
  unfold checkDivStep at h
  rw [beq_iff_eq] at h
  have hBv : (BitVec.ofNat 256 a.toNat : B256) =
      (BitVec.ofNat 256 (clMulNat q.toNat b.toNat 256 ^^^ r.toNat) : B256) := by
    simpa using congrArg (fun n => (BitVec.ofNat 256 n : B256)) h
  rw [ofNat_toB256 a, ofNat_xor_256, ofNat_toB256 r] at hBv
  rw [clMulNat_high_bits_zero q.toNat b.toNat 128 256 (by omega) hq] at hBv
  rw [← toNat_truncate_of_lt q hq, ← toNat_truncate_of_lt b hb,
      clMulNat_bv_eq_clMul (q.truncate 128) (b.truncate 128)] at hBv
  apply_fun toPoly at hBv
  rw [toPoly_xor, toPoly_clMul_B256 q b hq hb] at hBv
  exact hBv

end KernelEfficientCheckers

end BF128Ghash
