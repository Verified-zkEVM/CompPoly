/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.Goldilocks.FastDefs

/-!
# Fast Goldilocks: word-level correctness

Correctness of the raw `UInt64` kernels in `CompPoly.Fields.Goldilocks.FastDefs`:
low-level word lemmas (limb splitting, borrow and overflow correction, the 64-by-64
product decomposition), then for each kernel a bound showing the result is below the
modulus and a cast lemma identifying it with the corresponding operation in
`Goldilocks.Field`.

The field carrier and its API are built on these in
`CompPoly.Fields.Goldilocks.Fast`.
-/

@[expose] public section

namespace Goldilocks
namespace Fast

/-! ## Low-level `UInt64` lemmas -/

/-- The native `UInt64` modulus agrees with the mathematical Goldilocks modulus. -/
@[simp]
theorem modulus_toNat : modulus.toNat = Goldilocks.fieldSize := by
  decide

/-- The native negated-modulus constant agrees with `2^32 - 1`. -/
@[simp]
theorem negModulus_toNat : negModulus.toNat = 2 ^ 32 - 1 := by
  decide

/-- The Goldilocks modulus is positive. -/
theorem fieldSize_pos : 0 < Goldilocks.fieldSize := by
  decide

/-- The Goldilocks modulus fits in a `UInt64`. -/
theorem fieldSize_lt_uint64Size : Goldilocks.fieldSize < UInt64.size := by
  decide

/-- Every `UInt64` value is below twice the Goldilocks modulus. -/
theorem uint64_toNat_lt_two_fieldSize (x : UInt64) :
    x.toNat < 2 * Goldilocks.fieldSize := by
  exact Nat.lt_trans (UInt64.toNat_lt_size x) (by decide)

/-- The folding congruence used by the Goldilocks reducer.

`2^64 ≡ 2^32 - 1 (mod p)`.
-/
theorem uint64_cast_eq_negModulus :
    (UInt64.size : Goldilocks.Field) = (negModulus.toNat : Goldilocks.Field) := by
  decide

/-- Multiplying by `2^32 - 1` after shifting by `2^32` is negation modulo Goldilocks. -/
theorem pow32_mul_negModulus_cast :
    ((2 ^ 32 : Nat) : Goldilocks.Field) *
        (negModulus.toNat : Goldilocks.Field) =
      -1 := by
  decide

/-- Right shifting a `UInt64` by 32 gives division by `2^32` on naturals. -/
theorem shiftRight32_toNat (x : UInt64) :
    (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]
  have h : (32 : UInt64).toNat % 64 = 32 := by
    decide
  rw [h, Nat.shiftRight_eq_div_pow]

/-- Masking with `2^32 - 1` gives the low 32 bits on naturals. -/
theorem and_negModulus_toNat (x : UInt64) :
    (x &&& negModulus).toNat = x.toNat % 2 ^ 32 := by
  rw [← UInt64.toNat_toBitVec (x &&& negModulus)]
  rw [UInt64.toBitVec_and]
  rw [BitVec.toNat_and]
  rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec]
  rw [negModulus_toNat]
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- A `UInt64` subtraction with the Goldilocks borrow correction represents subtraction modulo `p`.

The assumption says the subtrahend is a 32-bit limb, which is the case for
`hi >>> 32` in the 128-bit reducer.
-/
theorem subBorrow_cast (a b : UInt64) (hb : b.toNat < 2 ^ 32) :
    (((if a < b then a - b - negModulus else a - b).toNat) : Goldilocks.Field) =
      (a.toNat : Goldilocks.Field) - (b.toNat : Goldilocks.Field) := by
  by_cases h : a < b
  · rw [ite_eq_left h]
    have hlt : a.toNat < b.toNat := by
      simpa [UInt64.lt_iff_toNat_lt] using h
    have hb_le_size : b.toNat ≤ UInt64.size := Nat.le_of_lt (UInt64.toNat_lt_size b)
    have hsub_lt_size : UInt64.size - b.toNat + a.toNat < 2 ^ 64 := by
      have hsize : UInt64.size = 2 ^ 64 := rfl
      rw [hsize] at hb_le_size ⊢
      omega
    have hsub_raw : (a - b).toNat = UInt64.size - b.toNat + a.toNat := by
      rw [UInt64.toNat_sub]
      exact Nat.mod_eq_of_lt hsub_lt_size
    have hneg_le : negModulus ≤ a - b := by
      rw [UInt64.le_iff_toNat_le]
      rw [hsub_raw, negModulus_toNat]
      have hsize : UInt64.size = 2 ^ 64 := rfl
      rw [hsize]
      omega
    rw [UInt64.toNat_sub_of_le _ _ hneg_le]
    rw [hsub_raw]
    have hneg_le_nat : negModulus.toNat ≤ UInt64.size - b.toNat + a.toNat := by
      rw [← hsub_raw]
      rwa [UInt64.le_iff_toNat_le] at hneg_le
    rw [Nat.cast_sub hneg_le_nat]
    rw [Nat.cast_add]
    rw [Nat.cast_sub hb_le_size]
    rw [uint64_cast_eq_negModulus]
    ring
  · rw [ite_eq_right h]
    have hle : b ≤ a := by
      rw [UInt64.le_iff_toNat_le]
      rw [UInt64.lt_iff_toNat_lt] at h
      exact Nat.le_of_not_gt h
    have hle_nat : b.toNat ≤ a.toNat := by
      rwa [UInt64.le_iff_toNat_le] at hle
    rw [UInt64.toNat_sub_of_le _ _ hle]
    rw [Nat.cast_sub hle_nat]

/-- A bounded `UInt64` addition with the Goldilocks overflow correction represents
addition modulo `p`. -/
theorem addOverflowBounded_cast (a b : UInt64)
    (hbound : a.toNat + b.toNat < 2 * UInt64.size - negModulus.toNat) :
    (((if a + b < a then a + b + negModulus else a + b).toNat) :
      Goldilocks.Field) =
      (a.toNat : Goldilocks.Field) + (b.toNat : Goldilocks.Field) := by
  by_cases hsum : a.toNat + b.toNat < UInt64.size
  · have hnot : ¬a + b < a := by
      intro hlt
      have hlt_nat : (a + b).toNat < a.toNat := by
        simpa [UInt64.lt_iff_toNat_lt] using hlt
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum] at hlt_nat
      omega
    rw [ite_eq_right hnot]
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hsum, Nat.cast_add]
  · have hsize_le : UInt64.size ≤ a.toNat + b.toNat := Nat.le_of_not_gt hsum
    have hlt : a + b < a := by
      rw [UInt64.lt_iff_toNat_lt]
      rw [UInt64.toNat_add]
      rw [Nat.mod_eq_sub_mod hsize_le]
      have hdiff_lt : a.toNat + b.toNat - UInt64.size < UInt64.size := by
        have ha := UInt64.toNat_lt_size a
        have hb := UInt64.toNat_lt_size b
        omega
      rw [Nat.mod_eq_of_lt hdiff_lt]
      have hb := UInt64.toNat_lt_size b
      omega
    rw [ite_eq_left hlt]
    have hsum_mod : (a + b).toNat = a.toNat + b.toNat - UInt64.size := by
      rw [UInt64.toNat_add]
      rw [Nat.mod_eq_sub_mod hsize_le]
      have hdiff_lt : a.toNat + b.toNat - UInt64.size < UInt64.size := by
        have ha := UInt64.toNat_lt_size a
        have hb := UInt64.toNat_lt_size b
        omega
      rw [Nat.mod_eq_of_lt hdiff_lt]
    rw [UInt64.toNat_add]
    rw [hsum_mod]
    have hno_second : a.toNat + b.toNat - UInt64.size + negModulus.toNat < UInt64.size := by
      omega
    rw [Nat.mod_eq_of_lt hno_second]
    rw [Nat.cast_add]
    rw [Nat.cast_sub hsize_le]
    rw [uint64_cast_eq_negModulus]
    rw [Nat.cast_add]
    ring

/-- Multiplication by `2^32 - 1` does not overflow for a 32-bit limb. -/
theorem mul_negModulus_toNat_of_lt (x : UInt64) (hx : x.toNat < 2 ^ 32) :
    (x * negModulus).toNat = x.toNat * negModulus.toNat := by
  rw [UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt]
  rw [negModulus_toNat]
  omega

/-- The product of a 32-bit limb by `2^32 - 1` leaves enough headroom for correction. -/
theorem mul_negModulus_toNat_le (x : UInt64) (hx : x.toNat < 2 ^ 32) :
    (x * negModulus).toNat ≤ UInt64.size - 2 * negModulus.toNat := by
  rw [mul_negModulus_toNat_of_lt x hx]
  rw [negModulus_toNat]
  have hx_le : x.toNat ≤ 2 ^ 32 - 1 := by
    omega
  have hmul : x.toNat * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul_right _ hx_le
  have hconst : (2 ^ 32 - 1) * (2 ^ 32 - 1) ≤ UInt64.size - 2 * (2 ^ 32 - 1) := by
    decide
  exact Nat.le_trans hmul hconst

/-- Splitting a high word into 32-bit limbs matches the Goldilocks folding congruence. -/
theorem hi_split_cast (hi : UInt64) :
    (hi.toNat : Goldilocks.Field) * (UInt64.size : Goldilocks.Field) =
      ((hi &&& negModulus).toNat : Goldilocks.Field) *
          (negModulus.toNat : Goldilocks.Field) -
        ((hi >>> 32).toNat : Goldilocks.Field) := by
  have hsplit_nat : hi.toNat = hi.toNat % 2 ^ 32 + 2 ^ 32 * (hi.toNat / 2 ^ 32) := by
    rw [Nat.mod_add_div]
  have hcast_split :
      (hi.toNat : Goldilocks.Field) =
        ((hi.toNat % 2 ^ 32 : Nat) : Goldilocks.Field) +
          (((2 ^ 32 : Nat) : Goldilocks.Field) *
            ((hi.toNat / 2 ^ 32 : Nat) : Goldilocks.Field)) := by
    simpa [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun n : Nat => (n : Goldilocks.Field)) hsplit_nat
  rw [hcast_split]
  rw [and_negModulus_toNat, shiftRight32_toNat, uint64_cast_eq_negModulus]
  rw [add_mul]
  conv_lhs =>
    enter [2]
    rw [mul_assoc]
    rw [mul_comm ((hi.toNat / 2 ^ 32 : Nat) : Goldilocks.Field)]
    rw [← mul_assoc]
    rw [pow32_mul_negModulus_cast]
  ring

/-- A `UInt64` value decomposes into its low and high 32-bit limbs. -/
theorem uint64_split32 (x : UInt64) :
    x.toNat = (x &&& negModulus).toNat + 2 ^ 32 * (x >>> 32).toNat := by
  rw [and_negModulus_toNat, shiftRight32_toNat]
  rw [Nat.mod_add_div]

/-- The low 32-bit limb of a `UInt64` is below `2^32`. -/
theorem uint64_low32_lt (x : UInt64) :
    (x &&& negModulus).toNat < 2 ^ 32 := by
  rw [and_negModulus_toNat]
  exact Nat.mod_lt _ (by decide)

/-- The high 32-bit limb of a `UInt64` is below `2^32`. -/
theorem uint64_high32_lt (x : UInt64) :
    (x >>> 32).toNat < 2 ^ 32 := by
  rw [shiftRight32_toNat]
  have hx := UInt64.toNat_lt_size x
  change x.toNat < 2 ^ 64 at hx
  exact Nat.div_lt_of_lt_mul hx

/-- Multiplying two 32-bit limbs does not overflow `UInt64`. -/
theorem mul32_toNat (a b : UInt64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt]
  nlinarith

/-- Algebraic decomposition of a product after splitting both factors into 32-bit limbs. -/
theorem product_split32 (x y : UInt64) :
    x.toNat * y.toNat =
      (x &&& negModulus).toNat * (y &&& negModulus).toNat +
        2 ^ 32 *
          ((x &&& negModulus).toNat * (y >>> 32).toNat +
            (x >>> 32).toNat * (y &&& negModulus).toNat) +
          2 ^ 64 * ((x >>> 32).toNat * (y >>> 32).toNat) := by
  rw [uint64_split32 x, uint64_split32 y]
  ring_nf

/-- Low word returned by a 64-by-64 product implementation. -/
theorem wideMul_low_toNat (lo : UInt64) (x y : UInt64) (hlo : lo = x * y) :
    lo.toNat = x.toNat * y.toNat % UInt64.size := by
  rw [hlo, UInt64.toNat_mul]

/-- Carry formula for the high word of a 32-bit-limb product. -/
private theorem wideMul_hi_nat (p00 p01 p10 p11 : Nat) :
    p11 + (p00 / 2 ^ 32 + p01) / 2 ^ 32 + ((p00 / 2 ^ 32 + p01) % 2 ^ 32 + p10) / 2 ^ 32 =
      (p00 + 2 ^ 32 * (p01 + p10) + 2 ^ 64 * p11) / 2 ^ 64 := by
  omega

/-- The high word of `wideMul` is the high half of the product. -/
theorem wideMul_snd_toNat (x y : UInt64) :
    (wideMul x y).2.toNat = x.toNat * y.toNat / 2 ^ 64 := by
  have hxLo := uint64_low32_lt x
  have hxHi := uint64_high32_lt x
  have hyLo := uint64_low32_lt y
  have hyHi := uint64_high32_lt y
  have hp00 := mul32_toNat _ _ hxLo hyLo
  have hp01 := mul32_toNat _ _ hxLo hyHi
  have hp10 := mul32_toNat _ _ hxHi hyLo
  have hp11 := mul32_toNat _ _ hxHi hyHi
  have hwide := wideMul_hi_nat ((x &&& negModulus).toNat * (y &&& negModulus).toNat)
    ((x &&& negModulus).toNat * (y >>> 32).toNat) ((x >>> 32).toNat * (y &&& negModulus).toNat)
    ((x >>> 32).toNat * (y >>> 32).toNat)
  have h00 : (x &&& negModulus).toNat * (y &&& negModulus).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h01 : (x &&& negModulus).toNat * (y >>> 32).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h10 : (x >>> 32).toNat * (y &&& negModulus).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h11 : (x >>> 32).toNat * (y >>> 32).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [product_split32 x y]
  simp only [wideMul, UInt64.toNat_add, shiftRight32_toNat, and_negModulus_toNat, hp00, hp01,
    hp10, hp11] at hwide h00 h01 h10 h11 hxLo hxHi hyLo hyHi ⊢
  omega

/-- Combined semantic correctness of a 64-by-64 product represented by low and high words. -/
theorem wideMul_cast
    (x y lo hi : UInt64)
    (hlo : lo = x * y)
    (hhi : hi.toNat = x.toNat * y.toNat / UInt64.size) :
    (lo.toNat : Goldilocks.Field) +
        (hi.toNat : Goldilocks.Field) * (UInt64.size : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) * (y.toNat : Goldilocks.Field) := by
  rw [wideMul_low_toNat lo x y hlo, hhi]
  rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mul_comm (x.toNat * y.toNat / UInt64.size),
    Nat.mod_add_div, Nat.cast_mul]

/-! ## Raw kernel correctness -/

/-- The raw one-word reducer returns a canonical representative. -/
theorem reduceUInt64Raw_lt (x : UInt64) :
    (reduceUInt64Raw x).toNat < Goldilocks.fieldSize := by
  unfold reduceUInt64Raw
  by_cases hx : x < modulus
  · rw [ite_eq_left hx]
    rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
    exact hx
  · rw [ite_eq_right hx]
    have hmod_le_x_nat : Goldilocks.fieldSize ≤ x.toNat := by
      rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    have hmod_le_x : modulus ≤ x := by
      rw [UInt64.le_iff_toNat_le, modulus_toNat]
      exact hmod_le_x_nat
    rw [UInt64.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
    have hx_lt_two := uint64_toNat_lt_two_fieldSize x
    omega

/-- One-word reduction preserves the represented canonical field element. -/
theorem reduceUInt64Raw_cast (x : UInt64) :
    ((reduceUInt64Raw x).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) := by
  unfold reduceUInt64Raw
  by_cases hx : x < modulus
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx]
    have hmod_le_x : modulus ≤ x := by
      rw [UInt64.le_iff_toNat_le, modulus_toNat]
      rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [UInt64.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt64.le_iff_toNat_le, modulus_toNat] at hmod_le_x
      exact hmod_le_x)]
    simp

/-- Tail of the 128-bit fold: add the middle term and correct one overflow. -/
private theorem foldTail_cast (lo hiHi hiLo t0 : UInt64) (hhiLo : hiLo.toNat < 2 ^ 32)
    (ht0 : (t0.toNat : Goldilocks.Field) =
      (lo.toNat : Goldilocks.Field) - (hiHi.toNat : Goldilocks.Field)) :
    (((if t0 + hiLo * negModulus < t0 then t0 + hiLo * negModulus + negModulus
        else t0 + hiLo * negModulus)).toNat : Goldilocks.Field) =
      (lo.toNat : Goldilocks.Field) - (hiHi.toNat : Goldilocks.Field) +
        (hiLo.toNat : Goldilocks.Field) * (negModulus.toNat : Goldilocks.Field) := by
  have ht1 : ((hiLo * negModulus).toNat : Goldilocks.Field) =
      (hiLo.toNat : Goldilocks.Field) * (negModulus.toNat : Goldilocks.Field) := by
    rw [mul_negModulus_toNat_of_lt hiLo hhiLo, Nat.cast_mul]
  have hsum : t0.toNat + (hiLo * negModulus).toNat < 2 * UInt64.size - negModulus.toNat := by
    have ht0 := UInt64.toNat_lt_size t0
    have ht1 := mul_negModulus_toNat_le hiLo hhiLo
    have htwice : 2 * negModulus.toNat ≤ UInt64.size := by decide
    omega
  rw [addOverflowBounded_cast t0 (hiLo * negModulus) hsum, ht0, ht1]

/-- The middle limb times `2^32 - 1`, formed as a shift and a subtraction. -/
theorem shiftLeft32_sub_low (hi : UInt64) :
    (hi <<< 32) - (hi &&& negModulus) = (hi &&& negModulus) * negModulus := by
  apply UInt64.toNat_inj.mp
  have hlo := uint64_low32_lt hi
  have hhi := UInt64.toNat_lt_size hi
  have hshl : (hi <<< 32).toNat = (hi &&& negModulus).toNat * 2 ^ 32 := by
    rw [UInt64.toNat_shiftLeft, and_negModulus_toNat]
    have h : (32 : UInt64).toNat % 64 = 32 := by decide
    rw [h, Nat.shiftLeft_eq]
    simp only [UInt64.size] at hhi
    omega
  have hle : (hi &&& negModulus) ≤ hi <<< 32 := by
    rw [UInt64.le_iff_toNat_le, hshl]
    omega
  rw [UInt64.toNat_sub_of_le _ _ hle, hshl, mul_negModulus_toNat_of_lt _ hlo, negModulus_toNat]
  omega

/-- The lazy fold represents `lo + hi * 2^64`. -/
theorem foldUInt128Lazy_cast (lo hi : UInt64) :
    ((foldUInt128Lazy lo hi).toNat : Goldilocks.Field) =
      (lo.toNat : Goldilocks.Field) +
        (hi.toNat : Goldilocks.Field) * (UInt64.size : Goldilocks.Field) := by
  have hhiLo := uint64_low32_lt hi
  have hsub := subBorrow_cast lo (hi >>> 32) (uint64_high32_lt hi)
  rw [hi_split_cast hi]
  simp only [foldUInt128Lazy, foldUInt128Borrow]
  by_cases hborrow : lo < hi >>> 32
  · rw [ite_eq_left hborrow] at hsub ⊢
    rw [foldTail_cast lo (hi >>> 32) (hi &&& negModulus) _ hhiLo hsub]
    ring
  · rw [ite_eq_right hborrow] at hsub ⊢
    rw [shiftLeft32_sub_low hi, foldTail_cast lo (hi >>> 32) (hi &&& negModulus) _ hhiLo hsub]
    ring

/-- The raw 128-bit reducer returns a canonical representative below the modulus. -/
theorem reduceUInt128Raw_lt (lo hi : UInt64) :
    (reduceUInt128Raw lo hi).toNat < Goldilocks.fieldSize :=
  reduceUInt64Raw_lt _

/-- Semantic correctness of raw 128-bit Goldilocks reduction. -/
theorem reduceUInt128Raw_cast (lo hi : UInt64) :
    ((reduceUInt128Raw lo hi).toNat : Goldilocks.Field) =
      (lo.toNat : Goldilocks.Field) +
        (hi.toNat : Goldilocks.Field) * (UInt64.size : Goldilocks.Field) := by
  unfold reduceUInt128Raw
  rw [reduceUInt64Raw_cast, foldUInt128Lazy_cast]

/-- The lazy product of any two words represents their product. -/
@[simp]
theorem mulLazy_cast (x y : UInt64) :
    ((mulLazy x y).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) * (y.toNat : Goldilocks.Field) := by
  unfold mulLazy
  rw [foldUInt128Lazy_cast]
  exact wideMul_cast x y _ _ rfl (wideMul_snd_toNat x y)

/-- Product reduction returns a canonical representative below the modulus. -/
theorem reduceMulRaw_lt (x y : UInt64) :
    (reduceMulRaw x y).toNat < Goldilocks.fieldSize :=
  reduceUInt64Raw_lt _

/-- Semantic correctness of native 64-by-64 product reduction. -/
theorem reduceMulRaw_cast (x y : UInt64) :
    ((reduceMulRaw x y).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) * (y.toNat : Goldilocks.Field) := by
  unfold reduceMulRaw
  rw [reduceUInt64Raw_cast, mulLazy_cast]

/-- Raw addition of canonical words computes the reduced sum. -/
theorem addRaw_toNat {x y : UInt64} (hx : x.toNat < Goldilocks.fieldSize)
    (hy : y.toNat < Goldilocks.fieldSize) :
    (addRaw x y).toNat = (x.toNat + y.toNat) % Goldilocks.fieldSize := by
  have hx64 := UInt64.toNat_lt_size x
  have hy64 := UInt64.toNat_lt_size y
  simp only [addRaw]
  split_ifs with h <;>
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, negModulus_toNat, modulus_toNat,
      UInt64.size, Goldilocks.fieldSize] at * <;>
    omega

/-- Raw addition of canonical words returns a canonical representative. -/
theorem addRaw_lt {x y : UInt64} (hx : x.toNat < Goldilocks.fieldSize)
    (hy : y.toNat < Goldilocks.fieldSize) :
    (addRaw x y).toNat < Goldilocks.fieldSize := by
  rw [addRaw_toNat hx hy]
  exact Nat.mod_lt _ fieldSize_pos

/-- Raw addition agrees with canonical-field addition on canonical words. -/
theorem addRaw_cast {x y : UInt64} (hx : x.toNat < Goldilocks.fieldSize)
    (hy : y.toNat < Goldilocks.fieldSize) :
    ((addRaw x y).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) + (y.toNat : Goldilocks.Field) := by
  rw [addRaw_toNat hx hy, ZMod.natCast_mod, Nat.cast_add]

/-- Raw negation returns a canonical representative when given one. -/
theorem negRaw_lt (x : UInt64) (hx : x.toNat < Goldilocks.fieldSize) :
    (negRaw x).toNat < Goldilocks.fieldSize := by
  unfold negRaw
  by_cases hzero : x = 0
  · rw [ite_eq_left hzero]
    decide
  · rw [ite_eq_right hzero]
    have hx_ne_nat : x.toNat ≠ 0 := by
      intro hz
      apply hzero
      apply UInt64.toNat_inj.mp
      rw [hz]
      decide
    have hx_pos : 0 < x.toNat := Nat.pos_of_ne_zero hx_ne_nat
    have hx_le_mod : x ≤ modulus := by
      rw [UInt64.le_iff_toNat_le, modulus_toNat]
      exact Nat.le_of_lt hx
    rw [UInt64.toNat_sub_of_le _ _ hx_le_mod, modulus_toNat]
    omega

/-- Raw negation agrees with canonical-field negation. -/
theorem negRaw_cast (x : UInt64) (hx : x.toNat < Goldilocks.fieldSize) :
    ((negRaw x).toNat : Goldilocks.Field) =
      -((x.toNat : Goldilocks.Field)) := by
  unfold negRaw
  by_cases hzero : x = 0
  · rw [ite_eq_left hzero]
    have hxNat : x.toNat = 0 := by
      simpa using congrArg UInt64.toNat hzero
    rw [hxNat]
    simp
  · rw [ite_eq_right hzero]
    have hle : x ≤ modulus := by
      rw [UInt64.le_iff_toNat_le, modulus_toNat]
      exact Nat.le_of_lt hx
    rw [UInt64.toNat_sub_of_le _ _ hle, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt64.le_iff_toNat_le, modulus_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    ring

/-- Raw subtraction returns a canonical representative when given canonical operands. -/
theorem subRaw_lt (x y : UInt64)
    (hx : x.toNat < Goldilocks.fieldSize)
    (hy : y.toNat < Goldilocks.fieldSize) :
    (subRaw x y).toNat < Goldilocks.fieldSize := by
  unfold subRaw
  by_cases hxy : y ≤ x
  · rw [ite_eq_left hxy]
    rw [UInt64.toNat_sub_of_le _ _ hxy]
    have hy_le_x : y.toNat ≤ x.toNat := by
      simpa [UInt64.le_iff_toNat_le] using hxy
    omega
  · rw [ite_eq_right hxy]
    have hx_lt_y : x.toNat < y.toNat := by
      have hnot : ¬y.toNat ≤ x.toNat := by
        intro hle
        apply hxy
        rw [UInt64.le_iff_toNat_le]
        exact hle
      exact Nat.lt_of_not_ge hnot
    have hraw_lt_size : 2 ^ 64 - y.toNat + x.toNat < 2 ^ 64 := by
      have hx_lt_size : x.toNat < 2 ^ 64 := by
        simpa [UInt64.size] using UInt64.toNat_lt_size x
      have hy_lt_size : y.toNat < 2 ^ 64 := by
        simpa [UInt64.size] using UInt64.toNat_lt_size y
      omega
    have hraw_toNat :
        (x - y).toNat = 2 ^ 64 - y.toNat + x.toNat := by
      rw [UInt64.toNat_sub]
      exact Nat.mod_eq_of_lt hraw_lt_size
    have hneg_le_raw_nat : negModulus.toNat ≤ (x - y).toNat := by
      rw [hraw_toNat, negModulus_toNat]
      have hy_lt_field : y.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
        simpa [Goldilocks.fieldSize] using hy
      omega
    have hneg_le_raw : negModulus ≤ x - y := by
      rw [UInt64.le_iff_toNat_le]
      exact hneg_le_raw_nat
    rw [UInt64.toNat_sub_of_le _ _ hneg_le_raw, hraw_toNat, negModulus_toNat]
    change 2 ^ 64 - y.toNat + x.toNat - (2 ^ 32 - 1) <
      2 ^ 64 - 2 ^ 32 + 1
    have hx_lt_field : x.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
      simpa [Goldilocks.fieldSize] using hx
    have hy_lt_field : y.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
      simpa [Goldilocks.fieldSize] using hy
    omega

/-- Raw subtraction agrees with canonical-field subtraction for canonical operands. -/
theorem subRaw_cast (x y : UInt64)
    (_hx : x.toNat < Goldilocks.fieldSize)
    (hy : y.toNat < Goldilocks.fieldSize) :
    ((subRaw x y).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) - (y.toNat : Goldilocks.Field) := by
  unfold subRaw
  by_cases hxy : y ≤ x
  · rw [ite_eq_left hxy]
    rw [UInt64.toNat_sub_of_le _ _ hxy]
    rw [Nat.cast_sub (by
      rw [UInt64.le_iff_toNat_le] at hxy
      exact hxy)]
  · rw [ite_eq_right hxy]
    have hx_lt_y : x.toNat < y.toNat := by
      have hnot : ¬y.toNat ≤ x.toNat := by
        intro hle
        apply hxy
        rw [UInt64.le_iff_toNat_le]
        exact hle
      exact Nat.lt_of_not_ge hnot
    have hraw_lt_size : 2 ^ 64 - y.toNat + x.toNat < 2 ^ 64 := by
      have hx_lt_size : x.toNat < 2 ^ 64 := by
        simpa [UInt64.size] using UInt64.toNat_lt_size x
      have hy_lt_size : y.toNat < 2 ^ 64 := by
        simpa [UInt64.size] using UInt64.toNat_lt_size y
      omega
    have hraw_toNat :
        (x - y).toNat = 2 ^ 64 - y.toNat + x.toNat := by
      rw [UInt64.toNat_sub]
      exact Nat.mod_eq_of_lt hraw_lt_size
    have hneg_le_raw_nat : negModulus.toNat ≤ (x - y).toNat := by
      rw [hraw_toNat, negModulus_toNat]
      have hy_lt_field : y.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
        simpa [Goldilocks.fieldSize] using hy
      omega
    have hneg_le_raw : negModulus ≤ x - y := by
      rw [UInt64.le_iff_toNat_le]
      exact hneg_le_raw_nat
    rw [UInt64.toNat_sub_of_le _ _ hneg_le_raw, hraw_toNat, negModulus_toNat]
    change (((UInt64.size - y.toNat + x.toNat - negModulus.toNat : Nat) :
        Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) - (y.toNat : Goldilocks.Field))
    have hneg_le_concrete : negModulus.toNat ≤ UInt64.size - y.toNat + x.toNat := by
      simpa [UInt64.size, hraw_toNat] using hneg_le_raw_nat
    rw [Nat.cast_sub hneg_le_concrete]
    rw [Nat.cast_add]
    rw [Nat.cast_sub (Nat.le_of_lt (UInt64.toNat_lt_size y))]
    rw [uint64_cast_eq_negModulus]
    ring

/-! ## Lazy exponentiation -/


/-- The lazy ladder computes `acc * x^n`. -/
theorem powLazy_cast (acc x : UInt64) (n : Nat) :
    ((powLazy acc x n).toNat : Goldilocks.Field) =
      (acc.toNat : Goldilocks.Field) * (x.toNat : Goldilocks.Field) ^ n := by
  induction n using Nat.strong_induction_on generalizing acc x with
  | _ n ih =>
    rw [powLazy]
    by_cases hn : n = 0
    · simp [hn]
    · rw [dite_eq_right hn]
      have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      rw [ih (n / 2) hlt, mulLazy_cast, ← pow_two, ← pow_mul]
      have hsplit : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      by_cases hodd : n % 2 = 1
      · rw [ite_eq_left hodd, mulLazy_cast]
        conv_rhs => rw [hsplit, hodd, pow_succ]
        ring
      · rw [ite_eq_right hodd]
        have hev : n % 2 = 0 := by omega
        conv_rhs => rw [hsplit, hev, Nat.add_zero]

/-- Lazy repeated squaring computes `x^(2^n)`. -/
@[simp]
theorem squareNLazy_cast (x : UInt64) (n : Nat) :
    ((squareNLazy x n).toNat : Goldilocks.Field) = (x.toNat : Goldilocks.Field) ^ (2 ^ n) := by
  induction n generalizing x with
  | zero =>
      unfold squareNLazy
      simp
  | succ n ih =>
      unfold squareNLazy
      rw [ih, mulLazy_cast, ← pow_two, ← pow_mul]
      congr 1
      rw [Nat.pow_succ]
      omega

/-- The lazy chain computes the Fermat exponent `p - 2`. -/
theorem invLazy_cast (x : UInt64) :
    ((invLazy x).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) ^ (Goldilocks.fieldSize - 2) := by
  unfold invLazy
  simp only [mulLazy_cast, squareNLazy_cast]
  ring_nf

end Fast
end Goldilocks
