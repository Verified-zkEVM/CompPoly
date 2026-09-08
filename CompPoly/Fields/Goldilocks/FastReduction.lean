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
  · rw [if_pos h]
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
  · rw [if_neg h]
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
    rw [if_neg hnot]
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
    rw [if_pos hlt]
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

/-- Pure Nat carry formula for the high word of a 32-bit-limb 64-by-64 product. -/
theorem wideMul_high_nat
    (p00 p01 p10 p11 : Nat)
    (_hp00 : p00 < 2 ^ 64)
    (_hp01 : p01 < 2 ^ 64)
    (_hp10 : p10 < 2 ^ 64)
    (_hp11 : p11 < 2 ^ 64) :
    let B := 2 ^ 32
    let carry := p00 / B + p01 % B + p10 % B
    p11 + p01 / B + p10 / B + carry / B =
      (p00 + B * (p01 + p10) + B ^ 2 * p11) / B ^ 2 := by
  dsimp
  let carry := p00 / 4294967296 + p01 % 4294967296 + p10 % 4294967296
  let q := p11 + p01 / 4294967296 + p10 / 4294967296 + carry / 4294967296
  have hN :
      p00 + 4294967296 * (p01 + p10) + 18446744073709551616 * p11 =
        p00 % 4294967296 + 4294967296 * (carry % 4294967296) +
          18446744073709551616 * q := by
    have hp00d : p00 % 4294967296 + 4294967296 * (p00 / 4294967296) = p00 :=
      Nat.mod_add_div p00 4294967296
    have hp01d : p01 % 4294967296 + 4294967296 * (p01 / 4294967296) = p01 :=
      Nat.mod_add_div p01 4294967296
    have hp10d : p10 % 4294967296 + 4294967296 * (p10 / 4294967296) = p10 :=
      Nat.mod_add_div p10 4294967296
    have hcd : carry % 4294967296 + 4294967296 * (carry / 4294967296) = carry :=
      Nat.mod_add_div carry 4294967296
    subst q
    subst carry
    omega
  rw [hN]
  change q =
    (p00 % 4294967296 + 4294967296 * (carry % 4294967296) +
        18446744073709551616 * q) /
      18446744073709551616
  rw [Nat.mul_comm 18446744073709551616 q]
  rw [Nat.add_mul_div_right _ _ (show 0 < 18446744073709551616 by decide)]
  rw [Nat.div_eq_of_lt]
  · rw [Nat.zero_add]
  · subst carry
    have hmod0 : p00 % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
    have hmod1 :
        (p00 / 4294967296 + p01 % 4294967296 + p10 % 4294967296) %
            4294967296 <
          4294967296 := Nat.mod_lt _ (by decide)
    omega

/-- High word returned by the 32-bit-limb `UInt64` multiplication algorithm. -/
theorem wideMul_high_toNat
    (x y hi : UInt64)
    (hhi :
      hi =
        let xLo := x &&& negModulus
        let xHi := x >>> 32
        let yLo := y &&& negModulus
        let yHi := y >>> 32
        let p00 := xLo * yLo
        let p01 := xLo * yHi
        let p10 := xHi * yLo
        let p11 := xHi * yHi
        let carry := (p00 >>> 32) + (p01 &&& negModulus) + (p10 &&& negModulus)
        p11 + (p01 >>> 32) + (p10 >>> 32) + (carry >>> 32)) :
    hi.toNat = x.toNat * y.toNat / UInt64.size := by
  let xLo := x &&& negModulus
  let xHi := x >>> 32
  let yLo := y &&& negModulus
  let yHi := y >>> 32
  let p00 := xLo * yLo
  let p01 := xLo * yHi
  let p10 := xHi * yLo
  let p11 := xHi * yHi
  let carry := (p00 >>> 32) + (p01 &&& negModulus) + (p10 &&& negModulus)
  have hxLo_lt : xLo.toNat < 2 ^ 32 := by
    subst xLo
    exact uint64_low32_lt x
  have hxHi_lt : xHi.toNat < 2 ^ 32 := by
    subst xHi
    exact uint64_high32_lt x
  have hyLo_lt : yLo.toNat < 2 ^ 32 := by
    subst yLo
    exact uint64_low32_lt y
  have hyHi_lt : yHi.toNat < 2 ^ 32 := by
    subst yHi
    exact uint64_high32_lt y
  have hp00_nat : p00.toNat = xLo.toNat * yLo.toNat := by
    subst p00
    exact mul32_toNat xLo yLo hxLo_lt hyLo_lt
  have hp01_nat : p01.toNat = xLo.toNat * yHi.toNat := by
    subst p01
    exact mul32_toNat xLo yHi hxLo_lt hyHi_lt
  have hp10_nat : p10.toNat = xHi.toNat * yLo.toNat := by
    subst p10
    exact mul32_toNat xHi yLo hxHi_lt hyLo_lt
  have hp11_nat : p11.toNat = xHi.toNat * yHi.toNat := by
    subst p11
    exact mul32_toNat xHi yHi hxHi_lt hyHi_lt
  have hp00_lt : p00.toNat < 2 ^ 64 := by
    rw [hp00_nat]
    nlinarith [hxLo_lt, hyLo_lt]
  have hp01_lt : p01.toNat < 2 ^ 64 := by
    rw [hp01_nat]
    nlinarith [hxLo_lt, hyHi_lt]
  have hp10_lt : p10.toNat < 2 ^ 64 := by
    rw [hp10_nat]
    nlinarith [hxHi_lt, hyLo_lt]
  have hp11_lt : p11.toNat < 2 ^ 64 := by
    rw [hp11_nat]
    nlinarith [hxHi_lt, hyHi_lt]
  have hcarry_nat :
      carry.toNat = p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 + p10.toNat % 2 ^ 32 := by
    subst carry
    rw [UInt64.toNat_add, UInt64.toNat_add]
    rw [shiftRight32_toNat, and_negModulus_toNat, and_negModulus_toNat]
    have hp00_hi_lt : p00.toNat / 2 ^ 32 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)]
      simpa [pow_add] using hp00_lt
    have hp01_lo_lt : p01.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have hp10_lo_lt : p10.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have hsum01 :
        p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 < 2 ^ 64 := by
      omega
    have hsum012 :
        p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 + p10.toNat % 2 ^ 32 <
          2 ^ 64 := by
      omega
    rw [Nat.mod_eq_of_lt hsum01, Nat.mod_eq_of_lt hsum012]
  have hwide :=
    wideMul_high_nat p00.toNat p01.toNat p10.toNat p11.toNat hp00_lt hp01_lt hp10_lt hp11_lt
  have hwide' :
      p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 +
          (p00.toNat / 2 ^ 32 + p01.toNat % 2 ^ 32 + p10.toNat % 2 ^ 32) / 2 ^ 32 =
        (p00.toNat + 2 ^ 32 * (p01.toNat + p10.toNat) + (2 ^ 32) ^ 2 * p11.toNat) /
          (2 ^ 32) ^ 2 := by
    simpa using hwide
  have hquot_lt :
      p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + carry.toNat / 2 ^ 32 <
        UInt64.size := by
    rw [hcarry_nat]
    rw [hwide']
    have hprod_bound : x.toNat * y.toNat < UInt64.size * UInt64.size := by
      exact
        mul_lt_mul'' (UInt64.toNat_lt_size x) (UInt64.toNat_lt_size y) (Nat.zero_le _)
          (Nat.zero_le _)
    have hsplit :
        p00.toNat + 2 ^ 32 * (p01.toNat + p10.toNat) + (2 ^ 32) ^ 2 * p11.toNat =
          x.toNat * y.toNat := by
      rw [hp00_nat, hp01_nat, hp10_nat, hp11_nat]
      subst p00
      subst p01
      subst p10
      subst p11
      subst xLo
      subst xHi
      subst yLo
      subst yHi
      simpa [pow_add, pow_mul] using (product_split32 x y).symm
    rw [hsplit]
    change x.toNat * y.toNat / UInt64.size < UInt64.size
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < UInt64.size)]
    exact hprod_bound
  have hhi_nat :
      hi.toNat = p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + carry.toNat / 2 ^ 32 := by
    rw [hhi]
    dsimp only
    change (p11 + (p01 >>> 32) + (p10 >>> 32) + (carry >>> 32)).toNat =
      p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + carry.toNat / 2 ^ 32
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add]
    rw [shiftRight32_toNat, shiftRight32_toNat, shiftRight32_toNat]
    have hsum01 : p11.toNat + p01.toNat / 2 ^ 32 < UInt64.size := by
      have hle : p11.toNat + p01.toNat / 2 ^ 32 ≤
          p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + carry.toNat / 2 ^ 32 := by
        omega
      exact lt_of_le_of_lt hle hquot_lt
    have hsum012 :
        p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 < UInt64.size := by
      have hle : p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 ≤
          p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + carry.toNat / 2 ^ 32 := by
        omega
      exact lt_of_le_of_lt hle hquot_lt
    have hquot_lt_pow :
        p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 + carry.toNat / 2 ^ 32 <
          2 ^ 64 := by
      simpa [UInt64.size] using hquot_lt
    have hsum01_pow : p11.toNat + p01.toNat / 2 ^ 32 < 2 ^ 64 := by
      simpa [UInt64.size] using hsum01
    have hsum012_pow :
        p11.toNat + p01.toNat / 2 ^ 32 + p10.toNat / 2 ^ 32 < 2 ^ 64 := by
      simpa [UInt64.size] using hsum012
    rw [Nat.mod_eq_of_lt hsum01_pow, Nat.mod_eq_of_lt hsum012_pow,
      Nat.mod_eq_of_lt hquot_lt_pow]
  rw [hhi_nat]
  rw [hcarry_nat]
  rw [hwide']
  have hsplit :
      p00.toNat + 2 ^ 32 * (p01.toNat + p10.toNat) + (2 ^ 32) ^ 2 * p11.toNat =
        x.toNat * y.toNat := by
    rw [hp00_nat, hp01_nat, hp10_nat, hp11_nat]
    subst p00
    subst p01
    subst p10
    subst p11
    subst xLo
    subst xHi
    subst yLo
    subst yHi
    simpa [pow_add, pow_mul] using (product_split32 x y).symm
  rw [hsplit]
  rfl

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
  · rw [if_pos hx]
    rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
    exact hx
  · rw [if_neg hx]
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
  · rw [if_pos hx]
  · rw [if_neg hx]
    have hmod_le_x : modulus ≤ x := by
      rw [UInt64.le_iff_toNat_le, modulus_toNat]
      rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [UInt64.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt64.le_iff_toNat_le, modulus_toNat] at hmod_le_x
      exact hmod_le_x)]
    simp

/-- The raw 128-bit reducer returns a canonical representative below the modulus. -/
theorem reduceUInt128Raw_lt (lo hi : UInt64) :
    (reduceUInt128Raw lo hi).toNat < Goldilocks.fieldSize := by
  unfold reduceUInt128Raw
  apply reduceUInt64Raw_lt

/-- Semantic correctness of raw 128-bit Goldilocks reduction. -/
theorem reduceUInt128Raw_cast (lo hi : UInt64) :
    ((reduceUInt128Raw lo hi).toNat : Goldilocks.Field) =
      (lo.toNat : Goldilocks.Field) +
        (hi.toNat : Goldilocks.Field) * (UInt64.size : Goldilocks.Field) := by
  let hi_hi := hi >>> 32
  let hi_lo := hi &&& negModulus
  let t0 := if lo < hi_hi then lo - hi_hi - negModulus else lo - hi_hi
  let t1 := hi_lo * negModulus
  let t2 := if t0 + t1 < t0 then t0 + t1 + negModulus else t0 + t1
  change ((reduceUInt64Raw t2).toNat : Goldilocks.Field) =
    (lo.toNat : Goldilocks.Field) +
      (hi.toNat : Goldilocks.Field) * (UInt64.size : Goldilocks.Field)
  have hred := reduceUInt64Raw_cast t2
  change ((reduceUInt64Raw t2).toNat : Goldilocks.Field) =
    (t2.toNat : Goldilocks.Field) at hred
  rw [hred]
  have hhi_hi_lt : hi_hi.toNat < 2 ^ 32 := by
    rw [show hi_hi = hi >>> 32 by rfl, shiftRight32_toNat]
    have hhi := UInt64.toNat_lt_size hi
    change hi.toNat < 2 ^ 64 at hhi
    omega
  have hhi_lo_lt : hi_lo.toNat < 2 ^ 32 := by
    rw [show hi_lo = hi &&& negModulus by rfl, and_negModulus_toNat]
    exact Nat.mod_lt _ (by decide)
  have ht0_cast :
      (t0.toNat : Goldilocks.Field) =
        (lo.toNat : Goldilocks.Field) - (hi_hi.toNat : Goldilocks.Field) := by
    rw [show t0 = if lo < hi_hi then lo - hi_hi - negModulus else lo - hi_hi by rfl]
    exact subBorrow_cast lo hi_hi hhi_hi_lt
  have ht1_cast :
      (t1.toNat : Goldilocks.Field) =
        (hi_lo.toNat : Goldilocks.Field) *
          (negModulus.toNat : Goldilocks.Field) := by
    rw [show t1 = hi_lo * negModulus by rfl]
    rw [mul_negModulus_toNat_of_lt hi_lo hhi_lo_lt]
    rw [Nat.cast_mul]
  have ht2_bound : t0.toNat + t1.toNat < 2 * UInt64.size - negModulus.toNat := by
    have ht0_lt := UInt64.toNat_lt_size t0
    have ht1_le : t1.toNat ≤ UInt64.size - 2 * negModulus.toNat := by
      simpa [t1] using mul_negModulus_toNat_le hi_lo hhi_lo_lt
    have htwice_neg_le_size : 2 * negModulus.toNat ≤ UInt64.size := by
      decide
    omega
  have ht2_cast :
      (t2.toNat : Goldilocks.Field) =
        (t0.toNat : Goldilocks.Field) + (t1.toNat : Goldilocks.Field) := by
    rw [show t2 = if t0 + t1 < t0 then t0 + t1 + negModulus else t0 + t1 by rfl]
    exact addOverflowBounded_cast t0 t1 ht2_bound
  rw [ht2_cast, ht0_cast, ht1_cast]
  rw [hi_split_cast hi]
  ring

/-- Product reduction returns a canonical representative below the modulus. -/
theorem reduceMulRaw_lt (x y : UInt64) :
    (reduceMulRaw x y).toNat < Goldilocks.fieldSize := by
  unfold reduceMulRaw
  apply reduceUInt128Raw_lt

/-- Semantic correctness of native 64-by-64 product reduction. -/
theorem reduceMulRaw_cast (x y : UInt64) :
    ((reduceMulRaw x y).toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) * (y.toNat : Goldilocks.Field) := by
  unfold reduceMulRaw
  rw [reduceUInt128Raw_cast]
  exact
    wideMul_cast x y (wideMul x y).1 (wideMul x y).2
      (by unfold wideMul; rfl)
      (by
        unfold wideMul
        exact wideMul_high_toNat x y _ rfl)

/-- Addition reduction returns a canonical representative. -/
theorem reduceAddWithCarryRaw_lt (lo : UInt64) (carry : Bool)
    (h :
      lo.toNat + (if carry then UInt64.size else 0) < 2 * Goldilocks.fieldSize) :
    (reduceAddWithCarryRaw lo carry).toNat < Goldilocks.fieldSize := by
  unfold reduceAddWithCarryRaw
  cases carry
  · simp only [Bool.false_eq_true, if_false]
    exact reduceUInt64Raw_lt lo
  · simp only [↓reduceIte] at h ⊢
    rw [UInt64.toNat_add]
    have hsum_lt_field : lo.toNat + negModulus.toNat < Goldilocks.fieldSize := by
      rw [negModulus_toNat, Goldilocks.fieldSize]
      rw [Goldilocks.fieldSize, UInt64.size] at h
      omega
    have hsum_lt_size : lo.toNat + negModulus.toNat < UInt64.size :=
      Nat.lt_trans hsum_lt_field fieldSize_lt_uint64Size
    rw [Nat.mod_eq_of_lt hsum_lt_size]
    exact hsum_lt_field

/-- Semantic correctness of addition reduction with carry. -/
theorem reduceAddWithCarryRaw_cast (lo : UInt64) (carry : Bool)
    (h :
      lo.toNat + (if carry then UInt64.size else 0) < 2 * Goldilocks.fieldSize) :
    ((reduceAddWithCarryRaw lo carry).toNat : Goldilocks.Field) =
      (lo.toNat : Goldilocks.Field) +
        (if carry then (UInt64.size : Goldilocks.Field) else 0) := by
  unfold reduceAddWithCarryRaw
  cases carry
  · simp only [Bool.false_eq_true, if_false, add_zero]
    exact reduceUInt64Raw_cast lo
  · simp only [↓reduceIte]
    change lo.toNat + UInt64.size < 2 * Goldilocks.fieldSize at h
    rw [UInt64.toNat_add]
    have hsum_lt_field : lo.toNat + negModulus.toNat < Goldilocks.fieldSize := by
      rw [negModulus_toNat, Goldilocks.fieldSize]
      rw [Goldilocks.fieldSize, UInt64.size] at h
      omega
    have hsum_lt_size : lo.toNat + negModulus.toNat < UInt64.size :=
      Nat.lt_trans hsum_lt_field fieldSize_lt_uint64Size
    rw [Nat.mod_eq_of_lt hsum_lt_size]
    rw [Nat.cast_add]
    rw [uint64_cast_eq_negModulus]

/-- The wrapped word and carry produced by adding two canonical representatives is bounded. -/
theorem addWithCarry_bound (x y : UInt64)
    (hx : x.toNat < Goldilocks.fieldSize)
    (hy : y.toNat < Goldilocks.fieldSize) :
    let lo := x + y
    let carry := decide (lo < x)
    lo.toNat + (if carry then UInt64.size else 0) < 2 * Goldilocks.fieldSize := by
  intro lo carry
  by_cases hcarry : carry
  · simp only [hcarry]
    have hlo_lt_x : lo.toNat < x.toNat := by
      simpa [carry, UInt64.lt_iff_toNat_lt] using hcarry
    have hsum_ge_size : UInt64.size ≤ x.toNat + y.toNat := by
      by_contra hnot
      have hsum_lt_size : x.toNat + y.toNat < UInt64.size :=
        Nat.lt_of_not_ge hnot
      have hlo_eq : lo.toNat = x.toNat + y.toNat := by
        rw [show lo = x + y by rfl, UInt64.toNat_add]
        exact Nat.mod_eq_of_lt hsum_lt_size
      omega
    have hsum_lt_2size : x.toNat + y.toNat < 2 * UInt64.size := by
      nlinarith [UInt64.toNat_lt_size x, UInt64.toNat_lt_size y]
    have hlo_eq : lo.toNat = x.toNat + y.toNat - UInt64.size := by
      rw [show lo = x + y by rfl, UInt64.toNat_add]
      rw [Nat.mod_eq_sub_mod (show x.toNat + y.toNat ≥ UInt64.size by
        exact hsum_ge_size)]
      rw [Nat.mod_eq_of_lt]
      omega
    rw [hlo_eq]
    change x.toNat + y.toNat - UInt64.size + UInt64.size <
      2 * Goldilocks.fieldSize
    have hsum_lt_field : x.toNat + y.toNat < 2 * Goldilocks.fieldSize := by
      omega
    omega
  · simp only [hcarry]
    exact uint64_toNat_lt_two_fieldSize lo

/-- The wrapped word and carry produced by native addition reconstruct the exact Nat sum. -/
theorem addWithCarry_value (x y : UInt64) :
    let lo := x + y
    let carry := decide (lo < x)
    lo.toNat + (if carry then UInt64.size else 0) = x.toNat + y.toNat := by
  intro lo carry
  by_cases hcarry : carry
  · simp only [hcarry]
    have hsum_ge_size : UInt64.size ≤ x.toNat + y.toNat := by
      by_contra hnot
      have hsum_lt_size : x.toNat + y.toNat < UInt64.size :=
        Nat.lt_of_not_ge hnot
      have hlo_eq : lo.toNat = x.toNat + y.toNat := by
        rw [show lo = x + y by rfl, UInt64.toNat_add]
        exact Nat.mod_eq_of_lt hsum_lt_size
      have hlo_lt_x : lo.toNat < x.toNat := by
        simpa [carry, UInt64.lt_iff_toNat_lt] using hcarry
      omega
    have hsum_lt_2size : x.toNat + y.toNat < 2 * UInt64.size := by
      nlinarith [UInt64.toNat_lt_size x, UInt64.toNat_lt_size y]
    have hlo_eq : lo.toNat = x.toNat + y.toNat - UInt64.size := by
      rw [show lo = x + y by rfl, UInt64.toNat_add]
      rw [Nat.mod_eq_sub_mod (show x.toNat + y.toNat ≥ UInt64.size by
        exact hsum_ge_size)]
      rw [Nat.mod_eq_of_lt]
      omega
    rw [hlo_eq]
    change x.toNat + y.toNat - UInt64.size + UInt64.size =
      x.toNat + y.toNat
    omega
  · simp only [hcarry]
    have hnot_lo_lt_x : ¬lo.toNat < x.toNat := by
      intro hlo_lt_x
      apply hcarry
      simpa [carry, UInt64.lt_iff_toNat_lt] using hlo_lt_x
    have hsum_lt_size : x.toNat + y.toNat < UInt64.size := by
      by_contra hnot
      have hsum_ge_size : UInt64.size ≤ x.toNat + y.toNat :=
        Nat.le_of_not_gt hnot
      have hsum_lt_2size : x.toNat + y.toNat < 2 * UInt64.size := by
        nlinarith [UInt64.toNat_lt_size x, UInt64.toNat_lt_size y]
      have hlo_eq : lo.toNat = x.toNat + y.toNat - UInt64.size := by
        rw [show lo = x + y by rfl, UInt64.toNat_add]
        rw [Nat.mod_eq_sub_mod (show x.toNat + y.toNat ≥ UInt64.size by
          exact hsum_ge_size)]
        rw [Nat.mod_eq_of_lt]
        omega
      have hy_lt_size : y.toNat < UInt64.size := UInt64.toNat_lt_size y
      omega
    rw [show lo = x + y by rfl, UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hsum_lt_size

/-- Raw negation returns a canonical representative when given one. -/
theorem negRaw_lt (x : UInt64) (hx : x.toNat < Goldilocks.fieldSize) :
    (negRaw x).toNat < Goldilocks.fieldSize := by
  unfold negRaw
  by_cases hzero : x = 0
  · rw [if_pos hzero]
    decide
  · rw [if_neg hzero]
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
  · rw [if_pos hzero]
    have hxNat : x.toNat = 0 := by
      simpa using congrArg UInt64.toNat hzero
    rw [hxNat]
    simp
  · rw [if_neg hzero]
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
  · rw [if_pos hxy]
    rw [UInt64.toNat_sub_of_le _ _ hxy]
    have hy_le_x : y.toNat ≤ x.toNat := by
      simpa [UInt64.le_iff_toNat_le] using hxy
    omega
  · rw [if_neg hxy]
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
  · rw [if_pos hxy]
    rw [UInt64.toNat_sub_of_le _ _ hxy]
    rw [Nat.cast_sub (by
      rw [UInt64.le_iff_toNat_le] at hxy
      exact hxy)]
  · rw [if_neg hxy]
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

end Fast
end Goldilocks
