/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.Goldilocks.FastDefs
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Fast Goldilocks Field

Verified `UInt64`-backed implementation of Goldilocks arithmetic, `p = 2^64 - 2^32 + 1`.
The carrier is a subtype of `UInt64` holding canonical representatives; the runtime
definitions live in the zero-import `FastDefs`, and this module proves them correct
against the canonical `ZMod` model in `CompPoly.Fields.Goldilocks.Basic`, then transfers
the field instances across `toField`.

Reduction rests on `2^64 ≡ 2^32 - 1 (mod p)`, so a 128-bit product folds back into one
word with shifts, one multiply by `2^32 - 1`, and carry corrections.
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

/-! ## Carrier and arithmetic -/


/-- The fast native-word Goldilocks field carrier, stored as a canonical residue. -/
abbrev Field : Type := { x : UInt64 // x.toNat < Goldilocks.fieldSize }

/-- Fast representatives have decidable equality through their `UInt64` value. -/
instance : DecidableEq Field := inferInstance

/-- The raw canonical word backing a fast Goldilocks element. -/
@[inline]
def raw (x : Field) : UInt64 := x.val

/-- Reduce a native `UInt64` modulo Goldilocks. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  ⟨reduceUInt64Raw x, reduceUInt64Raw_lt x⟩

/-- One-word reduction preserves the represented canonical field element. -/
@[simp]
theorem reduceUInt64_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) := by
  exact reduceUInt64Raw_cast x

/-- The zero fast Goldilocks element. -/
@[inline]
def zero : Field := ⟨0, by decide⟩

/-- The one fast Goldilocks element. -/
@[inline]
def one : Field := ⟨1, by decide⟩

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < Goldilocks.fieldSize) : Field :=
  ⟨UInt64.ofNat n, by
    have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
    rw [UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    · exact h
    · simpa [UInt64.size] using hn⟩

/-- Convert a natural number into fast canonical representation. -/
@[inline]
def ofNat (n : Nat) : Field :=
  ofCanonicalNat (n % Goldilocks.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 64-bit word into fast canonical representation. -/
@[inline]
def ofUInt64 (x : UInt64) : Field :=
  reduceUInt64 x

/-- Convert from the canonical `ZMod` Goldilocks field into fast canonical form. -/
@[inline]
def ofField (x : Goldilocks.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast canonical representation. -/
@[inline]
def ofInt (z : Int) : Field :=
  ofField (z : Goldilocks.Field)

/-- Convert a fast Goldilocks element to its canonical natural representative. -/
@[inline]
def toNat (x : Field) : Nat :=
  x.val.toNat

/-- Convert a fast Goldilocks element to the canonical `ZMod` Goldilocks field. -/
@[inline]
def toField (x : Field) : Goldilocks.Field :=
  (toNat x : Goldilocks.Field)

/-- Fast modular addition in canonical form. -/
@[inline]
def add (x y : Field) : Field :=
  let lo := x.val + y.val
  let carry := decide (lo < x.val)
  ⟨reduceAddWithCarryRaw lo carry,
    reduceAddWithCarryRaw_lt lo carry
      (addWithCarry_bound x.val y.val x.property y.property)⟩

/-- Fast modular negation in canonical form. -/
@[inline]
def neg (x : Field) : Field :=
  ⟨negRaw x.val, negRaw_lt x.val x.property⟩

/-- Fast modular subtraction in canonical form. -/
@[inline]
def sub (x y : Field) : Field :=
  ⟨subRaw x.val y.val, subRaw_lt x.val y.val x.property y.property⟩

/-- Fast modular multiplication in canonical form. -/
@[inline]
def mul (x y : Field) : Field :=
  ⟨reduceMulRaw x.val y.val, reduceMulRaw_lt x.val y.val⟩

/-- Fast squaring. -/
@[inline]
def square (x : Field) : Field :=
  mul x x

/-- Repeated squaring: `squareN x n` computes `x^(2^n)`. -/
@[inline]
def squareN (x : Field) : Nat → Field
  | 0 => x
  | n + 1 => square (squareN x n)

/-- Exponentiation over the fast representation using binary exponentiation. -/
@[inline]
def pow (x : Field) (n : Nat) : Field :=
  @npowBinRec Field ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the Goldilocks prime field. -/
@[inline]
def invExponent : Nat := Goldilocks.fieldSize - 2

/-- Fast modular inversion using an addition chain for `p - 2`.

For Goldilocks, `p - 2 = 0xFFFFFFFEFFFFFFFF`. The chain builds
`x^(2^31 - 1)`, derives `x^(2^32 - 2)` and `x^(2^32 - 1)`, then combines them as

`(2^32 - 2) * 2^32 + (2^32 - 1) = p - 2`.
-/
@[noinline]
def inv (x : Field) : Field :=
  let t2 := mul (square x) x
  let t4 := mul (squareN t2 2) t2
  let t8 := mul (squareN t4 4) t4
  let t16 := mul (squareN t8 8) t8
  let t31 :=
    mul (squareN t16 15)
      (mul (squareN t8 7)
        (mul (squareN t4 3)
          (mul (square t2) x)))
  let t32m2 := square t31
  let t32m1 := mul t32m2 x
  mul (squareN t32m2 32) t32m1

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field :=
  mul x (inv y)

/-- Use fast zero for standard `0` notation. -/
instance instZeroField : Zero Field where
  zero := zero

/-- Use fast one for standard `1` notation. -/
instance instOneField : One Field where
  one := one

/-- Use fast addition for standard `+` notation. -/
instance instAddField : Add Field where
  add := add

/-- Use fast negation for standard unary `-` notation. -/
instance instNegField : Neg Field where
  neg := neg

/-- Use fast subtraction for standard `-` notation. -/
instance instSubField : Sub Field where
  sub := sub

/-- Use fast multiplication for standard `*` notation. -/
instance instMulField : Mul Field where
  mul := mul

/-- Use fast inversion for standard inverse notation. -/
instance instInvField : Inv Field where
  inv := inv

/-- Use fast division for standard `/` notation. -/
instance instDivField : Div Field where
  div := div

/-- Use `ofNat` for natural-number casts into fast Goldilocks. -/
instance instNatCastField : NatCast Field where
  natCast := ofNat

/-- Interpret integer casts through the canonical Goldilocks field. -/
instance instIntCastField : IntCast Field where
  intCast := ofInt

/-- Natural scalar multiplication is multiplication by the corresponding fast natural cast. -/
instance instNatSMulField : SMul Nat Field where
  smul n x := (n : Field) * x

/-- Integer scalar multiplication is multiplication by the corresponding fast integer cast. -/
instance instIntSMulField : SMul Int Field where
  smul n x := (n : Field) * x

/-- Use fast binary exponentiation for natural powers. -/
instance instPowFieldNat : Pow Field Nat where
  pow := pow

/-- Use fast natural powers and inversion for integer powers. -/
instance instPowFieldInt : Pow Field Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

/-- Interpret nonnegative rational casts through the canonical Goldilocks field. -/
instance instNNRatCastField : NNRatCast Field where
  nnratCast q := ofField (q : Goldilocks.Field)

/-- Interpret rational casts through the canonical Goldilocks field. -/
instance instRatCastField : RatCast Field where
  ratCast q := ofField (q : Goldilocks.Field)

/-- Nonnegative rational scalar multiplication is transported through the canonical field. -/
instance instNNRatSMulField : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

/-- Rational scalar multiplication is transported through the canonical field. -/
instance instRatSMulField : SMul ℚ Field where
  smul q x := ofField (q • toField x)

/-! ## Correctness against the canonical model -/


/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
private theorem toField_ofCanonicalNat (n : Nat) (h : n < Goldilocks.fieldSize) :
    toField (ofCanonicalNat n h) = (n : Goldilocks.Field) := by
  unfold toField toNat ofCanonicalNat
  have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
  rw [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by simpa [UInt64.size] using hn)]

/-- Converting a canonical natural representative to fast form and reading it back is
the identity. -/
@[simp]
private theorem toNat_ofCanonicalNat (n : Nat) (h : n < Goldilocks.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  unfold toNat ofCanonicalNat
  have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using hn)

/-- Converting a natural number to fast form agrees with the same natural cast in the
canonical field. -/
@[simp]
theorem toField_ofNat (n : Nat) :
    toField (ofNat n) = (n : Goldilocks.Field) := by
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [← ZMod.natCast_zmod_val (n : Goldilocks.Field)]
  rw [ZMod.val_natCast]

/-- Converting a `UInt64` to fast form agrees with casting its natural value into the
canonical field. -/
@[simp]
theorem toField_ofUInt64 (x : UInt64) :
    toField (ofUInt64 x) = (x.toNat : Goldilocks.Field) := by
  unfold toField toNat ofUInt64
  exact reduceUInt64_cast x

/-- Converting an integer to fast form agrees with casting it into the canonical field. -/
@[simp]
theorem toField_ofInt (z : Int) :
    toField (ofInt z) = (z : Goldilocks.Field) := by
  unfold ofInt ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val (z : Goldilocks.Field)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : Goldilocks.Field) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  change toNat (ofField (toField x)) = toNat x
  unfold ofField toField
  rw [toNat_ofCanonicalNat]
  exact ZMod.val_natCast_of_lt x.property

/-- The canonical-field interpretation distinguishes fast Goldilocks values. -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- Fermat-style inversion in the canonical Goldilocks field. -/
private lemma canonical_inv_eq_pow (a : Goldilocks.Field) (ha : a ≠ 0) :
    a⁻¹ = a ^ (Goldilocks.fieldSize - 2) := by
  have hcard : Fintype.card Goldilocks.Field = Goldilocks.fieldSize :=
    ZMod.card Goldilocks.fieldSize
  have h1 : a ^ (Goldilocks.fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h
    exact h
  have hmul : a * a ^ (Goldilocks.fieldSize - 2) = 1 := by
    rw [← pow_succ']
    show a ^ (Goldilocks.fieldSize - 2 + 1) = 1
    have : Goldilocks.fieldSize - 2 + 1 = Goldilocks.fieldSize - 1 := by
      unfold Goldilocks.fieldSize
      omega
    rw [this]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Fast zero maps to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by
  decide

/-- Fast one maps to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by
  decide

/-- Fast addition agrees with canonical-field addition. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y := by
  change
    (((add x y).val.toNat : Goldilocks.Field) =
      (x.val.toNat : Goldilocks.Field) + (y.val.toNat : Goldilocks.Field))
  unfold add
  rw [reduceAddWithCarryRaw_cast _ _
    (addWithCarry_bound x.val y.val x.property y.property)]
  let lo := x.val + y.val
  let carry := decide (lo < x.val)
  have hvalue := addWithCarry_value x.val y.val
  change lo.toNat + (if carry then UInt64.size else 0) = x.val.toNat + y.val.toNat at hvalue
  change
    ((lo.toNat : Goldilocks.Field) +
        (if carry then (UInt64.size : Goldilocks.Field) else 0) =
      (x.val.toNat : Goldilocks.Field) + (y.val.toNat : Goldilocks.Field))
  by_cases hcarry : carry = true
  · simp only [hcarry, if_true] at hvalue ⊢
    rw [← Nat.cast_add, hvalue, Nat.cast_add]
  · simp only [hcarry, Bool.false_eq_true, if_false, add_zero] at hvalue ⊢
    rw [hvalue, Nat.cast_add]

/-- Fast negation agrees with canonical-field negation. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x := by
  change toField (neg x) = -(toField x)
  unfold neg toField toNat
  exact negRaw_cast x.val x.property

/-- Fast subtraction agrees with canonical-field subtraction. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y := by
  change toField (sub x y) = toField x - toField y
  unfold sub toField toNat
  exact subRaw_cast x.val y.val x.property y.property

/-- Fast multiplication agrees with canonical-field multiplication. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y := by
  change toField (mul x y) = toField x * toField y
  unfold mul toField toNat
  exact reduceMulRaw_cast x.val y.val

/-- The named fast multiplication function agrees with canonical-field multiplication. -/
@[simp]
theorem toField_mul_def (x y : Field) : toField (mul x y) = toField x * toField y :=
  toField_mul x y

/-- Fast squaring agrees with multiplying the canonical field value by itself. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

/-- Repeated fast squaring agrees with raising to `2^n` in the canonical field. -/
@[simp]
theorem toField_squareN (x : Field) (n : Nat) :
    toField (squareN x n) = toField x ^ (2 ^ n) := by
  induction n generalizing x with
  | zero =>
      unfold squareN
      simp
  | succ n ih =>
      unfold squareN
      rw [toField_square, ih]
      rw [← pow_add]
      congr 1
      rw [Nat.pow_succ]
      omega

/-- Fast multiplication is associative, proved by transporting to the canonical field. -/
private theorem mul_assoc_field (x y z : Field) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

/-- Binary exponentiation satisfies the expected successor equation. -/
private theorem pow_succ (x : Field) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  let _ : Semigroup Field := {
    mul := (· * ·)
    mul_assoc := mul_assoc_field
  }
  exact npowBinRec_succ n x

/-- Fast natural-power computation agrees with powers in the canonical field. -/
@[simp]
theorem toField_pow (x : Field) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero]
      rw [toField_one]
      simp
  | succ n ih =>
      rw [pow_succ, toField_mul, ih, _root_.pow_succ]

/-- The optimized inversion chain computes the Fermat inverse exponent. -/
private theorem toField_inv_chain (x : Field) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv
  simp only [toField_mul_def, toField_square, toField_squareN]
  ring_nf
  simp [invExponent, Goldilocks.fieldSize]

/-- Fast inversion agrees with canonical inversion before notation is unfolded. -/
private theorem toField_inv_raw (x : Field) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_chain]
  by_cases hx : toField x = 0
  · rw [hx]
    simp [invExponent, Goldilocks.fieldSize]
  · simpa [invExponent] using (canonical_inv_eq_pow (toField x) hx).symm

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

/-- Division is multiplication by inverse at the level of canonical interpretation. -/
private theorem toField_div_mul_inv (x y : Field) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  change toField (x * inv y) = toField x * toField (inv y)
  exact toField_mul x (inv y)

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  rw [toField_div_mul_inv, toField_inv_raw y]
  rfl

/-- Natural casts in the fast field agree with natural casts in the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : Field) = (n : Goldilocks.Field) := by
  change toField (ofNat n) = (n : Goldilocks.Field)
  rw [toField_ofNat]

/-- Integer casts in the fast field agree with integer casts in the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : Field) = (n : Goldilocks.Field) := by
  change toField (ofInt n) = (n : Goldilocks.Field)
  rw [toField_ofInt]

/-- Fast natural scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

/-- Fast integer scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

/-- Standard fast natural powers agree with powers in the canonical field. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Standard fast integer powers agree with integer powers in the canonical field. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := toField_inv_raw x
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

/-- Nonnegative rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : Goldilocks.Field) := by
  change toField (ofField (q : Goldilocks.Field)) = (q : Goldilocks.Field)
  rw [toField_ofField]

/-- Rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : Goldilocks.Field) := by
  change toField (ofField (q : Goldilocks.Field)) = (q : Goldilocks.Field)
  rw [toField_ofField]

/-- Fast nonnegative rational scalar multiplication agrees with canonical-field scalar
multiplication. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Fast rational scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ## Canonical bridge and field instances -/


/-- Ring equivalence between the fast representation and canonical Goldilocks. -/
def ringEquiv : Field ≃+* Goldilocks.Field where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x := rfl

/-- Applying the inverse `ringEquiv` converts a canonical value into fast form. -/
@[simp]
theorem ringEquiv_symm_apply (x : Goldilocks.Field) : ringEquiv.symm x = ofField x := rfl

/-- Field instance transferred from canonical Goldilocks through `toField`. -/
instance (priority := low) instField : _root_.Field Field :=
  toField_injective.field toField
    toField_zero
    toField_one
    toField_add
    toField_mul
    toField_neg
    toField_sub
    toField_inv
    toField_div
    toField_nsmul
    toField_zsmul
    toField_nnqsmul
    toField_qsmul
    toField_npow
    toField_zpow
    toField_natCast
    toField_intCast
    toField_nnratCast
    toField_ratCast

/-- Commutative-ring instance inherited from the transferred field structure. -/
instance (priority := low) instCommRing : CommRing Field := by
  infer_instance

/-- Fast Goldilocks is a non-binary field. -/
instance (priority := low) instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    intro h
    have hv := congrArg Subtype.val h
    exact (by decide : (2 : UInt64) ≠ 0) hv

end Fast
end Goldilocks
