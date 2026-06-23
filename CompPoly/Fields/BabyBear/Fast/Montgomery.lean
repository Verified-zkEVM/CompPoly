/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Prelude
import Mathlib.Data.Nat.ModEq

/-!
# Fast BabyBear Field — Montgomery Reduction

Montgomery-form constants (`montgomeryNegInv`, `rModModulus`, `r2ModModulus`) and the
native-word Montgomery reduction used by the fast BabyBear field. Field basics live
in `CompPoly.Fields.BabyBear.Fast.Prelude`; conversions and field operations build
on this module.
-/

namespace BabyBear
namespace Fast

/-- `2^32 mod BabyBear.fieldSize`. This is the Montgomery representation of one. -/
def rModModulus : UInt32 := 0x0FFFFFFE

/-- `(2^32)^2 mod BabyBear.fieldSize`, used to enter Montgomery representation. -/
def r2ModModulus : UInt32 := 0x45DDDDE3

/-- `-BabyBear.fieldSize⁻¹ mod 2^32`, used by Montgomery reduction. -/
def montgomeryNegInv : UInt32 := 0x77FFFFFF

theorem r2ModModulus_lt_fieldSize : r2ModModulus.toNat < BabyBear.fieldSize := by
  decide

theorem rModModulus_lt_fieldSize : rModModulus.toNat < BabyBear.fieldSize := by
  decide

theorem rModModulus_cast :
    (rModModulus.toNat : BabyBear.Field) = (UInt32.size : BabyBear.Field) := by
  decide

theorem r2ModModulus_cast :
    (r2ModModulus.toNat : BabyBear.Field) = (UInt32.size : BabyBear.Field) ^ 2 := by
  decide

theorem montgomery_sum_dvd (x : Nat) :
    UInt32.size ∣
      x + ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * BabyBear.fieldSize := by
  rw [← Nat.modEq_zero_iff_dvd]
  have hx : x ≡ x % UInt32.size [MOD UInt32.size] :=
    (Nat.mod_modEq x UInt32.size).symm
  have hm :
      ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * BabyBear.fieldSize ≡
        (x % UInt32.size) * (UInt32.size - 1) [MOD UInt32.size] := by
    have hmi :
        (x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size ≡
          x % UInt32.size * montgomeryNegInv.toNat [MOD UInt32.size] :=
      Nat.mod_modEq _ _
    have hp : montgomeryNegInv.toNat * BabyBear.fieldSize ≡ UInt32.size - 1
        [MOD UInt32.size] := by
      decide
    calc
      ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * BabyBear.fieldSize
          ≡ (x % UInt32.size * montgomeryNegInv.toNat) * BabyBear.fieldSize
              [MOD UInt32.size] := hmi.mul_right _
      _ = x % UInt32.size * (montgomeryNegInv.toNat * BabyBear.fieldSize) := by ring
      _ ≡ x % UInt32.size * (UInt32.size - 1) [MOD UInt32.size] := hp.mul_left _
  calc
    x + ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * BabyBear.fieldSize
        ≡ x % UInt32.size + x % UInt32.size * (UInt32.size - 1) [MOD UInt32.size] :=
          hx.add hm
    _ = x % UInt32.size * UInt32.size := by
      rw [add_comm, ← Nat.mul_succ]
      have hsucc : (UInt32.size - 1).succ = UInt32.size := by decide
      rw [hsucc]
    _ ≡ 0 [MOD UInt32.size] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact ⟨x % UInt32.size, by rw [mul_comm]⟩

/-- Nat-level Montgomery reduction used to specify and prove the native-word reducer. -/
def montgomeryReduceNat (x : Nat) : Nat :=
  let m := (x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size
  let u := (x + m * BabyBear.fieldSize) / UInt32.size
  if u < BabyBear.fieldSize then u else u - BabyBear.fieldSize

theorem montgomeryReduceNat_cast (x : Nat) :
    (montgomeryReduceNat x : BabyBear.Field) =
      (x : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
  let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  let u := (x + m * BabyBear.fieldSize) / UInt32.size
  have hdiv : UInt32.size ∣ x + m * BabyBear.fieldSize := by
    simpa [m] using montgomery_sum_dvd x
  have hu_mul : u * UInt32.size = x + m * BabyBear.fieldSize := by
    exact Nat.div_mul_cancel hdiv
  have hcast_mul : (u : BabyBear.Field) * (UInt32.size : BabyBear.Field) =
      (x : BabyBear.Field) := by
    rw [← Nat.cast_mul, hu_mul, Nat.cast_add, Nat.cast_mul]
    simp
  have hR := uint32Size_ne_zero_in_field
  by_cases hu : u < BabyBear.fieldSize
  · have hmain :
        (u : BabyBear.Field) = (x : BabyBear.Field) *
          (UInt32.size : BabyBear.Field)⁻¹ := by
      calc
        (u : BabyBear.Field) =
            (u : BabyBear.Field) * (UInt32.size : BabyBear.Field) *
              (UInt32.size : BabyBear.Field)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hR, mul_one]
        _ = (x : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
          rw [hcast_mul]
    dsimp only [montgomeryReduceNat]
    rw [if_pos hu]
    exact hmain
  · have hfield :
        ((u - BabyBear.fieldSize : Nat) : BabyBear.Field) = (u : BabyBear.Field) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    have hmain :
        ((u - BabyBear.fieldSize : Nat) : BabyBear.Field) =
          (x : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
      rw [hfield]
      calc
        (u : BabyBear.Field) =
            (u : BabyBear.Field) * (UInt32.size : BabyBear.Field) *
              (UInt32.size : BabyBear.Field)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hR, mul_one]
        _ = (x : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
          rw [hcast_mul]
    dsimp only [montgomeryReduceNat]
    rw [if_neg hu]
    exact hmain

theorem montgomeryQuotient_cast (x : Nat) :
    (let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
     let u := (x + m * BabyBear.fieldSize) / UInt32.size
     (u : BabyBear.Field)) =
      (x : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
  let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  let u := (x + m * BabyBear.fieldSize) / UInt32.size
  have hmr := montgomeryReduceNat_cast x
  unfold montgomeryReduceNat at hmr
  change (u : BabyBear.Field) =
      (x : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  by_cases hu : u < BabyBear.fieldSize
  · simpa only [m, u, hu, if_true] using hmr
  · have hfield : ((u - BabyBear.fieldSize : Nat) : BabyBear.Field) =
        (u : BabyBear.Field) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    rw [← hfield]
    simpa only [m, u, hu, if_false] using hmr

theorem montgomery_u_eq_nat (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    (let m : UInt32 := x.toUInt32 * montgomeryNegInv
     (((x + m.toUInt64 * modulus64) >>> 32).toUInt32).toNat) =
      (x.toNat + ((x.toNat % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) *
        BabyBear.fieldSize) / UInt32.size := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt64.toNat_ofNat,
    modulus64_toNat, Nat.shiftRight_eq_div_pow]
  norm_num [BabyBear.fieldSize, UInt32.size] at h ⊢
  let mNat := x.toNat * montgomeryNegInv.toNat % 4294967296
  have hm_lt : mNat < 4294967296 := Nat.mod_lt _ (by decide)
  have hsum_lt : x.toNat + mNat * 2013265921 < 18446744073709551616 := by
    have hprod_lt : mNat * 2013265921 < 2013265921 * 4294967296 := by nlinarith
    nlinarith
  change ((x.toNat + mNat * 2013265921) % 18446744073709551616 / 4294967296) %
      4294967296 = (x.toNat + mNat * 2013265921) / 4294967296
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul]
  · exact hsum_lt
  · decide

theorem montgomery_u_lt_two_fieldSize (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    (let m : UInt32 := x.toUInt32 * montgomeryNegInv
     (((x + m.toUInt64 * modulus64) >>> 32).toUInt32).toNat) <
      2 * BabyBear.fieldSize := by
  rw [montgomery_u_eq_nat x h]
  let mNat := x.toNat % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  have hm_lt : mNat < UInt32.size := Nat.mod_lt _ (by decide)
  rw [Nat.div_lt_iff_lt_mul]
  · have hprod_lt : mNat * BabyBear.fieldSize < UInt32.size * BabyBear.fieldSize := by
      exact Nat.mul_lt_mul_of_pos_right hm_lt fieldSize_pos
    have hprod_lt' :
        mNat * BabyBear.fieldSize < BabyBear.fieldSize * UInt32.size := by
      simpa [Nat.mul_comm] using hprod_lt
    change x.toNat + mNat * BabyBear.fieldSize < 2 * BabyBear.fieldSize * UInt32.size
    nlinarith
  · decide

/-- Reduce a native word known to be below twice the BabyBear prime. -/
@[inline]
def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  if x < modulus then x else x - modulus

theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * BabyBear.fieldSize) :
    (reduceUInt32Lt2ModulusRaw x).toNat < BabyBear.fieldSize := by
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < modulus
  · rw [if_pos hx]
    rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
    exact hx
  · rw [if_neg hx]
    have hmod_le_x : modulus ≤ x := by
      rw [UInt32.le_iff_toNat_le, modulus_toNat]
      rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
    omega

/-- Reduce a native word known to be below twice the BabyBear prime. -/
@[inline]
def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * BabyBear.fieldSize) :
    Field :=
  ⟨reduceUInt32Lt2ModulusRaw x, reduceUInt32Lt2ModulusRaw_lt x h⟩

theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * BabyBear.fieldSize) :
    ((reduceUInt32Lt2Modulus x h).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) := by
  change ((reduceUInt32Lt2ModulusRaw x).toNat : BabyBear.Field) =
    (x.toNat : BabyBear.Field)
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < modulus
  · rw [if_pos hx]
  · have hmod_le_x : modulus ≤ x := by
      rw [UInt32.le_iff_toNat_le, modulus_toNat]
      rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [if_neg hx]
    rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, modulus_toNat] at hmod_le_x
      exact hmod_le_x)]
    simp

/-- Reduce a native word below `2^32` modulo the BabyBear prime. -/
@[inline]
def reduceUInt32 (x : UInt32) : Field :=
  if hx : x < modulus then
    ⟨x, by
      rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
      exact hx⟩
  else
    let y := x - modulus
    if hy : y < modulus then
      ⟨y, by
        rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hy
        exact hy⟩
    else
      ⟨y - modulus, by
        have hmod_le_x : modulus ≤ x := by
          rw [UInt32.le_iff_toNat_le, modulus_toNat]
          rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
          exact Nat.le_of_not_gt hx
        have hy_eq : y.toNat = x.toNat - BabyBear.fieldSize := by
          change (x - modulus).toNat = x.toNat - BabyBear.fieldSize
          rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
        have hmod_le_y : modulus ≤ y := by
          rw [UInt32.le_iff_toNat_le, modulus_toNat]
          rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hy
          exact Nat.le_of_not_gt hy
        rw [UInt32.toNat_sub_of_le _ _ hmod_le_y, modulus_toNat, hy_eq]
        have hx_lt := UInt32.toNat_lt_size x
        have hthree := uint32Size_lt_three_fieldSize
        omega⟩

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBoundedRaw (x : UInt64) : UInt32 :=
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  reduceUInt32Lt2ModulusRaw u

theorem montgomeryReduceBoundedRaw_lt (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    (montgomeryReduceBoundedRaw x).toNat < BabyBear.fieldSize := by
  unfold montgomeryReduceBoundedRaw
  exact reduceUInt32Lt2ModulusRaw_lt _
    (montgomery_u_lt_two_fieldSize x h)

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBounded (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) : Field :=
  ⟨montgomeryReduceBoundedRaw x, montgomeryReduceBoundedRaw_lt x h⟩

theorem montgomeryReduceBounded_cast (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    ((montgomeryReduceBounded x h).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
  change ((montgomeryReduceBoundedRaw x).toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  unfold montgomeryReduceBoundedRaw
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  change ((reduceUInt32Lt2ModulusRaw u).toNat : BabyBear.Field) =
    (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  have hred := reduceUInt32Lt2Modulus_cast u (montgomery_u_lt_two_fieldSize x h)
  change ((reduceUInt32Lt2ModulusRaw u).toNat : BabyBear.Field) =
    (u.toNat : BabyBear.Field) at hred
  rw [hred]
  change (u.toNat : BabyBear.Field) =
    (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  rw [show u.toNat =
      (x.toNat + ((x.toNat % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) *
        BabyBear.fieldSize) / UInt32.size by
    exact montgomery_u_eq_nat x h]
  exact montgomeryQuotient_cast x.toNat

/-- Montgomery reduction of a 64-bit word. Hot bounded callers use `montgomeryReduceBounded`. -/
@[inline]
def montgomeryReduce (x : UInt64) : Field :=
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  reduceUInt32 u

end Fast
end BabyBear
