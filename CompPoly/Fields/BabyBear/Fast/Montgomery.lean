/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Prelude
import CompPoly.Fields.Montgomery.Native32

/-!
# Fast BabyBear Field — Montgomery Reduction

Montgomery-form constants (`montgomeryNegInv`, `rModModulus`, `r2ModModulus`) and the
native-word Montgomery reduction used by the fast BabyBear field. The radix-generic
number theory lives in `CompPoly.Fields.Montgomery.Basic` and the `R = 2^32` word bridge
in `CompPoly.Fields.Montgomery.Native32`; field basics live in
`CompPoly.Fields.BabyBear.Fast.Prelude`; conversions and field operations build on this
module.
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
    (Montgomery.Native32.u_lt_two_mul montgomeryNegInv modulus64 BabyBear.fieldSize
      modulus64_toNat fieldSize_pos two_fieldSize_mul_uint32Size_lt_two64 x h)

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
  have hred := reduceUInt32Lt2Modulus_cast u
    (Montgomery.Native32.u_lt_two_mul montgomeryNegInv modulus64 BabyBear.fieldSize
      modulus64_toNat fieldSize_pos two_fieldSize_mul_uint32Size_lt_two64 x h)
  change ((reduceUInt32Lt2ModulusRaw u).toNat : BabyBear.Field) =
    (u.toNat : BabyBear.Field) at hred
  rw [hred]
  change (u.toNat : BabyBear.Field) =
    (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  rw [show u.toNat =
      (x.toNat + ((x.toNat % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) *
        BabyBear.fieldSize) / UInt32.size by
    exact Montgomery.Native32.u_eq_nat montgomeryNegInv modulus64 BabyBear.fieldSize
      modulus64_toNat fieldSize_pos two_fieldSize_mul_uint32Size_lt_two64 x h]
  exact Montgomery.quotient_cast UInt32.size BabyBear.fieldSize montgomeryNegInv.toNat
    (by decide) (by decide) uint32Size_ne_zero_in_field x.toNat

/-- Montgomery reduction of a 64-bit word. Hot bounded callers use `montgomeryReduceBounded`. -/
@[inline]
def montgomeryReduce (x : UInt64) : Field :=
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  reduceUInt32 u

end Fast
end BabyBear
