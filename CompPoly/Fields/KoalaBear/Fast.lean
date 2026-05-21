/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.KoalaBear.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Data.Nat.ModEq

/-!
# Fast KoalaBear Field Operations

This module provides a native-word implementation of KoalaBear arithmetic as a sidecar
to the canonical `KoalaBear.Field := ZMod KoalaBear.fieldSize` model.

Elements are stored as Montgomery `UInt32` residues below `KoalaBear.fieldSize`,
representing `x * 2^32` modulo the KoalaBear prime. Addition, subtraction, and
negation operate directly on Montgomery words; multiplication uses Montgomery
reduction on a native `UInt64` product.
-/

namespace KoalaBear
namespace Fast

/-- KoalaBear modulus as a native word. -/
def modulus : UInt32 := 0x7F000001

/-- KoalaBear modulus as a 64-bit word for modular reduction. -/
def modulus64 : UInt64 := 0x7F000001

/-- `2^32 mod KoalaBear.fieldSize`. This is the Montgomery representation of one. -/
def rModModulus : UInt32 := 0x01FFFFFE

/-- `(2^32)^2 mod KoalaBear.fieldSize`, used to enter Montgomery representation. -/
def r2ModModulus : UInt32 := 0x17F7EFE4

/-- `-KoalaBear.fieldSize⁻¹ mod 2^32`, used by Montgomery reduction. -/
def montgomeryNegInv : UInt32 := 0x7EFFFFFF

/-- A native-word KoalaBear element stored as a Montgomery residue. -/
abbrev Element : Type := { x : UInt32 // x.toNat < KoalaBear.fieldSize }

instance : DecidableEq Element := inferInstance

/-- The raw Montgomery word backing a fast KoalaBear element. -/
@[inline]
def raw (x : Element) : UInt32 := x.val

@[simp] theorem modulus_toNat : modulus.toNat = KoalaBear.fieldSize := by
  decide

@[simp] theorem modulus64_toNat : modulus64.toNat = KoalaBear.fieldSize := by
  decide

private theorem fieldSize_pos : 0 < KoalaBear.fieldSize := by
  decide

private theorem fieldSize_lt_uint32Size : KoalaBear.fieldSize < UInt32.size := by
  decide

private theorem fieldSize_add_fieldSize_lt_two64 :
    KoalaBear.fieldSize + KoalaBear.fieldSize < 2 ^ 64 := by
  decide

private theorem fieldSize_add_fieldSize_lt_uint32Size :
    KoalaBear.fieldSize + KoalaBear.fieldSize < UInt32.size := by
  decide

private theorem fieldSize_mul_fieldSize_lt_two64 :
    KoalaBear.fieldSize * KoalaBear.fieldSize < 2 ^ 64 := by
  decide

private theorem uint32Size_lt_three_fieldSize :
    UInt32.size < KoalaBear.fieldSize + KoalaBear.fieldSize + KoalaBear.fieldSize := by
  decide

private theorem fieldSize_mul_uint32Size_lt_two64 :
    KoalaBear.fieldSize * UInt32.size < 2 ^ 64 := by
  decide

private theorem two_fieldSize_mul_uint32Size_lt_two64 :
    2 * KoalaBear.fieldSize * UInt32.size < 2 ^ 64 := by
  decide

private theorem r2ModModulus_lt_fieldSize : r2ModModulus.toNat < KoalaBear.fieldSize := by
  decide

private theorem rModModulus_lt_fieldSize : rModModulus.toNat < KoalaBear.fieldSize := by
  decide

private theorem rModModulus_cast :
    (rModModulus.toNat : KoalaBear.Field) = (UInt32.size : KoalaBear.Field) := by
  decide

private theorem r2ModModulus_cast :
    (r2ModModulus.toNat : KoalaBear.Field) = (UInt32.size : KoalaBear.Field) ^ 2 := by
  decide

private theorem uint32Size_ne_zero_in_field :
    (UInt32.size : KoalaBear.Field) ≠ 0 := by
  decide

private theorem montgomery_sum_dvd (x : Nat) :
    UInt32.size ∣
      x + ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * KoalaBear.fieldSize := by
  rw [← Nat.modEq_zero_iff_dvd]
  have hx : x ≡ x % UInt32.size [MOD UInt32.size] :=
    (Nat.mod_modEq x UInt32.size).symm
  have hm :
      ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * KoalaBear.fieldSize ≡
        (x % UInt32.size) * (UInt32.size - 1) [MOD UInt32.size] := by
    have hmi :
        (x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size ≡
          x % UInt32.size * montgomeryNegInv.toNat [MOD UInt32.size] :=
      Nat.mod_modEq _ _
    have hp : montgomeryNegInv.toNat * KoalaBear.fieldSize ≡ UInt32.size - 1
        [MOD UInt32.size] := by
      decide
    calc
      ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * KoalaBear.fieldSize
          ≡ (x % UInt32.size * montgomeryNegInv.toNat) * KoalaBear.fieldSize
              [MOD UInt32.size] := hmi.mul_right _
      _ = x % UInt32.size * (montgomeryNegInv.toNat * KoalaBear.fieldSize) := by ring
      _ ≡ x % UInt32.size * (UInt32.size - 1) [MOD UInt32.size] := hp.mul_left _
  calc
    x + ((x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) * KoalaBear.fieldSize
        ≡ x % UInt32.size + x % UInt32.size * (UInt32.size - 1) [MOD UInt32.size] :=
          hx.add hm
    _ = x % UInt32.size * UInt32.size := by
      rw [add_comm, ← Nat.mul_succ]
      have hsucc : (UInt32.size - 1).succ = UInt32.size := by decide
      rw [hsucc]
    _ ≡ 0 [MOD UInt32.size] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact ⟨x % UInt32.size, by rw [mul_comm]⟩

private def montgomeryReduceNat (x : Nat) : Nat :=
  let m := (x % UInt32.size * montgomeryNegInv.toNat) % UInt32.size
  let u := (x + m * KoalaBear.fieldSize) / UInt32.size
  if u < KoalaBear.fieldSize then u else u - KoalaBear.fieldSize

private theorem montgomeryReduceNat_lt (x : Nat)
    (h : x < KoalaBear.fieldSize * UInt32.size) :
    montgomeryReduceNat x < KoalaBear.fieldSize := by
  let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  let u := (x + m * KoalaBear.fieldSize) / UInt32.size
  have hm_lt : m < UInt32.size := Nat.mod_lt _ (by decide)
  have hu_lt : u < 2 * KoalaBear.fieldSize := by
    rw [Nat.div_lt_iff_lt_mul]
    · have hprod_lt : m * KoalaBear.fieldSize < UInt32.size * KoalaBear.fieldSize := by
        exact Nat.mul_lt_mul_of_pos_right hm_lt fieldSize_pos
      have hprod_lt' : m * KoalaBear.fieldSize < KoalaBear.fieldSize * UInt32.size := by
        simpa [Nat.mul_comm] using hprod_lt
      nlinarith
    · decide
  by_cases hu : u < KoalaBear.fieldSize
  · unfold montgomeryReduceNat
    change (if u < KoalaBear.fieldSize then u else u - KoalaBear.fieldSize) <
      KoalaBear.fieldSize
    rw [if_pos hu]
    exact hu
  · have hsub : u - KoalaBear.fieldSize < KoalaBear.fieldSize := by omega
    unfold montgomeryReduceNat
    change (if u < KoalaBear.fieldSize then u else u - KoalaBear.fieldSize) <
      KoalaBear.fieldSize
    rw [if_neg hu]
    exact hsub

private theorem montgomeryReduceNat_cast (x : Nat) :
    (montgomeryReduceNat x : KoalaBear.Field) =
      (x : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
  let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  let u := (x + m * KoalaBear.fieldSize) / UInt32.size
  have hdiv : UInt32.size ∣ x + m * KoalaBear.fieldSize := by
    simpa [m] using montgomery_sum_dvd x
  have hu_mul : u * UInt32.size = x + m * KoalaBear.fieldSize := by
    exact Nat.div_mul_cancel hdiv
  have hcast_mul : (u : KoalaBear.Field) * (UInt32.size : KoalaBear.Field) =
      (x : KoalaBear.Field) := by
    rw [← Nat.cast_mul, hu_mul, Nat.cast_add, Nat.cast_mul]
    simp
  have hR := uint32Size_ne_zero_in_field
  by_cases hu : u < KoalaBear.fieldSize
  · have hmain :
        (u : KoalaBear.Field) = (x : KoalaBear.Field) *
          (UInt32.size : KoalaBear.Field)⁻¹ := by
      calc
        (u : KoalaBear.Field) =
            (u : KoalaBear.Field) * (UInt32.size : KoalaBear.Field) *
              (UInt32.size : KoalaBear.Field)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hR, mul_one]
        _ = (x : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
          rw [hcast_mul]
    dsimp only [montgomeryReduceNat]
    rw [if_pos hu]
    exact hmain
  · have hfield :
        ((u - KoalaBear.fieldSize : Nat) : KoalaBear.Field) = (u : KoalaBear.Field) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    have hmain :
        ((u - KoalaBear.fieldSize : Nat) : KoalaBear.Field) =
          (x : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
      rw [hfield]
      calc
        (u : KoalaBear.Field) =
            (u : KoalaBear.Field) * (UInt32.size : KoalaBear.Field) *
              (UInt32.size : KoalaBear.Field)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hR, mul_one]
        _ = (x : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
          rw [hcast_mul]
    dsimp only [montgomeryReduceNat]
    rw [if_neg hu]
    exact hmain

private theorem montgomeryQuotient_cast (x : Nat) :
    (let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
     let u := (x + m * KoalaBear.fieldSize) / UInt32.size
     (u : KoalaBear.Field)) =
      (x : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
  let m := x % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  let u := (x + m * KoalaBear.fieldSize) / UInt32.size
  have hmr := montgomeryReduceNat_cast x
  unfold montgomeryReduceNat at hmr
  change (u : KoalaBear.Field) =
      (x : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
  by_cases hu : u < KoalaBear.fieldSize
  · simpa only [m, u, hu, if_true] using hmr
  · have hfield : ((u - KoalaBear.fieldSize : Nat) : KoalaBear.Field) =
        (u : KoalaBear.Field) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    rw [← hfield]
    simpa only [m, u, hu, if_false] using hmr

private theorem montgomery_u_eq_nat (x : UInt64)
    (h : x.toNat < KoalaBear.fieldSize * UInt32.size) :
    (let m : UInt32 := x.toUInt32 * montgomeryNegInv
     (((x + m.toUInt64 * modulus64) >>> 32).toUInt32).toNat) =
      (x.toNat + ((x.toNat % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) *
        KoalaBear.fieldSize) / UInt32.size := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt64.toNat_ofNat,
    modulus64_toNat, Nat.shiftRight_eq_div_pow]
  norm_num [KoalaBear.fieldSize, UInt32.size] at h ⊢
  let mNat := x.toNat * montgomeryNegInv.toNat % 4294967296
  have hm_lt : mNat < 4294967296 := Nat.mod_lt _ (by decide)
  have hsum_lt : x.toNat + mNat * 2130706433 < 18446744073709551616 := by
    have hprod_lt : mNat * 2130706433 < 2130706433 * 4294967296 := by nlinarith
    nlinarith
  change ((x.toNat + mNat * 2130706433) % 18446744073709551616 / 4294967296) %
      4294967296 = (x.toNat + mNat * 2130706433) / 4294967296
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul]
  · exact hsum_lt
  · decide

private theorem montgomery_u_lt_two_fieldSize (x : UInt64)
    (h : x.toNat < KoalaBear.fieldSize * UInt32.size) :
    (let m : UInt32 := x.toUInt32 * montgomeryNegInv
     (((x + m.toUInt64 * modulus64) >>> 32).toUInt32).toNat) <
      2 * KoalaBear.fieldSize := by
  rw [montgomery_u_eq_nat x h]
  let mNat := x.toNat % UInt32.size * montgomeryNegInv.toNat % UInt32.size
  have hm_lt : mNat < UInt32.size := Nat.mod_lt _ (by decide)
  rw [Nat.div_lt_iff_lt_mul]
  · have hprod_lt : mNat * KoalaBear.fieldSize < UInt32.size * KoalaBear.fieldSize := by
      exact Nat.mul_lt_mul_of_pos_right hm_lt fieldSize_pos
    have hprod_lt' :
        mNat * KoalaBear.fieldSize < KoalaBear.fieldSize * UInt32.size := by
      simpa [Nat.mul_comm] using hprod_lt
    change x.toNat + mNat * KoalaBear.fieldSize < 2 * KoalaBear.fieldSize * UInt32.size
    nlinarith
  · decide

/-- Reduce a native word known to be below twice the KoalaBear prime. -/
@[inline]
private def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  if x < modulus then x else x - modulus

private theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * KoalaBear.fieldSize) :
    (reduceUInt32Lt2ModulusRaw x).toNat < KoalaBear.fieldSize := by
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

/-- Reduce a native word known to be below twice the KoalaBear prime. -/
@[inline]
private def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * KoalaBear.fieldSize) :
    Element :=
  ⟨reduceUInt32Lt2ModulusRaw x, reduceUInt32Lt2ModulusRaw_lt x h⟩

private theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * KoalaBear.fieldSize) :
    ((reduceUInt32Lt2Modulus x h).val.toNat : KoalaBear.Field) =
      (x.toNat : KoalaBear.Field) := by
  change ((reduceUInt32Lt2ModulusRaw x).toNat : KoalaBear.Field) =
    (x.toNat : KoalaBear.Field)
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

private theorem reduceUInt32Lt2Modulus_val_eq_nat (x : UInt32)
    (h : x.toNat < 2 * KoalaBear.fieldSize) :
    (reduceUInt32Lt2Modulus x h).val.toNat = montgomeryReduceNat (x.toNat * UInt32.size) := by
  change (reduceUInt32Lt2ModulusRaw x).toNat = montgomeryReduceNat (x.toNat * UInt32.size)
  unfold reduceUInt32Lt2ModulusRaw montgomeryReduceNat
  have hm_zero :
      (x.toNat * UInt32.size % UInt32.size * montgomeryNegInv.toNat) % UInt32.size = 0 := by
    simp
  rw [hm_zero]
  simp only [zero_mul, add_zero]
  have hdiv : x.toNat * UInt32.size / UInt32.size = x.toNat := by
    rw [Nat.mul_div_cancel _ (by decide : 0 < UInt32.size)]
  rw [hdiv]
  by_cases hx : x < modulus
  · rw [if_pos]
    · have hxNat : x.toNat < KoalaBear.fieldSize := by
        rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
        exact hx
      rw [if_pos hxNat]
    · have hxNat : x.toNat < KoalaBear.fieldSize := by
        rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
        exact hx
      exact hxNat
  · rw [if_neg]
    · have hmod_le_x : modulus ≤ x := by
        rw [UInt32.le_iff_toNat_le, modulus_toNat]
        rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
        exact Nat.le_of_not_gt hx
      have hxNat : ¬x.toNat < KoalaBear.fieldSize := by
        rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
        exact hx
      rw [if_neg hxNat]
      rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, modulus_toNat]
    · have hxNat : ¬x.toNat < KoalaBear.fieldSize := by
        rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
        exact hx
      exact hxNat

/-- Reduce a native word below `2^32` modulo the KoalaBear prime. -/
@[inline]
private def reduceUInt32 (x : UInt32) : Element :=
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
        have hy_eq : y.toNat = x.toNat - KoalaBear.fieldSize := by
          change (x - modulus).toNat = x.toNat - KoalaBear.fieldSize
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
private def montgomeryReduceBoundedRaw (x : UInt64) : UInt32 :=
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  reduceUInt32Lt2ModulusRaw u

private theorem montgomeryReduceBoundedRaw_lt (x : UInt64)
    (h : x.toNat < KoalaBear.fieldSize * UInt32.size) :
    (montgomeryReduceBoundedRaw x).toNat < KoalaBear.fieldSize := by
  unfold montgomeryReduceBoundedRaw
  exact reduceUInt32Lt2ModulusRaw_lt _
    (montgomery_u_lt_two_fieldSize x h)

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
private def montgomeryReduceBounded (x : UInt64)
    (h : x.toNat < KoalaBear.fieldSize * UInt32.size) : Element :=
  ⟨montgomeryReduceBoundedRaw x, montgomeryReduceBoundedRaw_lt x h⟩

private theorem montgomeryReduceBounded_cast (x : UInt64)
    (h : x.toNat < KoalaBear.fieldSize * UInt32.size) :
    ((montgomeryReduceBounded x h).val.toNat : KoalaBear.Field) =
      (x.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
  change ((montgomeryReduceBoundedRaw x).toNat : KoalaBear.Field) =
      (x.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
  unfold montgomeryReduceBoundedRaw
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  change ((reduceUInt32Lt2ModulusRaw u).toNat : KoalaBear.Field) =
    (x.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
  have hred := reduceUInt32Lt2Modulus_cast u (montgomery_u_lt_two_fieldSize x h)
  change ((reduceUInt32Lt2ModulusRaw u).toNat : KoalaBear.Field) =
    (u.toNat : KoalaBear.Field) at hred
  rw [hred]
  change (u.toNat : KoalaBear.Field) =
    (x.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
  rw [show u.toNat =
      (x.toNat + ((x.toNat % UInt32.size * montgomeryNegInv.toNat) % UInt32.size) *
        KoalaBear.fieldSize) / UInt32.size by
    exact montgomery_u_eq_nat x h]
  exact montgomeryQuotient_cast x.toNat

/-- Montgomery reduction of a 64-bit word. Hot bounded callers use `montgomeryReduceBounded`. -/
@[inline]
def montgomeryReduce (x : UInt64) : Element :=
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  reduceUInt32 u

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (_h : n < KoalaBear.fieldSize) : Element :=
  montgomeryReduceBounded (UInt64.ofNat n * r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
    have hnmod : n % 2 ^ 64 = n := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans _h (Nat.lt_trans fieldSize_lt_uint32Size (by decide))
    rw [hnmod]
    have hprod : n * r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [r2ModModulus_lt_fieldSize])

/-- Reduce a `UInt64` modulo the KoalaBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Element :=
  let y := x % modulus64
  montgomeryReduceBounded (y * r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : (x % modulus64).toNat < KoalaBear.fieldSize := by
      rw [UInt64.toNat_mod, modulus64_toNat]
      exact Nat.mod_lt _ fieldSize_pos
    have hprod : (x % modulus64).toNat * r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [r2ModModulus_lt_fieldSize])

/-- The zero fast KoalaBear element. -/
def zero : Element := ⟨0, by decide⟩

/-- The one fast KoalaBear element. -/
def one : Element := ⟨rModModulus, by decide⟩

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (n : Nat) : Element :=
  ofCanonicalNat (n % KoalaBear.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Element :=
  reduceUInt64 x.toUInt64

/-- Convert from the canonical `ZMod` KoalaBear field into fast Montgomery form. -/
@[inline]
def ofField (x : KoalaBear.Field) : Element :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (n : Int) : Element :=
  ofField (n : KoalaBear.Field)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : Element) : UInt32 :=
  raw (montgomeryReduceBounded x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, fieldSize_pos]))

/-- Convert a fast KoalaBear element to its canonical natural representative. -/
@[inline]
def toNat (x : Element) : Nat :=
  (toCanonicalUInt32 x).toNat

/-- Convert a fast KoalaBear element to the canonical `ZMod` KoalaBear field. -/
@[inline]
def toField (x : Element) : KoalaBear.Field :=
  (toNat x : KoalaBear.Field)

private theorem toNat_lt_fieldSize (x : Element) : toNat x < KoalaBear.fieldSize := by
  unfold toNat toCanonicalUInt32 raw
  change (montgomeryReduceBoundedRaw x.val.toUInt64).toNat < KoalaBear.fieldSize
  exact montgomeryReduceBoundedRaw_lt x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, fieldSize_pos])

private theorem toField_eq_raw_mul_inv (x : Element) :
    toField x =
      (x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ := by
  unfold toField toNat toCanonicalUInt32 raw
  have hred := montgomeryReduceBounded_cast x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, fieldSize_pos])
  change ((montgomeryReduceBoundedRaw x.val.toUInt64).toNat : KoalaBear.Field) =
      (x.val.toUInt64.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw x.val.toUInt64).toNat : KoalaBear.Field) =
      (x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
  rw [hred]
  rw [UInt32.toNat_toUInt64]

private theorem raw_cast_eq_toField_mul (x : Element) :
    (x.val.toNat : KoalaBear.Field) =
      toField x * (UInt32.size : KoalaBear.Field) := by
  rw [toField_eq_raw_mul_inv]
  rw [mul_assoc]
  rw [inv_mul_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

private theorem nat_eq_of_field_eq {a b : Nat} (ha : a < KoalaBear.fieldSize)
    (hb : b < KoalaBear.fieldSize) (h : (a : KoalaBear.Field) = (b : KoalaBear.Field)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

private theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < KoalaBear.fieldSize) :
    ((ofCanonicalNat n h).val.toNat : KoalaBear.Field) =
      (n : KoalaBear.Field) * (UInt32.size : KoalaBear.Field) := by
  unfold ofCanonicalNat
  have hred := montgomeryReduceBounded_cast
    (UInt64.ofNat n * r2ModModulus.toUInt64) (by
      rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
      have hnmod : n % 2 ^ 64 = n := by
        apply Nat.mod_eq_of_lt
        exact Nat.lt_trans h (Nat.lt_trans fieldSize_lt_uint32Size (by decide))
      rw [hnmod]
      have hprod : n * r2ModModulus.toNat < 2 ^ 64 := by
        nlinarith [r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
      rw [Nat.mod_eq_of_lt hprod]
      nlinarith [r2ModModulus_lt_fieldSize])
  change ((montgomeryReduceBoundedRaw
      (UInt64.ofNat n * r2ModModulus.toUInt64)).toNat : KoalaBear.Field) =
        ((UInt64.ofNat n * r2ModModulus.toUInt64).toNat : KoalaBear.Field) *
          (UInt32.size : KoalaBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw
      (UInt64.ofNat n * r2ModModulus.toUInt64)).toNat : KoalaBear.Field) =
        (n : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  have hnmod : n % 2 ^ 64 = n := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans h (Nat.lt_trans fieldSize_lt_uint32Size (by decide))
  rw [hnmod]
  have hprod : n * r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul, r2ModModulus_cast]
  rw [pow_two]
  rw [mul_assoc (n : KoalaBear.Field) ((UInt32.size : KoalaBear.Field) *
    (UInt32.size : KoalaBear.Field)) ((UInt32.size : KoalaBear.Field)⁻¹)]
  rw [mul_assoc (UInt32.size : KoalaBear.Field) (UInt32.size : KoalaBear.Field)
    ((UInt32.size : KoalaBear.Field)⁻¹)]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

private theorem toField_ofCanonicalNat_aux (n : Nat) (h : n < KoalaBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : KoalaBear.Field) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

private theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : KoalaBear.Field) =
      (x.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field) := by
  unfold reduceUInt64
  let y := x % modulus64
  have hred := montgomeryReduceBounded_cast (y * r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : y.toNat < KoalaBear.fieldSize := by
      rw [show y = x % modulus64 by rfl, UInt64.toNat_mod, modulus64_toNat]
      exact Nat.mod_lt _ fieldSize_pos
    have hprod : y.toNat * r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [r2ModModulus_lt_fieldSize])
  change ((montgomeryReduceBoundedRaw (y * r2ModModulus.toUInt64)).toNat :
      KoalaBear.Field) =
        ((y * r2ModModulus.toUInt64).toNat : KoalaBear.Field) *
          (UInt32.size : KoalaBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (y * r2ModModulus.toUInt64)).toNat :
      KoalaBear.Field) =
        (x.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hy_lt : y.toNat < KoalaBear.fieldSize := by
    rw [show y = x % modulus64 by rfl, UInt64.toNat_mod, modulus64_toNat]
    exact Nat.mod_lt _ fieldSize_pos
  have hprod : y.toNat * r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [hy_lt, r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  have hy_cast : (y.toNat : KoalaBear.Field) = (x.toNat : KoalaBear.Field) := by
    rw [show y = x % modulus64 by rfl, UInt64.toNat_mod, modulus64_toNat]
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_modEq _ _
  rw [Nat.cast_mul, r2ModModulus_cast, hy_cast]
  rw [pow_two]
  rw [mul_assoc (x.toNat : KoalaBear.Field) ((UInt32.size : KoalaBear.Field) *
    (UInt32.size : KoalaBear.Field)) ((UInt32.size : KoalaBear.Field)⁻¹)]
  rw [mul_assoc (UInt32.size : KoalaBear.Field) (UInt32.size : KoalaBear.Field)
    ((UInt32.size : KoalaBear.Field)⁻¹)]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < KoalaBear.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  exact nat_eq_of_field_eq (toNat_lt_fieldSize _) h (toField_ofCanonicalNat_aux n h)

@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < KoalaBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : KoalaBear.Field) := by
  exact toField_ofCanonicalNat_aux n h

@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 x) = x.toNat % KoalaBear.fieldSize := by
  apply nat_eq_of_field_eq (toNat_lt_fieldSize _) (Nat.mod_lt _ fieldSize_pos)
  change toField (reduceUInt64 x) = ((x.toNat % KoalaBear.fieldSize : Nat) : KoalaBear.Field)
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq _ _).symm

@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 x) = (x.toNat : KoalaBear.Field) := by
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : Element) : Element :=
  reduceUInt32Lt2Modulus (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega))

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : Element) : Element :=
  if hx : x.val = 0 then
    zero
  else
    ⟨modulus - x.val, by
      have hle : x.val ≤ modulus := by
        rw [UInt32.le_iff_toNat_le, modulus_toNat]
        exact Nat.le_of_lt x.property
      rw [UInt32.toNat_sub_of_le _ _ hle, modulus_toNat]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt32.toNat_inj.mp
        simpa using hzero
      omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : Element) : Element :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt32.toNat_sub_of_le _ _ hyx]
      omega⟩
  else
    ⟨x.val + modulus - y.val, by
      have hsum_lt : x.val.toNat + KoalaBear.fieldSize < UInt32.size := by
        have htwo := fieldSize_add_fieldSize_lt_uint32Size
        omega
      have hsum_eq : (x.val + modulus).toNat = x.val.toNat + KoalaBear.fieldSize := by
        rw [UInt32.toNat_add, modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
      have hyle : y.val ≤ x.val + modulus := by
        rw [UInt32.le_iff_toNat_le, hsum_eq]
        omega
      rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
      have hyxNat : ¬y.val.toNat ≤ x.val.toNat := by
        intro hle
        apply hyx
        rw [UInt32.le_iff_toNat_le]
        exact hle
      omega⟩

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : Element) : Element :=
  montgomeryReduceBounded (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, fieldSize_lt_uint32Size, fieldSize_pos])

/-- Fast squaring. -/
@[inline]
def square (x : Element) : Element :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : Element) (n : Nat) : Element :=
  @npowBinRec Element ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the KoalaBear prime field. -/
def invExponent : Nat := KoalaBear.fieldSize - 2

/-- Four squarings followed by multiplication by the next 4-bit exponent digit. -/
@[inline]
private def shift4Mul (acc digit : Element) : Element :=
  mul (square (square (square (square acc)))) digit

/-- Inversion in Montgomery form by a fixed 4-bit Fermat chain. -/
@[inline]
def inv (x : Element) : Element :=
  let x2 := square x
  let x3 := mul x2 x
  let x5 := mul x3 x2
  let x7 := mul x5 x2
  let x14 := square x7
  let x15 := mul x14 x
  let acc := shift4Mul x7 x14
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  shift4Mul acc x15

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Element) : Element :=
  mul x (inv y)

instance instZeroElement : Zero Element where
  zero := zero

instance instOneElement : One Element where
  one := one

instance instAddElement : Add Element where
  add := add

instance instNegElement : Neg Element where
  neg := neg

instance instSubElement : Sub Element where
  sub := sub

instance instMulElement : Mul Element where
  mul := mul

instance instInvElement : Inv Element where
  inv := inv

instance instDivElement : Div Element where
  div := div

instance instNatCastElement : NatCast Element where
  natCast := ofNat

instance instIntCastElement : IntCast Element where
  intCast := ofInt

instance instNatSMulElement : SMul Nat Element where
  smul n x := ofNat n * x

instance instIntSMulElement : SMul Int Element where
  smul n x := ofInt n * x

instance instPowElementNat : Pow Element Nat where
  pow := pow

instance instPowElementInt : Pow Element Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance instNNRatCastElement : NNRatCast Element where
  nnratCast q := ofField (q : KoalaBear.Field)

instance instRatCastElement : RatCast Element where
  ratCast q := ofField (q : KoalaBear.Field)

instance instNNRatSMulElement : SMul ℚ≥0 Element where
  smul q x := ofField (q • toField x)

instance instRatSMulElement : SMul ℚ Element where
  smul q x := ofField (q • toField x)

@[simp]
theorem toField_ofField (x : KoalaBear.Field) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

@[simp]
theorem ofField_toField (x : Element) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  apply nat_eq_of_field_eq
  · exact (ofField (toField x)).property
  · exact x.property
  · rw [raw_cast_eq_toField_mul]
    rw [toField_ofField]
    rw [raw_cast_eq_toField_mul]

theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

@[simp]
theorem toField_zero : toField (0 : Element) = 0 := by
  rw [toField_eq_raw_mul_inv]
  change ((0 : Nat) : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ = 0
  exact zero_mul _

@[simp]
theorem toField_one : toField (1 : Element) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (rModModulus.toNat : KoalaBear.Field) *
      (UInt32.size : KoalaBear.Field)⁻¹ = 1
  rw [rModModulus_cast]
  exact mul_inv_cancel₀ uint32Size_ne_zero_in_field

@[simp]
theorem toField_add (x y : Element) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instAddElement add
  have hred := reduceUInt32Lt2Modulus_cast (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
  change ((reduceUInt32Lt2ModulusRaw (x.val + y.val)).toNat : KoalaBear.Field) =
      ((x.val + y.val).toNat : KoalaBear.Field) at hred
  change ((reduceUInt32Lt2ModulusRaw (x.val + y.val)).toNat : KoalaBear.Field) *
      (UInt32.size : KoalaBear.Field)⁻¹ =
        (x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ +
          (y.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
  rw [hred]
  rw [UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < UInt32.size := by
    nlinarith [x.property, y.property, fieldSize_add_fieldSize_lt_uint32Size]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.cast_add]
  ring

@[simp]
theorem toField_sub (x y : Element) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hsubval : (x - y : Element).val = x.val - y.val := by
      change (sub x y).val = x.val - y.val
      unfold sub
      rw [dif_pos hyx]
    rw [hsubval]
    change (((x.val - y.val).toNat : KoalaBear.Field) *
        (UInt32.size : KoalaBear.Field)⁻¹) =
        (x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ -
          (y.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyx]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hyx
      exact hyx)]
    ring
  · have hsum_lt : x.val.toNat + KoalaBear.fieldSize < UInt32.size := by
      have htwo := fieldSize_add_fieldSize_lt_uint32Size
      omega
    have hsum_eq : (x.val + modulus).toNat = x.val.toNat + KoalaBear.fieldSize := by
      rw [UInt32.toNat_add, modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hyle : y.val ≤ x.val + modulus := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      omega
    have hsubval : (x - y : Element).val = x.val + modulus - y.val := by
      change (sub x y).val = x.val + modulus - y.val
      unfold sub
      rw [dif_neg hyx]
    rw [hsubval]
    change (((x.val + modulus - y.val).toNat : KoalaBear.Field) *
        (UInt32.size : KoalaBear.Field)⁻¹) =
        (x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ -
          (y.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, hsum_eq] at hyle
      exact hyle)]
    rw [Nat.cast_add, ZMod.natCast_self]
    ring

@[simp]
theorem toField_neg (x : Element) : toField (-x) = -toField x := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegval : (-x : Element).val = zero.val := by
      change (neg x).val = zero.val
      unfold neg
      rw [dif_pos hx]
    rw [hnegval]
    change ((zero.val.toNat : KoalaBear.Field) *
        (UInt32.size : KoalaBear.Field)⁻¹) =
        -((x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹)
    have hxNat : x.val.toNat = 0 := by
      simpa using congrArg UInt32.toNat hx
    rw [hxNat]
    change ((0 : Nat) : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ =
      -(((0 : Nat) : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹)
    simp
  · have hle : x.val ≤ modulus := by
      rw [UInt32.le_iff_toNat_le, modulus_toNat]
      exact Nat.le_of_lt x.property
    have hnegval : (-x : Element).val = modulus - x.val := by
      change (neg x).val = modulus - x.val
      unfold neg
      rw [dif_neg hx]
    rw [hnegval]
    change (((modulus - x.val).toNat : KoalaBear.Field) *
        (UInt32.size : KoalaBear.Field)⁻¹) =
        -((x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹)
    rw [UInt32.toNat_sub_of_le _ _ hle, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, modulus_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    ring

@[simp]
theorem toField_mul (x y : Element) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instMulElement mul
  have hred := montgomeryReduceBounded_cast (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, fieldSize_lt_uint32Size, fieldSize_pos])
  change ((montgomeryReduceBoundedRaw (x.val.toUInt64 * y.val.toUInt64)).toNat :
      KoalaBear.Field) =
        ((x.val.toUInt64 * y.val.toUInt64).toNat : KoalaBear.Field) *
          (UInt32.size : KoalaBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (x.val.toUInt64 * y.val.toUInt64)).toNat :
      KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ =
        (x.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹ *
          ((y.val.toNat : KoalaBear.Field) * (UInt32.size : KoalaBear.Field)⁻¹)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul]
  ring

private theorem mul_assoc_element (x y z : Element) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ (x : Element) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup Element := {
    mul := (· * ·)
    mul_assoc := mul_assoc_element
  }
  exact npowBinRec_succ n x

@[simp]
theorem toField_square (x : Element) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

@[simp]
theorem toField_pow (x : Element) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero]
      rw [toField_one]
      simp
  | succ n ih =>
      rw [pow_succ, toField_mul, ih, _root_.pow_succ]

private theorem toField_mul_pow (base x y : Element) (m n : Nat)
    (hx : toField x = toField base ^ m) (hy : toField y = toField base ^ n) :
    toField (mul x y) = toField base ^ (m + n) := by
  change toField (x * y) = toField base ^ (m + n)
  rw [toField_mul, hx, hy, ← pow_add]

private theorem toField_shift4Mul (acc digit : Element) :
    toField (shift4Mul acc digit) = toField acc ^ 16 * toField digit := by
  unfold shift4Mul
  change toField (square (square (square (square acc))) * digit) =
    toField acc ^ 16 * toField digit
  rw [toField_mul]
  repeat rw [toField_square]
  ring

private theorem toField_shift4Mul_pow (base acc digit : Element) (e d : Nat)
    (hacc : toField acc = toField base ^ e) (hdigit : toField digit = toField base ^ d) :
    toField (shift4Mul acc digit) = toField base ^ (16 * e + d) := by
  rw [toField_shift4Mul, hacc, hdigit]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

private theorem toField_inv_pow (x : Element) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv
  let x2 := square x
  let x3 := mul x2 x
  let x5 := mul x3 x2
  let x7 := mul x5 x2
  let x14 := square x7
  let x15 := mul x14 x
  let acc1 := shift4Mul x7 x14
  let acc2 := shift4Mul acc1 x15
  let acc3 := shift4Mul acc2 x15
  let acc4 := shift4Mul acc3 x15
  let acc5 := shift4Mul acc4 x15
  let acc6 := shift4Mul acc5 x15
  have hx1 : toField x = toField x ^ 1 := by simp
  have hx2 : toField x2 = toField x ^ 2 := by
    dsimp [x2]
    rw [toField_square, pow_two]
  have hx3 : toField x3 = toField x ^ 3 := by
    dsimp [x3]
    simpa using toField_mul_pow x x2 x 2 1 hx2 hx1
  have hx5 : toField x5 = toField x ^ 5 := by
    dsimp [x5]
    simpa using toField_mul_pow x x3 x2 3 2 hx3 hx2
  have hx7 : toField x7 = toField x ^ 7 := by
    dsimp [x7]
    simpa using toField_mul_pow x x5 x2 5 2 hx5 hx2
  have hx14 : toField x14 = toField x ^ 14 := by
    dsimp [x14]
    rw [toField_square, hx7, ← pow_add]
  have hx15 : toField x15 = toField x ^ 15 := by
    dsimp [x15]
    simpa using toField_mul_pow x x14 x 14 1 hx14 hx1
  have hacc1 : toField acc1 = toField x ^ 126 := by
    dsimp [acc1]
    simpa using toField_shift4Mul_pow x x7 x14 7 14 hx7 hx14
  have hacc2 : toField acc2 = toField x ^ 2031 := by
    dsimp [acc2]
    simpa using toField_shift4Mul_pow x acc1 x15 126 15 hacc1 hx15
  have hacc3 : toField acc3 = toField x ^ 32511 := by
    dsimp [acc3]
    simpa using toField_shift4Mul_pow x acc2 x15 2031 15 hacc2 hx15
  have hacc4 : toField acc4 = toField x ^ 520191 := by
    dsimp [acc4]
    simpa using toField_shift4Mul_pow x acc3 x15 32511 15 hacc3 hx15
  have hacc5 : toField acc5 = toField x ^ 8323071 := by
    dsimp [acc5]
    simpa using toField_shift4Mul_pow x acc4 x15 520191 15 hacc4 hx15
  have hacc6 : toField acc6 = toField x ^ 133169151 := by
    dsimp [acc6]
    simpa using toField_shift4Mul_pow x acc5 x15 8323071 15 hacc5 hx15
  have hfinal := toField_shift4Mul_pow x acc6 x15 133169151 15 hacc6 hx15
  simpa [invExponent, KoalaBear.fieldSize] using hfinal

private theorem toField_inv_raw (x : Element) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx]
    simp [invExponent, KoalaBear.fieldSize]
  · simpa [invExponent] using (KoalaBear.inv_eq_pow (toField x) hx).symm

@[simp]
theorem toField_inv (x : Element) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_mul_raw (x y : Element) : toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

private theorem toField_div_mul_inv (x y : Element) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  exact toField_mul_raw x (inv y)

@[simp]
theorem toField_div (x y : Element) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : KoalaBear.Field, c = b⁻¹ → a * c = a / b := by
    intro a b c hc
    rw [hc]
    rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

@[simp]
theorem toField_natCast (n : Nat) : toField (n : Element) = (n : KoalaBear.Field) := by
  change toField (ofNat n) = (n : KoalaBear.Field)
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

@[simp]
theorem toField_intCast (n : Int) : toField (n : Element) = (n : KoalaBear.Field) := by
  change toField (ofInt n) = (n : KoalaBear.Field)
  unfold ofInt
  rw [toField_ofField]

@[simp]
theorem toField_nsmul (n : Nat) (x : Element) : toField (n • x) = n • toField x := by
  change toField ((n : Element) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

@[simp]
theorem toField_zsmul (n : Int) (x : Element) : toField (n • x) = n • toField x := by
  change toField ((n : Element) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

@[simp]
theorem toField_npow (x : Element) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

@[simp]
theorem toField_zpow (x : Element) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := by
        change toField x⁻¹ = (toField x)⁻¹
        rw [toField_inv]
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Element) = (q : KoalaBear.Field) := by
  change toField (ofField (q : KoalaBear.Field)) = (q : KoalaBear.Field)
  rw [toField_ofField]

@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Element) = (q : KoalaBear.Field) := by
  change toField (ofField (q : KoalaBear.Field)) = (q : KoalaBear.Field)
  rw [toField_ofField]

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Element) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

@[simp]
theorem toField_qsmul (q : ℚ) (x : Element) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

instance (priority := low) instFieldElement : _root_.Field Element :=
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

instance (priority := low) instCommRingElement : CommRing Element := by
  infer_instance

instance (priority := low) instNonBinaryFieldElement : NonBinaryField Element where
  char_neq_2 := by
    change ((2 : Nat) : Element) ≠ 0
    intro h
    exact NonBinaryField.char_neq_2 (F := KoalaBear.Field) (by
      calc
        (2 : KoalaBear.Field) = toField ((2 : Nat) : Element) := (toField_natCast 2).symm
        _ = toField (0 : Element) := congrArg toField h
        _ = 0 := toField_zero)

end Fast
end KoalaBear
