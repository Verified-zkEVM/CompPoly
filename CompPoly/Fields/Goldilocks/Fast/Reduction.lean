/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast.Internal

/-!
# Raw Reducers for Fast Goldilocks Arithmetic

This module contains the raw `UInt64` arithmetic kernels and their correctness
lemmas. The public fast field API wraps these kernels in
`CompPoly.Fields.Goldilocks.Fast`.
-/

namespace Goldilocks
namespace Fast
namespace Reduction

/-- Full 64-by-64 product as `(lo, hi)` words, computed from 32-bit limbs. -/
@[inline]
def wideMul (x y : UInt64) : UInt64 × UInt64 :=
  let xLo := x &&& neg_modulus
  let xHi := x >>> 32
  let yLo := y &&& neg_modulus
  let yHi := y >>> 32
  let p00 := xLo * yLo
  let p01 := xLo * yHi
  let p10 := xHi * yLo
  let p11 := xHi * yHi
  let carry := (p00 >>> 32) + (p01 &&& neg_modulus) + (p10 &&& neg_modulus)
  let hi := p11 + (p01 >>> 32) + (p10 >>> 32) + (carry >>> 32)
  (x * y, hi)

/-- Raw one-word reduction for a `UInt64` value.

Since every `UInt64` is below `2^64 = p + 2^32 - 1`, one subtraction by `p`
is enough to canonicalize a native word.
-/
@[inline]
def reduceUInt64Raw (x : UInt64) : UInt64 :=
  if x < modulus then x else x - modulus

/-- The raw one-word reducer returns a canonical representative. -/
theorem reduceUInt64Raw_lt (x : UInt64) :
    (reduceUInt64Raw x).toNat < Goldilocks.Basic.fieldSize := by
  unfold reduceUInt64Raw
  by_cases hx : x < modulus
  · rw [if_pos hx]
    rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
    exact hx
  · rw [if_neg hx]
    have hmod_le_x_nat : Goldilocks.Basic.fieldSize ≤ x.toNat := by
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
    ((reduceUInt64Raw x).toNat : Goldilocks.Basic.Field) =
      (x.toNat : Goldilocks.Basic.Field) := by
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

/-- Raw reduction of a 128-bit integer represented by low and high words modulo Goldilocks. -/
@[inline]
def reduceUInt128Raw (lo hi : UInt64) : UInt64 :=
  let hi_hi := hi >>> 32
  let hi_lo := hi &&& neg_modulus

  let borrow := lo < hi_hi
  let t0 := lo - hi_hi
  let t0 := if borrow then t0 - neg_modulus else t0

  let t1 := hi_lo * neg_modulus

  let t2 := t0 + t1
  let overflow := t2 < t0
  let t2 := if overflow then t2 + neg_modulus else t2

  reduceUInt64Raw t2

/-- The raw 128-bit reducer returns a canonical representative below the modulus. -/
theorem reduceUInt128Raw_lt (lo hi : UInt64) :
    (reduceUInt128Raw lo hi).toNat < Goldilocks.Basic.fieldSize := by
  unfold reduceUInt128Raw
  apply reduceUInt64Raw_lt

/-- Semantic correctness of raw 128-bit Goldilocks reduction. -/
theorem reduceUInt128Raw_cast (lo hi : UInt64) :
    ((reduceUInt128Raw lo hi).toNat : Goldilocks.Basic.Field) =
      (lo.toNat : Goldilocks.Basic.Field) +
        (hi.toNat : Goldilocks.Basic.Field) * (UInt64.size : Goldilocks.Basic.Field) := by
  let hi_hi := hi >>> 32
  let hi_lo := hi &&& neg_modulus
  let t0 := if lo < hi_hi then lo - hi_hi - neg_modulus else lo - hi_hi
  let t1 := hi_lo * neg_modulus
  let t2 := if t0 + t1 < t0 then t0 + t1 + neg_modulus else t0 + t1
  change ((reduceUInt64Raw t2).toNat : Goldilocks.Basic.Field) =
    (lo.toNat : Goldilocks.Basic.Field) +
      (hi.toNat : Goldilocks.Basic.Field) * (UInt64.size : Goldilocks.Basic.Field)
  have hred := reduceUInt64Raw_cast t2
  change ((reduceUInt64Raw t2).toNat : Goldilocks.Basic.Field) =
    (t2.toNat : Goldilocks.Basic.Field) at hred
  rw [hred]
  have hhi_hi_lt : hi_hi.toNat < 2 ^ 32 := by
    rw [show hi_hi = hi >>> 32 by rfl, shiftRight32_toNat]
    have hhi := UInt64.toNat_lt_size hi
    change hi.toNat < 2 ^ 64 at hhi
    omega
  have hhi_lo_lt : hi_lo.toNat < 2 ^ 32 := by
    rw [show hi_lo = hi &&& neg_modulus by rfl, and_neg_modulus_toNat]
    exact Nat.mod_lt _ (by decide)
  have ht0_cast :
      (t0.toNat : Goldilocks.Basic.Field) =
        (lo.toNat : Goldilocks.Basic.Field) - (hi_hi.toNat : Goldilocks.Basic.Field) := by
    rw [show t0 = if lo < hi_hi then lo - hi_hi - neg_modulus else lo - hi_hi by rfl]
    exact subBorrow_cast lo hi_hi hhi_hi_lt
  have ht1_cast :
      (t1.toNat : Goldilocks.Basic.Field) =
        (hi_lo.toNat : Goldilocks.Basic.Field) *
          (neg_modulus.toNat : Goldilocks.Basic.Field) := by
    rw [show t1 = hi_lo * neg_modulus by rfl]
    rw [mul_neg_modulus_toNat_of_lt hi_lo hhi_lo_lt]
    rw [Nat.cast_mul]
  have ht2_bound : t0.toNat + t1.toNat < 2 * UInt64.size - neg_modulus.toNat := by
    have ht0_lt := UInt64.toNat_lt_size t0
    have ht1_le : t1.toNat ≤ UInt64.size - 2 * neg_modulus.toNat := by
      simpa [t1] using mul_neg_modulus_toNat_le hi_lo hhi_lo_lt
    have htwice_neg_le_size : 2 * neg_modulus.toNat ≤ UInt64.size := by
      decide
    omega
  have ht2_cast :
      (t2.toNat : Goldilocks.Basic.Field) =
        (t0.toNat : Goldilocks.Basic.Field) + (t1.toNat : Goldilocks.Basic.Field) := by
    rw [show t2 = if t0 + t1 < t0 then t0 + t1 + neg_modulus else t0 + t1 by rfl]
    exact addOverflowBounded_cast t0 t1 ht2_bound
  rw [ht2_cast, ht0_cast, ht1_cast]
  rw [hi_split_cast hi]
  ring

/-- Raw reduction of a 64-by-64 product modulo Goldilocks. -/
@[inline]
def reduceMulRaw (x y : UInt64) : UInt64 :=
  let product := wideMul x y
  reduceUInt128Raw product.1 product.2

/-- Product reduction returns a canonical representative below the modulus. -/
theorem reduceMulRaw_lt (x y : UInt64) :
    (reduceMulRaw x y).toNat < Goldilocks.Basic.fieldSize := by
  unfold reduceMulRaw
  apply reduceUInt128Raw_lt

/-- Semantic correctness of native 64-by-64 product reduction. -/
theorem reduceMulRaw_cast (x y : UInt64) :
    ((reduceMulRaw x y).toNat : Goldilocks.Basic.Field) =
      (x.toNat : Goldilocks.Basic.Field) * (y.toNat : Goldilocks.Basic.Field) := by
  unfold reduceMulRaw
  rw [reduceUInt128Raw_cast]
  exact
    wideMul_cast x y (wideMul x y).1 (wideMul x y).2
      (by unfold wideMul; rfl)
      (by
        unfold wideMul
        exact wideMul_high_toNat x y _ rfl)

/-- Raw one-step reduction for a 65-bit addition represented by low word and carry. -/
@[inline]
def reduceAddWithCarryRaw (lo : UInt64) (carry : Bool) : UInt64 :=
  if carry then
    lo + neg_modulus
  else
    reduceUInt64Raw lo

/-- Addition reduction returns a canonical representative. -/
theorem reduceAddWithCarryRaw_lt (lo : UInt64) (carry : Bool)
    (h :
      lo.toNat + (if carry then UInt64.size else 0) < 2 * Goldilocks.Basic.fieldSize) :
    (reduceAddWithCarryRaw lo carry).toNat < Goldilocks.Basic.fieldSize := by
  unfold reduceAddWithCarryRaw
  cases carry
  · simp only [Bool.false_eq_true, if_false]
    exact reduceUInt64Raw_lt lo
  · simp only [↓reduceIte] at h ⊢
    rw [UInt64.toNat_add]
    have hsum_lt_field : lo.toNat + neg_modulus.toNat < Goldilocks.Basic.fieldSize := by
      rw [neg_modulus_toNat, Goldilocks.Basic.fieldSize]
      rw [Goldilocks.Basic.fieldSize, UInt64.size] at h
      omega
    have hsum_lt_size : lo.toNat + neg_modulus.toNat < UInt64.size :=
      Nat.lt_trans hsum_lt_field fieldSize_lt_uint64Size
    rw [Nat.mod_eq_of_lt hsum_lt_size]
    exact hsum_lt_field

/-- Semantic correctness of addition reduction with carry. -/
theorem reduceAddWithCarryRaw_cast (lo : UInt64) (carry : Bool)
    (h :
      lo.toNat + (if carry then UInt64.size else 0) < 2 * Goldilocks.Basic.fieldSize) :
    ((reduceAddWithCarryRaw lo carry).toNat : Goldilocks.Basic.Field) =
      (lo.toNat : Goldilocks.Basic.Field) +
        (if carry then (UInt64.size : Goldilocks.Basic.Field) else 0) := by
  unfold reduceAddWithCarryRaw
  cases carry
  · simp only [Bool.false_eq_true, if_false, add_zero]
    exact reduceUInt64Raw_cast lo
  · simp only [↓reduceIte]
    change lo.toNat + UInt64.size < 2 * Goldilocks.Basic.fieldSize at h
    rw [UInt64.toNat_add]
    have hsum_lt_field : lo.toNat + neg_modulus.toNat < Goldilocks.Basic.fieldSize := by
      rw [neg_modulus_toNat, Goldilocks.Basic.fieldSize]
      rw [Goldilocks.Basic.fieldSize, UInt64.size] at h
      omega
    have hsum_lt_size : lo.toNat + neg_modulus.toNat < UInt64.size :=
      Nat.lt_trans hsum_lt_field fieldSize_lt_uint64Size
    rw [Nat.mod_eq_of_lt hsum_lt_size]
    rw [Nat.cast_add]
    rw [uint64_cast_eq_neg_modulus]

/-- The wrapped word and carry produced by adding two canonical representatives is bounded. -/
theorem addWithCarry_bound (x y : UInt64)
    (hx : x.toNat < Goldilocks.Basic.fieldSize)
    (hy : y.toNat < Goldilocks.Basic.fieldSize) :
    let lo := x + y
    let carry := decide (lo < x)
    lo.toNat + (if carry then UInt64.size else 0) < 2 * Goldilocks.Basic.fieldSize := by
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
      2 * Goldilocks.Basic.fieldSize
    have hsum_lt_field : x.toNat + y.toNat < 2 * Goldilocks.Basic.fieldSize := by
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

/-- Raw modular negation in canonical form. -/
@[inline]
def negRaw (x : UInt64) : UInt64 :=
  if x = 0 then 0 else modulus - x

/-- Raw negation returns a canonical representative when given one. -/
theorem negRaw_lt (x : UInt64) (hx : x.toNat < Goldilocks.Basic.fieldSize) :
    (negRaw x).toNat < Goldilocks.Basic.fieldSize := by
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
theorem negRaw_cast (x : UInt64) (hx : x.toNat < Goldilocks.Basic.fieldSize) :
    ((negRaw x).toNat : Goldilocks.Basic.Field) =
      -((x.toNat : Goldilocks.Basic.Field)) := by
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

/-- Raw modular subtraction in canonical form. -/
@[inline]
def subRaw (x y : UInt64) : UInt64 :=
  if y ≤ x then x - y else x - y - neg_modulus

/-- Raw subtraction returns a canonical representative when given canonical operands. -/
theorem subRaw_lt (x y : UInt64)
    (hx : x.toNat < Goldilocks.Basic.fieldSize)
    (hy : y.toNat < Goldilocks.Basic.fieldSize) :
    (subRaw x y).toNat < Goldilocks.Basic.fieldSize := by
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
    have hneg_le_raw_nat : neg_modulus.toNat ≤ (x - y).toNat := by
      rw [hraw_toNat, neg_modulus_toNat]
      have hy_lt_field : y.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
        simpa [Goldilocks.Basic.fieldSize] using hy
      omega
    have hneg_le_raw : neg_modulus ≤ x - y := by
      rw [UInt64.le_iff_toNat_le]
      exact hneg_le_raw_nat
    rw [UInt64.toNat_sub_of_le _ _ hneg_le_raw, hraw_toNat, neg_modulus_toNat]
    change 2 ^ 64 - y.toNat + x.toNat - (2 ^ 32 - 1) <
      2 ^ 64 - 2 ^ 32 + 1
    have hx_lt_field : x.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
      simpa [Goldilocks.Basic.fieldSize] using hx
    have hy_lt_field : y.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
      simpa [Goldilocks.Basic.fieldSize] using hy
    omega

/-- Raw subtraction agrees with canonical-field subtraction for canonical operands. -/
theorem subRaw_cast (x y : UInt64)
    (_hx : x.toNat < Goldilocks.Basic.fieldSize)
    (hy : y.toNat < Goldilocks.Basic.fieldSize) :
    ((subRaw x y).toNat : Goldilocks.Basic.Field) =
      (x.toNat : Goldilocks.Basic.Field) - (y.toNat : Goldilocks.Basic.Field) := by
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
    have hneg_le_raw_nat : neg_modulus.toNat ≤ (x - y).toNat := by
      rw [hraw_toNat, neg_modulus_toNat]
      have hy_lt_field : y.toNat < 2 ^ 64 - 2 ^ 32 + 1 := by
        simpa [Goldilocks.Basic.fieldSize] using hy
      omega
    have hneg_le_raw : neg_modulus ≤ x - y := by
      rw [UInt64.le_iff_toNat_le]
      exact hneg_le_raw_nat
    rw [UInt64.toNat_sub_of_le _ _ hneg_le_raw, hraw_toNat, neg_modulus_toNat]
    change (((UInt64.size - y.toNat + x.toNat - neg_modulus.toNat : Nat) :
        Goldilocks.Basic.Field) =
      (x.toNat : Goldilocks.Basic.Field) - (y.toNat : Goldilocks.Basic.Field))
    have hneg_le_concrete : neg_modulus.toNat ≤ UInt64.size - y.toNat + x.toNat := by
      simpa [UInt64.size, hraw_toNat] using hneg_le_raw_nat
    rw [Nat.cast_sub hneg_le_concrete]
    rw [Nat.cast_add]
    rw [Nat.cast_sub (Nat.le_of_lt (UInt64.toNat_lt_size y))]
    rw [uint64_cast_eq_neg_modulus]
    ring

end Reduction
end Fast
end Goldilocks
