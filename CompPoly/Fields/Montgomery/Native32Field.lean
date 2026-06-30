/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.Montgomery.Native32
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fast 32-bit-word prime fields — shared implementation

A `BabyBear`-style and `KoalaBear`-style fast field differ only in a handful of word
constants; their definitions, the proofs about them, and the resulting algebraic instances
are otherwise identical. This module captures that common content **once**, parameterized
by a `Mont32Field` instance that supplies the per-field data.

* `Mont32Field F` bundles the prime (`fieldSize`), its native-word forms, the Montgomery
  constants, and the small `decide`-checkable numeric/`ZMod` facts the proofs consume.
  Everything except the five word constants is spec-level and erased at codegen.
* `FastField F` is the fast carrier `{ x : UInt32 // x.toNat < fieldSize }`, indexed by the
  tag `F` so that the generic `Add`/`Mul`/`Field`/… instances below resolve for each
  concrete field's `Field := FastField <tag>`. At runtime it erases to `UInt32`.
* The executable `def`s are `@[inline]`/`@[specialize]`, so once a concrete instance is
  fixed the instance projections fold to literals and the compiled code is identical to a
  hand-written monomorphic version — no `Mont32Field` dictionary survives to runtime.

The radix-generic number theory lives in `CompPoly.Fields.Montgomery.Basic` and the
`R = 2^32` word bridge in `CompPoly.Fields.Montgomery.Native32`. A concrete fast field is
then just a `Mont32Field` instance plus thin re-export shims.
-/

namespace Montgomery
namespace Native32

/-- Per-field data for a fast 32-bit-word Montgomery prime field.

The five word constants (`modulus`, `modulus64`, `rModModulus`, `r2ModModulus`,
`montgomeryNegInv`) are the only runtime data; the remaining fields are `Prop`s, all
dischargeable by `decide` for a concrete field, and are erased at codegen. `F` is a tag
(in practice the canonical `ZMod fieldSize` field) used for instance resolution. -/
class Mont32Field (F : Type) where
  /-- The field size / prime `p`. -/
  fieldSize : Nat
  /-- `fieldSize` is prime — needed to reduce into `ZMod fieldSize` as a field. -/
  prime : Fact (Nat.Prime fieldSize)
  /-- `fieldSize` as a 32-bit word. -/
  modulus : UInt32
  /-- `fieldSize` as a 64-bit word. -/
  modulus64 : UInt64
  /-- `2^32 mod fieldSize`, the Montgomery representation of one. -/
  rModModulus : UInt32
  /-- `(2^32)^2 mod fieldSize`, used to enter Montgomery form. -/
  r2ModModulus : UInt32
  /-- `-fieldSize⁻¹ mod 2^32`, used by Montgomery reduction. -/
  montgomeryNegInv : UInt32
  modulus_toNat : modulus.toNat = fieldSize
  modulus64_toNat : modulus64.toNat = fieldSize
  fieldSize_pos : 0 < fieldSize
  two_lt_fieldSize : 2 < fieldSize
  fieldSize_lt_uint32Size : fieldSize < UInt32.size
  fieldSize_add_fieldSize_lt_two64 : fieldSize + fieldSize < 2 ^ 64
  fieldSize_add_fieldSize_lt_uint32Size : fieldSize + fieldSize < UInt32.size
  fieldSize_mul_fieldSize_lt_two64 : fieldSize * fieldSize < 2 ^ 64
  uint32Size_lt_three_fieldSize : UInt32.size < fieldSize + fieldSize + fieldSize
  fieldSize_mul_uint32Size_lt_two64 : fieldSize * UInt32.size < 2 ^ 64
  two_fieldSize_mul_uint32Size_lt_two64 : 2 * fieldSize * UInt32.size < 2 ^ 64
  uint32Size_ne_zero_in_field : (UInt32.size : ZMod fieldSize) ≠ 0
  rModModulus_lt_fieldSize : rModModulus.toNat < fieldSize
  r2ModModulus_lt_fieldSize : r2ModModulus.toNat < fieldSize
  rModModulus_cast : (rModModulus.toNat : ZMod fieldSize) = (UInt32.size : ZMod fieldSize)
  r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod fieldSize) = (UInt32.size : ZMod fieldSize) ^ 2
  /-- The Montgomery inverse congruence `negInv * p ≡ 2^32 - 1 [MOD 2^32]`. -/
  negInv_congr :
    montgomeryNegInv.toNat * fieldSize ≡ UInt32.size - 1 [MOD UInt32.size]
  /-- Characteristic `≠ 2`, used to build the `NonBinaryField` instance. -/
  two_ne_zero_in_field : (2 : ZMod fieldSize) ≠ 0

attribute [instance] Mont32Field.prime

/-- The fast carrier for the field tagged by `F`: a native word below `fieldSize`,
interpreted as a Montgomery residue. At runtime this erases to `UInt32`. -/
def FastField (F : Type) [Mont32Field F] : Type :=
  { x : UInt32 // x.toNat < Mont32Field.fieldSize F }

instance (F : Type) [Mont32Field F] : DecidableEq (FastField F) :=
  inferInstanceAs (DecidableEq { x : UInt32 // x.toNat < Mont32Field.fieldSize F })

section
variable {F : Type} [P : Mont32Field F]

instance : NeZero P.fieldSize := ⟨P.fieldSize_pos.ne'⟩

/-- The raw Montgomery word backing a fast element. -/
@[inline]
def raw (x : FastField F) : UInt32 := x.val

/-! ## Montgomery reduction -/

/-- Reduce a native word known to be below twice the prime. -/
@[inline]
def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  if x < P.modulus then x else x - P.modulus

theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * P.fieldSize) :
    (reduceUInt32Lt2ModulusRaw (F := F) x).toNat < P.fieldSize := by
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < P.modulus
  · rw [if_pos hx]
    rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hx
    exact hx
  · rw [if_neg hx]
    have hmod_le_x : P.modulus ≤ x := by
      rw [UInt32.le_iff_toNat_le, P.modulus_toNat]
      rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, P.modulus_toNat]
    omega

/-- Reduce a native word known to be below twice the prime. -/
@[inline]
def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * P.fieldSize) :
    FastField F :=
  ⟨reduceUInt32Lt2ModulusRaw (F := F) x, reduceUInt32Lt2ModulusRaw_lt x h⟩

theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * P.fieldSize) :
    ((reduceUInt32Lt2Modulus (F := F) x h).val.toNat : ZMod P.fieldSize) =
      (x.toNat : ZMod P.fieldSize) := by
  change ((reduceUInt32Lt2ModulusRaw (F := F) x).toNat : ZMod P.fieldSize) =
    (x.toNat : ZMod P.fieldSize)
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < P.modulus
  · rw [if_pos hx]
  · have hmod_le_x : P.modulus ≤ x := by
      rw [UInt32.le_iff_toNat_le, P.modulus_toNat]
      rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [if_neg hx]
    rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, P.modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, P.modulus_toNat] at hmod_le_x
      exact hmod_le_x)]
    simp

/-- Reduce a native word below `2^32` modulo the prime. -/
@[inline]
def reduceUInt32 (x : UInt32) : FastField F :=
  if hx : x < P.modulus then
    ⟨x, by
      rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hx
      exact hx⟩
  else
    let y := x - P.modulus
    if hy : y < P.modulus then
      ⟨y, by
        rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hy
        exact hy⟩
    else
      ⟨y - P.modulus, by
        have hmod_le_x : P.modulus ≤ x := by
          rw [UInt32.le_iff_toNat_le, P.modulus_toNat]
          rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hx
          exact Nat.le_of_not_gt hx
        have hy_eq : y.toNat = x.toNat - P.fieldSize := by
          change (x - P.modulus).toNat = x.toNat - P.fieldSize
          rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, P.modulus_toNat]
        have hmod_le_y : P.modulus ≤ y := by
          rw [UInt32.le_iff_toNat_le, P.modulus_toNat]
          rw [UInt32.lt_iff_toNat_lt, P.modulus_toNat] at hy
          exact Nat.le_of_not_gt hy
        rw [UInt32.toNat_sub_of_le _ _ hmod_le_y, P.modulus_toNat, hy_eq]
        have hx_lt := UInt32.toNat_lt_size x
        have hthree := P.uint32Size_lt_three_fieldSize
        omega⟩

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBoundedRaw (x : UInt64) : UInt32 :=
  let m : UInt32 := x.toUInt32 * P.montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * P.modulus64) >>> 32).toUInt32
  reduceUInt32Lt2ModulusRaw (F := F) u

theorem montgomeryReduceBoundedRaw_lt (x : UInt64)
    (h : x.toNat < P.fieldSize * UInt32.size) :
    (montgomeryReduceBoundedRaw (F := F) x).toNat < P.fieldSize := by
  unfold montgomeryReduceBoundedRaw
  exact reduceUInt32Lt2ModulusRaw_lt _
    (Montgomery.Native32.u_lt_two_mul P.montgomeryNegInv P.modulus64 P.fieldSize
      P.modulus64_toNat P.fieldSize_pos P.two_fieldSize_mul_uint32Size_lt_two64 x h)

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBounded (x : UInt64)
    (h : x.toNat < P.fieldSize * UInt32.size) : FastField F :=
  ⟨montgomeryReduceBoundedRaw (F := F) x, montgomeryReduceBoundedRaw_lt x h⟩

theorem montgomeryReduceBounded_cast (x : UInt64)
    (h : x.toNat < P.fieldSize * UInt32.size) :
    ((montgomeryReduceBounded (F := F) x h).val.toNat : ZMod P.fieldSize) =
      (x.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ := by
  change ((montgomeryReduceBoundedRaw (F := F) x).toNat : ZMod P.fieldSize) =
      (x.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
  unfold montgomeryReduceBoundedRaw
  let m : UInt32 := x.toUInt32 * P.montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * P.modulus64) >>> 32).toUInt32
  change ((reduceUInt32Lt2ModulusRaw (F := F) u).toNat : ZMod P.fieldSize) =
    (x.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
  have hred := reduceUInt32Lt2Modulus_cast (F := F) u
    (Montgomery.Native32.u_lt_two_mul P.montgomeryNegInv P.modulus64 P.fieldSize
      P.modulus64_toNat P.fieldSize_pos P.two_fieldSize_mul_uint32Size_lt_two64 x h)
  change ((reduceUInt32Lt2ModulusRaw (F := F) u).toNat : ZMod P.fieldSize) =
    (u.toNat : ZMod P.fieldSize) at hred
  rw [hred]
  change (u.toNat : ZMod P.fieldSize) =
    (x.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
  rw [show u.toNat =
      (x.toNat + ((x.toNat % UInt32.size * P.montgomeryNegInv.toNat) % UInt32.size) *
        P.fieldSize) / UInt32.size by
    exact Montgomery.Native32.u_eq_nat P.montgomeryNegInv P.modulus64 P.fieldSize
      P.modulus64_toNat P.fieldSize_pos P.two_fieldSize_mul_uint32Size_lt_two64 x h]
  exact Montgomery.quotient_cast UInt32.size P.fieldSize P.montgomeryNegInv.toNat
    (by decide) P.negInv_congr P.uint32Size_ne_zero_in_field x.toNat

/-- Montgomery reduction of a 64-bit word. Hot bounded callers use `montgomeryReduceBounded`. -/
@[inline]
def montgomeryReduce (x : UInt64) : FastField F :=
  let m : UInt32 := x.toUInt32 * P.montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * P.modulus64) >>> 32).toUInt32
  reduceUInt32 (F := F) u

/-! ## Conversions -/

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (_h : n < P.fieldSize) : FastField F :=
  montgomeryReduceBounded (UInt64.ofNat n * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
    have hnmod : n % 2 ^ 64 = n := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans _h (Nat.lt_trans P.fieldSize_lt_uint32Size (by decide))
    rw [hnmod]
    have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [P.r2ModModulus_lt_fieldSize, P.fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_fieldSize])

/-- Reduce a `UInt64` modulo the prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : FastField F :=
  let y := x % P.modulus64
  montgomeryReduceBounded (y * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : (x % P.modulus64).toNat < P.fieldSize := by
      rw [UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.fieldSize_pos
    have hprod : (x % P.modulus64).toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, P.r2ModModulus_lt_fieldSize, P.fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_fieldSize])

/-- The zero fast element. -/
def zero : FastField F := ⟨0, by
  have h0 : (0 : UInt32).toNat = 0 := by decide
  have hp := P.fieldSize_pos
  omega⟩

/-- The one fast element. -/
def one : FastField F := ⟨P.rModModulus, P.rModModulus_lt_fieldSize⟩

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (n : Nat) : FastField F :=
  ofCanonicalNat (n % P.fieldSize) (Nat.mod_lt _ P.fieldSize_pos)

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : FastField F :=
  reduceUInt64 x.toUInt64

/-- Convert from the canonical `ZMod` field into fast Montgomery form. -/
@[inline]
def ofField (x : ZMod P.fieldSize) : FastField F :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (n : Int) : FastField F :=
  ofField (n : ZMod P.fieldSize)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : FastField F) : UInt32 :=
  raw (montgomeryReduceBounded x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.fieldSize_pos]))

/-- Convert a fast element to its canonical natural representative. -/
@[inline]
def toNat (x : FastField F) : Nat :=
  (toCanonicalUInt32 x).toNat

/-- Convert a fast element to the canonical `ZMod` field. -/
@[inline]
def toField (x : FastField F) : ZMod P.fieldSize :=
  (toNat x : ZMod P.fieldSize)

theorem toNat_lt_fieldSize (x : FastField F) : toNat x < P.fieldSize := by
  unfold toNat toCanonicalUInt32 raw
  change (montgomeryReduceBoundedRaw (F := F) x.val.toUInt64).toNat < P.fieldSize
  exact montgomeryReduceBoundedRaw_lt x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.fieldSize_pos])

theorem toField_eq_raw_mul_inv (x : FastField F) :
    toField x =
      (x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ := by
  unfold toField toNat toCanonicalUInt32 raw
  have hred := montgomeryReduceBounded_cast x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.fieldSize_pos])
  change ((montgomeryReduceBoundedRaw (F := F) x.val.toUInt64).toNat : ZMod P.fieldSize) =
      (x.val.toUInt64.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F) x.val.toUInt64).toNat : ZMod P.fieldSize) =
      (x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
  rw [hred]
  rw [UInt32.toNat_toUInt64]

theorem raw_cast_eq_toField_mul (x : FastField F) :
    (x.val.toNat : ZMod P.fieldSize) =
      toField x * (UInt32.size : ZMod P.fieldSize) := by
  rw [toField_eq_raw_mul_inv]
  rw [mul_assoc]
  rw [inv_mul_cancel₀ P.uint32Size_ne_zero_in_field]
  rw [mul_one]

theorem nat_eq_of_field_eq {a b : Nat} (ha : a < P.fieldSize)
    (hb : b < P.fieldSize) (h : (a : ZMod P.fieldSize) = (b : ZMod P.fieldSize)) :
    a = b :=
  Montgomery.natCast_inj ha hb h

theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < P.fieldSize) :
    ((ofCanonicalNat (F := F) n h).val.toNat : ZMod P.fieldSize) =
      (n : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize) := by
  unfold ofCanonicalNat
  have hred := montgomeryReduceBounded_cast
    (UInt64.ofNat n * P.r2ModModulus.toUInt64) (by
      rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
      have hnmod : n % 2 ^ 64 = n := by
        apply Nat.mod_eq_of_lt
        exact Nat.lt_trans h (Nat.lt_trans P.fieldSize_lt_uint32Size (by decide))
      rw [hnmod]
      have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
        nlinarith [P.r2ModModulus_lt_fieldSize, P.fieldSize_mul_fieldSize_lt_two64]
      rw [Nat.mod_eq_of_lt hprod]
      nlinarith [P.r2ModModulus_lt_fieldSize])
  change ((montgomeryReduceBoundedRaw (F := F)
      (UInt64.ofNat n * P.r2ModModulus.toUInt64)).toNat : ZMod P.fieldSize) =
        ((UInt64.ofNat n * P.r2ModModulus.toUInt64).toNat : ZMod P.fieldSize) *
          (UInt32.size : ZMod P.fieldSize)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F)
      (UInt64.ofNat n * P.r2ModModulus.toUInt64)).toNat : ZMod P.fieldSize) =
        (n : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  have hnmod : n % 2 ^ 64 = n := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans h (Nat.lt_trans P.fieldSize_lt_uint32Size (by decide))
  rw [hnmod]
  have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [P.r2ModModulus_lt_fieldSize, P.fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul, P.r2ModModulus_cast]
  rw [pow_two]
  rw [mul_assoc (n : ZMod P.fieldSize) ((UInt32.size : ZMod P.fieldSize) *
    (UInt32.size : ZMod P.fieldSize)) ((UInt32.size : ZMod P.fieldSize)⁻¹)]
  rw [mul_assoc (UInt32.size : ZMod P.fieldSize) (UInt32.size : ZMod P.fieldSize)
    ((UInt32.size : ZMod P.fieldSize)⁻¹)]
  rw [mul_inv_cancel₀ P.uint32Size_ne_zero_in_field]
  rw [mul_one]

theorem toField_ofCanonicalNat_aux (n : Nat) (h : n < P.fieldSize) :
    toField (ofCanonicalNat (F := F) n h) = (n : ZMod P.fieldSize) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.uint32Size_ne_zero_in_field]
  rw [mul_one]

theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 (F := F) x).val.toNat : ZMod P.fieldSize) =
      (x.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize) := by
  unfold reduceUInt64
  let y := x % P.modulus64
  have hred := montgomeryReduceBounded_cast (y * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : y.toNat < P.fieldSize := by
      rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.fieldSize_pos
    have hprod : y.toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, P.r2ModModulus_lt_fieldSize, P.fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_fieldSize])
  change ((montgomeryReduceBoundedRaw (F := F) (y * P.r2ModModulus.toUInt64)).toNat :
      ZMod P.fieldSize) =
        ((y * P.r2ModModulus.toUInt64).toNat : ZMod P.fieldSize) *
          (UInt32.size : ZMod P.fieldSize)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F) (y * P.r2ModModulus.toUInt64)).toNat :
      ZMod P.fieldSize) =
        (x.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hy_lt : y.toNat < P.fieldSize := by
    rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
    exact Nat.mod_lt _ P.fieldSize_pos
  have hprod : y.toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [hy_lt, P.r2ModModulus_lt_fieldSize, P.fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  have hy_cast : (y.toNat : ZMod P.fieldSize) = (x.toNat : ZMod P.fieldSize) := by
    rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_modEq _ _
  rw [Nat.cast_mul, P.r2ModModulus_cast, hy_cast]
  rw [pow_two]
  rw [mul_assoc (x.toNat : ZMod P.fieldSize) ((UInt32.size : ZMod P.fieldSize) *
    (UInt32.size : ZMod P.fieldSize)) ((UInt32.size : ZMod P.fieldSize)⁻¹)]
  rw [mul_assoc (UInt32.size : ZMod P.fieldSize) (UInt32.size : ZMod P.fieldSize)
    ((UInt32.size : ZMod P.fieldSize)⁻¹)]
  rw [mul_inv_cancel₀ P.uint32Size_ne_zero_in_field]
  rw [mul_one]

@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < P.fieldSize) :
    toNat (ofCanonicalNat (F := F) n h) = n :=
  nat_eq_of_field_eq (toNat_lt_fieldSize _) h (toField_ofCanonicalNat_aux n h)

@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < P.fieldSize) :
    toField (ofCanonicalNat (F := F) n h) = (n : ZMod P.fieldSize) :=
  toField_ofCanonicalNat_aux n h

@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 (F := F) x) = x.toNat % P.fieldSize := by
  apply nat_eq_of_field_eq (toNat_lt_fieldSize _) (Nat.mod_lt _ P.fieldSize_pos)
  change toField (reduceUInt64 (F := F) x) = ((x.toNat % P.fieldSize : Nat) : ZMod P.fieldSize)
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.uint32Size_ne_zero_in_field]
  rw [mul_one]
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq _ _).symm

@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 (F := F) x) = (x.toNat : ZMod P.fieldSize) := by
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.uint32Size_ne_zero_in_field]
  rw [mul_one]

/-! ## Field operations -/

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : FastField F) : FastField F :=
  reduceUInt32Lt2Modulus (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by
      have := x.property; have := y.property; omega))

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : FastField F) : FastField F :=
  if hx : x.val = 0 then
    zero
  else
    ⟨P.modulus - x.val, by
      have hle : x.val ≤ P.modulus := by
        rw [UInt32.le_iff_toNat_le, P.modulus_toNat]
        exact Nat.le_of_lt x.property
      rw [UInt32.toNat_sub_of_le _ _ hle, P.modulus_toNat]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt32.toNat_inj.mp
        simpa using hzero
      have hp := P.fieldSize_pos
      omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : FastField F) : FastField F :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt32.toNat_sub_of_le _ _ hyx]
      have := x.property; omega⟩
  else
    ⟨x.val + P.modulus - y.val, by
      have hsum_lt : x.val.toNat + P.fieldSize < UInt32.size := by
        have htwo := P.fieldSize_add_fieldSize_lt_uint32Size
        have := x.property; omega
      have hsum_eq : (x.val + P.modulus).toNat = x.val.toNat + P.fieldSize := by
        rw [UInt32.toNat_add, P.modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
      have hyle : y.val ≤ x.val + P.modulus := by
        rw [UInt32.le_iff_toNat_le, hsum_eq]
        have := y.property; omega
      rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
      have hyxNat : ¬y.val.toNat ≤ x.val.toNat := by
        intro hle
        apply hyx
        rw [UInt32.le_iff_toNat_le]
        exact hle
      have := y.property; omega⟩

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : FastField F) : FastField F :=
  montgomeryReduceBounded (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, P.fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.fieldSize_lt_uint32Size, P.fieldSize_pos])

/-- Fast squaring. -/
@[inline]
def square (x : FastField F) : FastField F :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[specialize]
def pow (x : FastField F) (n : Nat) : FastField F :=
  @npowBinRec (FastField F) ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the prime field. -/
def invExponent : Nat := P.fieldSize - 2

/-- Inversion in Montgomery form via Fermat's little theorem (`x⁻¹ = x^(p-2)`),
by binary exponentiation (`pow`). -/
@[inline]
def inv (x : FastField F) : FastField F :=
  pow x (invExponent (F := F))

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : FastField F) : FastField F :=
  mul x (inv y)

instance instZero : Zero (FastField F) where
  zero := zero

instance instOne : One (FastField F) where
  one := one

instance instAdd : Add (FastField F) where
  add := add

instance instNeg : Neg (FastField F) where
  neg := neg

instance instSub : Sub (FastField F) where
  sub := sub

instance instMul : Mul (FastField F) where
  mul := mul

instance instInv : Inv (FastField F) where
  inv := inv

instance instDiv : Div (FastField F) where
  div := div

instance instNatCast : NatCast (FastField F) where
  natCast := ofNat

instance instIntCast : IntCast (FastField F) where
  intCast := ofInt

instance instNatSMul : SMul Nat (FastField F) where
  smul n x := ofNat n * x

instance instIntSMul : SMul Int (FastField F) where
  smul n x := ofInt n * x

instance instPowNat : Pow (FastField F) Nat where
  pow := pow

instance instPowInt : Pow (FastField F) Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance instNNRatCast : NNRatCast (FastField F) where
  nnratCast q := ofField (q : ZMod P.fieldSize)

instance instRatCast : RatCast (FastField F) where
  ratCast q := ofField (q : ZMod P.fieldSize)

instance instNNRatSMul : SMul ℚ≥0 (FastField F) where
  smul q x := ofField (q • toField x)

instance instRatSMul : SMul ℚ (FastField F) where
  smul q x := ofField (q • toField x)

/-- Fermat-style inversion in `ZMod fieldSize`. -/
theorem inv_eq_pow_field (a : ZMod P.fieldSize) (ha : a ≠ 0) :
    a⁻¹ = a ^ (P.fieldSize - 2) := by
  have hcard : Fintype.card (ZMod P.fieldSize) = P.fieldSize := ZMod.card P.fieldSize
  have h1 : a ^ (P.fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (P.fieldSize - 2) = 1 := by
    rw [← pow_succ']; show a ^ (P.fieldSize - 2 + 1) = 1
    have : P.fieldSize - 2 + 1 = P.fieldSize - 1 := by
      have := P.two_lt_fieldSize; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod P.fieldSize) : toField (ofField (F := F) x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : FastField F) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  apply nat_eq_of_field_eq (F := F)
  · exact (ofField (toField x)).property
  · exact x.property
  · rw [raw_cast_eq_toField_mul]
    rw [toField_ofField]
    rw [raw_cast_eq_toField_mul]

/-- The canonical-field interpretation distinguishes fast values. -/
theorem toField_injective : Function.Injective (toField (F := F)) :=
  Function.LeftInverse.injective ofField_toField

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : FastField F) = 0 := by
  rw [toField_eq_raw_mul_inv]
  change ((0 : Nat) : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ = 0
  rw [Nat.cast_zero, zero_mul]

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : FastField F) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (P.rModModulus.toNat : ZMod P.fieldSize) *
      (UInt32.size : ZMod P.fieldSize)⁻¹ = 1
  rw [P.rModModulus_cast]
  exact mul_inv_cancel₀ P.uint32Size_ne_zero_in_field

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : FastField F) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instAdd add
  have hred := reduceUInt32Lt2Modulus_cast (F := F) (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by
      have hx := x.property; have hy := y.property; omega))
  change ((reduceUInt32Lt2ModulusRaw (F := F) (x.val + y.val)).toNat : ZMod P.fieldSize) =
      ((x.val + y.val).toNat : ZMod P.fieldSize) at hred
  change ((reduceUInt32Lt2ModulusRaw (F := F) (x.val + y.val)).toNat : ZMod P.fieldSize) *
      (UInt32.size : ZMod P.fieldSize)⁻¹ =
        (x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ +
          (y.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
  rw [hred]
  rw [UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < UInt32.size := by
    nlinarith [x.property, y.property, P.fieldSize_add_fieldSize_lt_uint32Size]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.cast_add]
  ring

/-- Fast subtraction agrees with subtraction in the canonical field. -/
@[simp]
theorem toField_sub (x y : FastField F) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hsubval : (x - y : FastField F).val = x.val - y.val := by
      change (sub x y).val = x.val - y.val
      unfold sub
      rw [dif_pos hyx]
    rw [hsubval]
    change (((x.val - y.val).toNat : ZMod P.fieldSize) *
        (UInt32.size : ZMod P.fieldSize)⁻¹) =
        (x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ -
          (y.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyx]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hyx
      exact hyx)]
    ring
  · have hsum_lt : x.val.toNat + P.fieldSize < UInt32.size := by
      have htwo := P.fieldSize_add_fieldSize_lt_uint32Size
      have := x.property; omega
    have hsum_eq : (x.val + P.modulus).toNat = x.val.toNat + P.fieldSize := by
      rw [UInt32.toNat_add, P.modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hyle : y.val ≤ x.val + P.modulus := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      have := y.property; omega
    have hsubval : (x - y : FastField F).val = x.val + P.modulus - y.val := by
      change (sub x y).val = x.val + P.modulus - y.val
      unfold sub
      rw [dif_neg hyx]
    rw [hsubval]
    change (((x.val + P.modulus - y.val).toNat : ZMod P.fieldSize) *
        (UInt32.size : ZMod P.fieldSize)⁻¹) =
        (x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ -
          (y.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, hsum_eq] at hyle
      exact hyle)]
    rw [Nat.cast_add, ZMod.natCast_self]
    ring

/-- Fast negation agrees with negation in the canonical field. -/
@[simp]
theorem toField_neg (x : FastField F) : toField (-x) = -toField x := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegval : (-x : FastField F).val = (zero : FastField F).val := by
      change (neg x).val = (zero : FastField F).val
      unfold neg
      rw [dif_pos hx]
    rw [hnegval]
    change ((zero : FastField F).val.toNat : ZMod P.fieldSize) *
        (UInt32.size : ZMod P.fieldSize)⁻¹ =
        -((x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹)
    have hxNat : x.val.toNat = 0 := by
      simpa using congrArg UInt32.toNat hx
    rw [hxNat]
    change ((0 : Nat) : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ =
      -(((0 : Nat) : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹)
    simp
  · have hle : x.val ≤ P.modulus := by
      rw [UInt32.le_iff_toNat_le, P.modulus_toNat]
      exact Nat.le_of_lt x.property
    have hnegval : (-x : FastField F).val = P.modulus - x.val := by
      change (neg x).val = P.modulus - x.val
      unfold neg
      rw [dif_neg hx]
    rw [hnegval]
    change (((P.modulus - x.val).toNat : ZMod P.fieldSize) *
        (UInt32.size : ZMod P.fieldSize)⁻¹) =
        -((x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹)
    rw [UInt32.toNat_sub_of_le _ _ hle, P.modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, P.modulus_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    ring

/-- Fast multiplication agrees with multiplication in the canonical field. -/
@[simp]
theorem toField_mul (x y : FastField F) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instMul mul
  have hred := montgomeryReduceBounded_cast (F := F) (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, P.fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.fieldSize_lt_uint32Size, P.fieldSize_pos])
  change ((montgomeryReduceBoundedRaw (F := F) (x.val.toUInt64 * y.val.toUInt64)).toNat :
      ZMod P.fieldSize) =
        ((x.val.toUInt64 * y.val.toUInt64).toNat : ZMod P.fieldSize) *
          (UInt32.size : ZMod P.fieldSize)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F) (x.val.toUInt64 * y.val.toUInt64)).toNat :
      ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ =
        (x.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹ *
          ((y.val.toNat : ZMod P.fieldSize) * (UInt32.size : ZMod P.fieldSize)⁻¹)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, P.fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul]
  ring

/-- Ring equivalence between the fast Montgomery representation and the canonical field. -/
def ringEquiv : FastField F ≃+* ZMod P.fieldSize where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp]
theorem ringEquiv_apply (x : FastField F) : ringEquiv x = toField x := rfl

@[simp]
theorem ringEquiv_symm_apply (x : ZMod P.fieldSize) :
    (ringEquiv (F := F)).symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : FastField F) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : FastField F) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup (FastField F) := {
    mul := (· * ·)
    mul_assoc := mul_assoc_field
  }
  exact npowBinRec_succ n x

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : FastField F) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

/-- Fast natural-power computation agrees with powers in the canonical field. -/
@[simp]
theorem toField_pow (x : FastField F) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero]
      rw [toField_one]
      simp
  | succ n ih =>
      rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

private theorem toField_inv_pow (x : FastField F) :
    toField (inv x) = toField x ^ (invExponent (F := F)) := by
  unfold inv
  exact toField_pow x (invExponent (F := F))

private theorem toField_inv_raw (x : FastField F) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero]
    exact zero_pow (by unfold invExponent; have := P.two_lt_fieldSize; omega)
  · simpa [invExponent] using (inv_eq_pow_field (toField x) hx).symm

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : FastField F) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_mul_raw (x y : FastField F) :
    toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

private theorem toField_div_mul_inv (x y : FastField F) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  exact toField_mul_raw x (inv y)

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : FastField F) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : ZMod P.fieldSize, c = b⁻¹ → a * c = a / b := by
    intro a b c hc
    rw [hc]
    rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : FastField F) = (n : ZMod P.fieldSize) := by
  change toField (ofNat n) = (n : ZMod P.fieldSize)
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : FastField F) = (n : ZMod P.fieldSize) := by
  change toField (ofInt n) = (n : ZMod P.fieldSize)
  unfold ofInt
  rw [toField_ofField]

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : FastField F) : toField (n • x) = n • toField x := by
  change toField ((n : FastField F) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : FastField F) : toField (n • x) = n • toField x := by
  change toField ((n : FastField F) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : FastField F) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : FastField F) (n : Int) : toField (x ^ n) = toField x ^ n := by
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

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : FastField F) = (q : ZMod P.fieldSize) := by
  change toField (ofField (q : ZMod P.fieldSize)) = (q : ZMod P.fieldSize)
  rw [toField_ofField]

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : FastField F) = (q : ZMod P.fieldSize) := by
  change toField (ofField (q : ZMod P.fieldSize)) = (q : ZMod P.fieldSize)
  rw [toField_ofField]

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : FastField F) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : FastField F) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Field instance transferred from the canonical field through `toField`. -/
instance (priority := low) instField : _root_.Field (FastField F) :=
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
instance (priority := low) instCommRing : CommRing (FastField F) := by
  infer_instance

/-- A fast 32-bit-word field is non-binary. -/
instance (priority := low) instNonBinaryField : NonBinaryField (FastField F) where
  char_neq_2 := by
    change ((2 : Nat) : FastField F) ≠ 0
    intro h
    exact P.two_ne_zero_in_field (by
      calc
        (2 : ZMod P.fieldSize) = ((2 : Nat) : ZMod P.fieldSize) := by norm_cast
        _ = toField ((2 : Nat) : FastField F) := (toField_natCast 2).symm
        _ = toField (0 : FastField F) := congrArg toField h
        _ = 0 := toField_zero)

end

end Native32
end Montgomery
