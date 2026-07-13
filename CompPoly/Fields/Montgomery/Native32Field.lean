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

* `Mont32Field F` bundles the prime (`modulus`), its native-word forms, the Montgomery
  constants, and the small `decide`-checkable numeric/`ZMod` facts the proofs consume.
  Everything except the five word constants is spec-level and erased at codegen.
* `FastField F` is the fast carrier `{ x : UInt32 // x.toNat < modulus }`, indexed by the
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

The five word constants (`modulus32`, `modulus64`, `rModModulus`, `r2ModModulus`,
`montgomeryNegInv`) are the only runtime data; the remaining fields are `Prop`s and
erased at codegen. -/
class Mont32Field (F : Type) where
  /-- The prime modulus `p`. -/
  modulus : ℕ
  /-- `modulus` is prime — needed to reduce into `ZMod modulus` as a field. -/
  prime : Fact (Nat.Prime modulus)
  /-- `modulus` as a 32-bit word. -/
  modulus32 : UInt32
  /-- `modulus` as a 64-bit word. -/
  modulus64 : UInt64
  /-- `2^32 mod modulus`, the Montgomery representation of one. -/
  rModModulus : UInt32
  /-- `(2^32)^2 mod modulus`, used to enter Montgomery form. -/
  r2ModModulus : UInt32
  /-- `-modulus⁻¹ mod 2^32`, used by Montgomery reduction. -/
  montgomeryNegInv : UInt32
  modulus32_toNat : modulus32.toNat = modulus
  modulus64_toNat : modulus64.toNat = modulus
  two_mul_modulus_lt_two_pow_32 : 2 * modulus < 2 ^ 32
  two_pow_32_lt_three_mul_modulus : 2 ^ 32 < 3 * modulus
  rModModulus_toNat : rModModulus.toNat = 2 ^ 32 % modulus
  r2ModModulus_toNat : r2ModModulus.toNat = (2 ^ 32) ^ 2 % modulus
  montgomeryNegInv_mul_modulus_mod_two_pow_32 :
    (montgomeryNegInv.toNat * modulus) % 2 ^ 32 = 2 ^ 32 - 1

attribute [instance] Mont32Field.prime

namespace Mont32Field

theorem two_lt_modulus {F : Type} [P : Mont32Field F] : 2 < P.modulus := by
  have h := P.two_pow_32_lt_three_mul_modulus
  omega

theorem modulus_pos {F : Type} [P : Mont32Field F] : 0 < P.modulus := by
  exact Nat.zero_lt_of_lt P.two_lt_modulus

theorem modulus_lt_two_pow_32 {F : Type} [P : Mont32Field F] :
    P.modulus < 2 ^ 32 := by
  have h := P.two_mul_modulus_lt_two_pow_32
  omega

theorem modulus_sq_lt_two_pow_64 {F : Type} [P : Mont32Field F] :
    P.modulus ^ 2 < 2 ^ 64 := by
  nlinarith [P.modulus_lt_two_pow_32]

theorem two_pow_32_ne_zero_in_field {F : Type} [P : Mont32Field F] :
    ((2 ^ 32 : ℕ) : ZMod P.modulus) ≠ 0 := by
  have htwo : (2 : ZMod P.modulus) ≠ 0 := by
    intro h
    have hdvd : P.modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 P.modulus).mp h
    exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)
  rw [Nat.cast_pow]
  exact pow_ne_zero 32 htwo

theorem rModModulus_lt_modulus {F : Type} [P : Mont32Field F] :
    P.rModModulus.toNat < P.modulus := by
  rw [P.rModModulus_toNat]
  exact Nat.mod_lt _ P.modulus_pos

theorem r2ModModulus_lt_modulus {F : Type} [P : Mont32Field F] :
    P.r2ModModulus.toNat < P.modulus := by
  rw [P.r2ModModulus_toNat]
  exact Nat.mod_lt _ P.modulus_pos

theorem rModModulus_cast {F : Type} [P : Mont32Field F] :
    (P.rModModulus.toNat : ZMod P.modulus) = ((2 ^ 32 : ℕ) : ZMod P.modulus) := by
  rw [P.rModModulus_toNat, ZMod.natCast_mod]

theorem r2ModModulus_cast {F : Type} [P : Mont32Field F] :
    (P.r2ModModulus.toNat : ZMod P.modulus) = ((2 ^ 32 : ℕ) : ZMod P.modulus) ^ 2 := by
  rw [P.r2ModModulus_toNat, ZMod.natCast_mod, Nat.cast_pow]

end Mont32Field

/-- The fast carrier for the field tagged by `F`: a native word below `modulus`,
interpreted as a Montgomery residue. At runtime this erases to `UInt32`. -/
def FastField (F : Type) [Mont32Field F] : Type :=
  { x : UInt32 // x.toNat < Mont32Field.modulus F }

instance (F : Type) [Mont32Field F] : DecidableEq (FastField F) :=
  inferInstanceAs (DecidableEq { x : UInt32 // x.toNat < Mont32Field.modulus F })

section
variable {F : Type} [P : Mont32Field F]

instance : NeZero P.modulus := ⟨P.modulus_pos.ne'⟩

/-- The raw Montgomery word backing a fast element. -/
@[inline]
def raw (x : FastField F) : UInt32 := x.val

/-! ## Montgomery reduction -/

/-- Reduce a native word known to be below twice the prime. -/
@[inline]
def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  if x < P.modulus32 then x else x - P.modulus32

theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * P.modulus) :
    (reduceUInt32Lt2ModulusRaw (F := F) x).toNat < P.modulus := by
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < P.modulus32
  · rw [if_pos hx]
    rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hx
    exact hx
  · rw [if_neg hx]
    have hmod_le_x : P.modulus32 ≤ x := by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
      rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, P.modulus32_toNat]
    omega

/-- Reduce a native word known to be below twice the prime. -/
@[inline]
def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * P.modulus) :
    FastField F :=
  ⟨reduceUInt32Lt2ModulusRaw (F := F) x, reduceUInt32Lt2ModulusRaw_lt x h⟩

theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * P.modulus) :
    ((reduceUInt32Lt2Modulus (F := F) x h).val.toNat : ZMod P.modulus) =
      (x.toNat : ZMod P.modulus) := by
  change ((reduceUInt32Lt2ModulusRaw (F := F) x).toNat : ZMod P.modulus) =
    (x.toNat : ZMod P.modulus)
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < P.modulus32
  · rw [if_pos hx]
  · have hmod_le_x : P.modulus32 ≤ x := by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
      rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hx
      exact Nat.le_of_not_gt hx
    rw [if_neg hx]
    rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, P.modulus32_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat] at hmod_le_x
      exact hmod_le_x)]
    simp

/-- Reduce a native word below `2^32` modulo the prime. -/
@[inline]
def reduceUInt32 (x : UInt32) : FastField F :=
  if hx : x < P.modulus32 then
    ⟨x, by
      rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hx
      exact hx⟩
  else
    let y := x - P.modulus32
    if hy : y < P.modulus32 then
      ⟨y, by
        rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hy
        exact hy⟩
    else
      ⟨y - P.modulus32, by
        have hmod_le_x : P.modulus32 ≤ x := by
          rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
          rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hx
          exact Nat.le_of_not_gt hx
        have hy_eq : y.toNat = x.toNat - P.modulus := by
          change (x - P.modulus32).toNat = x.toNat - P.modulus
          rw [UInt32.toNat_sub_of_le _ _ hmod_le_x, P.modulus32_toNat]
        have hmod_le_y : P.modulus32 ≤ y := by
          rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
          rw [UInt32.lt_iff_toNat_lt, P.modulus32_toNat] at hy
          exact Nat.le_of_not_gt hy
        rw [UInt32.toNat_sub_of_le _ _ hmod_le_y, P.modulus32_toNat, hy_eq]
        have hx_lt := UInt32.toNat_lt_size x
        change x.toNat < 2 ^ 32 at hx_lt
        have hthree := P.two_pow_32_lt_three_mul_modulus
        omega⟩

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBoundedRaw (x : UInt64) : UInt32 :=
  reduceUInt32Lt2ModulusRaw (F := F)
    (Montgomery.Native32.reduceQuotient P.montgomeryNegInv P.modulus64 x)

theorem montgomeryReduceBoundedRaw_lt (x : UInt64)
    (h : x.toNat < P.modulus * 2 ^ 32) :
    (montgomeryReduceBoundedRaw (F := F) x).toNat < P.modulus := by
  have hmodulus_bound : P.modulus64.toNat < 2 ^ 31 := by
    rw [P.modulus64_toNat]
    have hp := P.two_mul_modulus_lt_two_pow_32
    omega
  unfold montgomeryReduceBoundedRaw
  exact reduceUInt32Lt2ModulusRaw_lt _
    (by
      simpa only [P.modulus64_toNat] using
        Montgomery.Native32.reduceQuotient_toNat_lt_two_mul P.montgomeryNegInv P.modulus64
          (by simpa only [P.modulus64_toNat] using P.modulus_pos)
          hmodulus_bound
          x (by simpa only [P.modulus64_toNat] using h))

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBounded (x : UInt64)
    (h : x.toNat < P.modulus * 2 ^ 32) : FastField F :=
  ⟨montgomeryReduceBoundedRaw (F := F) x, montgomeryReduceBoundedRaw_lt x h⟩

theorem montgomeryReduceBounded_cast (x : UInt64)
    (h : x.toNat < P.modulus * 2 ^ 32) :
    ((montgomeryReduceBounded (F := F) x h).val.toNat : ZMod P.modulus) =
      (x.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ := by
  have hmodulus_bound : P.modulus64.toNat < 2 ^ 31 := by
    rw [P.modulus64_toNat]
    have hp := P.two_mul_modulus_lt_two_pow_32
    omega
  change ((montgomeryReduceBoundedRaw (F := F) x).toNat : ZMod P.modulus) =
      (x.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
  unfold montgomeryReduceBoundedRaw
  let u := Montgomery.Native32.reduceQuotient P.montgomeryNegInv P.modulus64 x
  change ((reduceUInt32Lt2ModulusRaw (F := F) u).toNat : ZMod P.modulus) =
    (x.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
  have hred := reduceUInt32Lt2Modulus_cast (F := F) u
    (by
      simpa only [P.modulus64_toNat] using
        Montgomery.Native32.reduceQuotient_toNat_lt_two_mul P.montgomeryNegInv P.modulus64
          (by simpa only [P.modulus64_toNat] using P.modulus_pos)
          hmodulus_bound
          x (by simpa only [P.modulus64_toNat] using h))
  change ((reduceUInt32Lt2ModulusRaw (F := F) u).toNat : ZMod P.modulus) =
    (u.toNat : ZMod P.modulus) at hred
  rw [hred]
  change (u.toNat : ZMod P.modulus) =
    (x.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
  rw [show u.toNat = reduceNatQuotient (2 ^ 32) P.modulus P.montgomeryNegInv.toNat x.toNat by
    simpa only [u, P.modulus64_toNat] using
      Montgomery.Native32.reduceQuotient_toNat P.montgomeryNegInv P.modulus64
        (by simpa only [P.modulus64_toNat] using P.modulus_pos)
        hmodulus_bound
        x (by simpa only [P.modulus64_toNat] using h)]
  exact Montgomery.reduceNatQuotient_cast (2 ^ 32) P.modulus P.montgomeryNegInv.toNat
    (by decide) P.montgomeryNegInv_mul_modulus_mod_two_pow_32
    P.two_pow_32_ne_zero_in_field x.toNat

/-- Montgomery reduction of a 64-bit word. Hot bounded callers use `montgomeryReduceBounded`. -/
@[inline]
def montgomeryReduce (x : UInt64) : FastField F :=
  let u := Montgomery.Native32.reduceQuotient P.montgomeryNegInv P.modulus64 x
  reduceUInt32 (F := F) u

/-! ## Conversions -/

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : ℕ) (_h : n < P.modulus) : FastField F :=
  montgomeryReduceBounded (UInt64.ofNat n * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
    have hnmod : n % 2 ^ 64 = n := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans _h (Nat.lt_trans P.modulus_lt_two_pow_32 (by decide))
    rw [hnmod]
    have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_modulus])

/-- Reduce a `UInt64` modulo the prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : FastField F :=
  let y := x % P.modulus64
  montgomeryReduceBounded (y * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : (x % P.modulus64).toNat < P.modulus := by
      rw [UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.modulus_pos
    have hprod : (x % P.modulus64).toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_modulus])

/-- The zero fast element. -/
def zero : FastField F := ⟨0, by
  have h0 : (0 : UInt32).toNat = 0 := by decide
  have hp := P.modulus_pos
  omega⟩

/-- The one fast element. -/
def one : FastField F := ⟨P.rModModulus, P.rModModulus_lt_modulus⟩

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (n : ℕ) : FastField F :=
  ofCanonicalNat (n % P.modulus) (Nat.mod_lt _ P.modulus_pos)

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : FastField F :=
  reduceUInt64 x.toUInt64

/-- Convert from the canonical `ZMod` field into fast Montgomery form. -/
@[inline]
def ofField (x : ZMod P.modulus) : FastField F :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (n : Int) : FastField F :=
  ofField (n : ZMod P.modulus)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : FastField F) : UInt32 :=
  raw (montgomeryReduceBounded x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos]))

/-- Convert a fast element to its canonical natural representative. -/
@[inline]
def toNat (x : FastField F) : ℕ :=
  (toCanonicalUInt32 x).toNat

/-- Convert a fast element to the canonical `ZMod` field. -/
@[inline]
def toField (x : FastField F) : ZMod P.modulus :=
  (toNat x : ZMod P.modulus)

theorem toNat_lt_modulus (x : FastField F) : toNat x < P.modulus := by
  unfold toNat toCanonicalUInt32 raw
  change (montgomeryReduceBoundedRaw (F := F) x.val.toUInt64).toNat < P.modulus
  exact montgomeryReduceBoundedRaw_lt x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos])

theorem toField_eq_raw_mul_inv (x : FastField F) :
    toField x =
      (x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ := by
  unfold toField toNat toCanonicalUInt32 raw
  have hred := montgomeryReduceBounded_cast x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos])
  change ((montgomeryReduceBoundedRaw (F := F) x.val.toUInt64).toNat : ZMod P.modulus) =
      (x.val.toUInt64.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F) x.val.toUInt64).toNat : ZMod P.modulus) =
      (x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
  rw [hred]
  rw [UInt32.toNat_toUInt64]

theorem raw_cast_eq_toField_mul (x : FastField F) :
    (x.val.toNat : ZMod P.modulus) =
      toField x * ((2 ^ 32 : ℕ) : ZMod P.modulus) := by
  rw [toField_eq_raw_mul_inv]
  rw [mul_assoc]
  rw [inv_mul_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

theorem nat_eq_of_field_eq {a b : ℕ} (ha : a < P.modulus)
    (hb : b < P.modulus) (h : (a : ZMod P.modulus) = (b : ZMod P.modulus)) :
    a = b :=
  Montgomery.natCast_inj_of_lt h ha hb

theorem ofCanonicalNat_raw_cast (n : ℕ) (h : n < P.modulus) :
    ((ofCanonicalNat (F := F) n h).val.toNat : ZMod P.modulus) =
      (n : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus) := by
  unfold ofCanonicalNat
  have hred := montgomeryReduceBounded_cast
    (UInt64.ofNat n * P.r2ModModulus.toUInt64) (by
      rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
      have hnmod : n % 2 ^ 64 = n := by
        apply Nat.mod_eq_of_lt
        exact Nat.lt_trans h (Nat.lt_trans P.modulus_lt_two_pow_32 (by decide))
      rw [hnmod]
      have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
        nlinarith [P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
      rw [Nat.mod_eq_of_lt hprod]
      nlinarith [P.r2ModModulus_lt_modulus])
  change ((montgomeryReduceBoundedRaw (F := F)
      (UInt64.ofNat n * P.r2ModModulus.toUInt64)).toNat : ZMod P.modulus) =
        ((UInt64.ofNat n * P.r2ModModulus.toUInt64).toNat : ZMod P.modulus) *
          ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F)
      (UInt64.ofNat n * P.r2ModModulus.toUInt64)).toNat : ZMod P.modulus) =
        (n : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  have hnmod : n % 2 ^ 64 = n := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans h (Nat.lt_trans P.modulus_lt_two_pow_32 (by decide))
  rw [hnmod]
  have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul, P.r2ModModulus_cast]
  rw [pow_two]
  rw [mul_assoc (n : ZMod P.modulus) (((2 ^ 32 : ℕ) : ZMod P.modulus) *
    ((2 ^ 32 : ℕ) : ZMod P.modulus)) (((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)]
  rw [mul_assoc ((2 ^ 32 : ℕ) : ZMod P.modulus) ((2 ^ 32 : ℕ) : ZMod P.modulus)
    (((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

theorem toField_ofCanonicalNat_aux (n : ℕ) (h : n < P.modulus) :
    toField (ofCanonicalNat (F := F) n h) = (n : ZMod P.modulus) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 (F := F) x).val.toNat : ZMod P.modulus) =
      (x.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus) := by
  unfold reduceUInt64
  let y := x % P.modulus64
  have hred := montgomeryReduceBounded_cast (y * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : y.toNat < P.modulus := by
      rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.modulus_pos
    have hprod : y.toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_modulus])
  change ((montgomeryReduceBoundedRaw (F := F) (y * P.r2ModModulus.toUInt64)).toNat :
      ZMod P.modulus) =
        ((y * P.r2ModModulus.toUInt64).toNat : ZMod P.modulus) *
          ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F) (y * P.r2ModModulus.toUInt64)).toNat :
      ZMod P.modulus) =
        (x.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hy_lt : y.toNat < P.modulus := by
    rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
    exact Nat.mod_lt _ P.modulus_pos
  have hprod : y.toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [hy_lt, P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  have hy_cast : (y.toNat : ZMod P.modulus) = (x.toNat : ZMod P.modulus) := by
    rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_modEq _ _
  rw [Nat.cast_mul, P.r2ModModulus_cast, hy_cast]
  rw [pow_two]
  rw [mul_assoc (x.toNat : ZMod P.modulus) (((2 ^ 32 : ℕ) : ZMod P.modulus) *
    ((2 ^ 32 : ℕ) : ZMod P.modulus)) (((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)]
  rw [mul_assoc ((2 ^ 32 : ℕ) : ZMod P.modulus) ((2 ^ 32 : ℕ) : ZMod P.modulus)
    (((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

@[simp]
theorem toNat_ofCanonicalNat (n : ℕ) (h : n < P.modulus) :
    toNat (ofCanonicalNat (F := F) n h) = n :=
  nat_eq_of_field_eq (toNat_lt_modulus _) h (toField_ofCanonicalNat_aux n h)

@[simp]
theorem toField_ofCanonicalNat (n : ℕ) (h : n < P.modulus) :
    toField (ofCanonicalNat (F := F) n h) = (n : ZMod P.modulus) :=
  toField_ofCanonicalNat_aux n h

@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 (F := F) x) = x.toNat % P.modulus := by
  apply nat_eq_of_field_eq (toNat_lt_modulus _) (Nat.mod_lt _ P.modulus_pos)
  change toField (reduceUInt64 (F := F) x) = ((x.toNat % P.modulus : ℕ) : ZMod P.modulus)
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq _ _).symm

@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 (F := F) x) = (x.toNat : ZMod P.modulus) := by
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
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
    ⟨P.modulus32 - x.val, by
      have hle : x.val ≤ P.modulus32 := by
        rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
        exact Nat.le_of_lt x.property
      rw [UInt32.toNat_sub_of_le _ _ hle, P.modulus32_toNat]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt32.toNat_inj.mp
        simpa using hzero
      have hp := P.modulus_pos
      omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : FastField F) : FastField F :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt32.toNat_sub_of_le _ _ hyx]
      have := x.property; omega⟩
  else
    ⟨x.val + P.modulus32 - y.val, by
      have hsum_lt : x.val.toNat + P.modulus < 2 ^ 32 := by
        have htwo := P.two_mul_modulus_lt_two_pow_32
        have := x.property; omega
      have hsum_eq : (x.val + P.modulus32).toNat = x.val.toNat + P.modulus := by
        rw [UInt32.toNat_add, P.modulus32_toNat, Nat.mod_eq_of_lt hsum_lt]
      have hyle : y.val ≤ x.val + P.modulus32 := by
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
      nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.modulus_lt_two_pow_32, P.modulus_pos])

/-- Fast squaring. -/
@[inline]
def square (x : FastField F) : FastField F :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[specialize]
def pow (x : FastField F) (n : ℕ) : FastField F :=
  @npowBinRec (FastField F) ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the prime field. -/
def invExponent : ℕ := P.modulus - 2

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

instance instNatSMul : SMul ℕ (FastField F) where
  smul n x := ofNat n * x

instance instIntSMul : SMul Int (FastField F) where
  smul n x := ofInt n * x

instance instPowNat : Pow (FastField F) ℕ where
  pow := pow

instance instPowInt : Pow (FastField F) Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance instNNRatCast : NNRatCast (FastField F) where
  nnratCast q := ofField (q : ZMod P.modulus)

instance instRatCast : RatCast (FastField F) where
  ratCast q := ofField (q : ZMod P.modulus)

instance instNNRatSMul : SMul ℚ≥0 (FastField F) where
  smul q x := ofField (q • toField x)

instance instRatSMul : SMul ℚ (FastField F) where
  smul q x := ofField (q • toField x)

/-- Fermat-style inversion in `ZMod modulus`. -/
theorem inv_eq_pow_field (a : ZMod P.modulus) (ha : a ≠ 0) :
    a⁻¹ = a ^ (P.modulus - 2) := by
  have hcard : Fintype.card (ZMod P.modulus) = P.modulus := ZMod.card P.modulus
  have h1 : a ^ (P.modulus - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (P.modulus - 2) = 1 := by
    rw [← pow_succ']; show a ^ (P.modulus - 2 + 1) = 1
    have : P.modulus - 2 + 1 = P.modulus - 1 := by
      have := P.two_lt_modulus; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod P.modulus) : toField (ofField (F := F) x) = x := by
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
  change ((0 : ℕ) : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ = 0
  rw [Nat.cast_zero, zero_mul]

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : FastField F) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (P.rModModulus.toNat : ZMod P.modulus) *
      ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ = 1
  rw [P.rModModulus_cast]
  exact mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : FastField F) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instAdd add
  have hred := reduceUInt32Lt2Modulus_cast (F := F) (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by
      have hx := x.property; have hy := y.property; omega))
  change ((reduceUInt32Lt2ModulusRaw (F := F) (x.val + y.val)).toNat : ZMod P.modulus) =
      ((x.val + y.val).toNat : ZMod P.modulus) at hred
  change ((reduceUInt32Lt2ModulusRaw (F := F) (x.val + y.val)).toNat : ZMod P.modulus) *
      ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ =
        (x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ +
          (y.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
  rw [hred]
  rw [UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < 2 ^ 32 := by
    nlinarith [x.property, y.property, P.two_mul_modulus_lt_two_pow_32]
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
    change (((x.val - y.val).toNat : ZMod P.modulus) *
        ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹) =
        (x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ -
          (y.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyx]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hyx
      exact hyx)]
    ring
  · have hsum_lt : x.val.toNat + P.modulus < 2 ^ 32 := by
      have htwo := P.two_mul_modulus_lt_two_pow_32
      have := x.property; omega
    have hsum_eq : (x.val + P.modulus32).toNat = x.val.toNat + P.modulus := by
      rw [UInt32.toNat_add, P.modulus32_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hyle : y.val ≤ x.val + P.modulus32 := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      have := y.property; omega
    have hsubval : (x - y : FastField F).val = x.val + P.modulus32 - y.val := by
      change (sub x y).val = x.val + P.modulus32 - y.val
      unfold sub
      rw [dif_neg hyx]
    rw [hsubval]
    change (((x.val + P.modulus32 - y.val).toNat : ZMod P.modulus) *
        ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹) =
        (x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ -
          (y.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹
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
    change ((zero : FastField F).val.toNat : ZMod P.modulus) *
        ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ =
        -((x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)
    have hxNat : x.val.toNat = 0 := by
      simpa using congrArg UInt32.toNat hx
    rw [hxNat]
    change ((0 : ℕ) : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ =
      -(((0 : ℕ) : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)
    simp
  · have hle : x.val ≤ P.modulus32 := by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
      exact Nat.le_of_lt x.property
    have hnegval : (-x : FastField F).val = P.modulus32 - x.val := by
      change (neg x).val = P.modulus32 - x.val
      unfold neg
      rw [dif_neg hx]
    rw [hnegval]
    change (((P.modulus32 - x.val).toNat : ZMod P.modulus) *
        ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹) =
        -((x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)
    rw [UInt32.toNat_sub_of_le _ _ hle, P.modulus32_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat] at hle
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
      nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.modulus_lt_two_pow_32, P.modulus_pos])
  change ((montgomeryReduceBoundedRaw (F := F) (x.val.toUInt64 * y.val.toUInt64)).toNat :
      ZMod P.modulus) =
        ((x.val.toUInt64 * y.val.toUInt64).toNat : ZMod P.modulus) *
          ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (F := F) (x.val.toUInt64 * y.val.toUInt64)).toNat :
      ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ =
        (x.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹ *
          ((y.val.toNat : ZMod P.modulus) * ((2 ^ 32 : ℕ) : ZMod P.modulus)⁻¹)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul]
  ring

/-- Ring equivalence between the fast Montgomery representation and the canonical field. -/
def ringEquiv : FastField F ≃+* ZMod P.modulus where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp]
theorem ringEquiv_apply (x : FastField F) : ringEquiv x = toField x := rfl

@[simp]
theorem ringEquiv_symm_apply (x : ZMod P.modulus) :
    (ringEquiv (F := F)).symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : FastField F) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : FastField F) (n : ℕ) : pow x (n + 1) = pow x n * x := by
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
theorem toField_pow (x : FastField F) (n : ℕ) : toField (pow x n) = toField x ^ n := by
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
    exact zero_pow (by unfold invExponent; have := P.two_lt_modulus; omega)
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
  have h : ∀ a b c : ZMod P.modulus, c = b⁻¹ → a * c = a / b := by
    intro a b c hc
    rw [hc]
    rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : ℕ) : toField (n : FastField F) = (n : ZMod P.modulus) := by
  change toField (ofNat n) = (n : ZMod P.modulus)
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : FastField F) = (n : ZMod P.modulus) := by
  change toField (ofInt n) = (n : ZMod P.modulus)
  unfold ofInt
  rw [toField_ofField]

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : ℕ) (x : FastField F) : toField (n • x) = n • toField x := by
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
theorem toField_npow (x : FastField F) (n : ℕ) : toField (x ^ n) = toField x ^ n := by
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
theorem toField_nnratCast (q : ℚ≥0) : toField (q : FastField F) = (q : ZMod P.modulus) := by
  change toField (ofField (q : ZMod P.modulus)) = (q : ZMod P.modulus)
  rw [toField_ofField]

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : FastField F) = (q : ZMod P.modulus) := by
  change toField (ofField (q : ZMod P.modulus)) = (q : ZMod P.modulus)
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
    change ((2 : ℕ) : FastField F) ≠ 0
    intro h
    have htwo : (2 : ZMod P.modulus) = 0 := by
      calc
        (2 : ZMod P.modulus) = ((2 : ℕ) : ZMod P.modulus) := by norm_cast
        _ = toField ((2 : ℕ) : FastField F) := (toField_natCast 2).symm
        _ = toField (0 : FastField F) := congrArg toField h
        _ = 0 := toField_zero
    have hdvd : P.modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 P.modulus).mp htwo
    exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)

end

end Native32
end Montgomery
