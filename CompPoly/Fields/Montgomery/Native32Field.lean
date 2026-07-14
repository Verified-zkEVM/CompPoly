/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.Montgomery.Native32
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# Fast 32-bit Montgomery Fields

The bounded carrier, conversions, arithmetic, and field instances built on `Native32` reduction.
-/

namespace Montgomery
namespace Native32

/-- Per-field data for a fast 32-bit Montgomery field. -/
class Mont32Field (modulus : ℕ) where
  /-- `modulus` is prime. -/
  prime : modulus.Prime
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
  modulus32_toNat : modulus32.toNat = modulus := by decide
  modulus64_toNat : modulus64.toNat = modulus := by decide
  two_lt_modulus : 2 < modulus := by decide
  two_mul_modulus_lt_two_pow_32 : 2 * modulus < 2 ^ 32 := by decide
  rModModulus_toNat : rModModulus.toNat = 2 ^ 32 % modulus := by decide
  r2ModModulus_toNat : r2ModModulus.toNat = (2 ^ 32) ^ 2 % modulus := by decide
  montgomeryNegInv_mul_modulus_mod_two_pow_32 :
    (montgomeryNegInv.toNat * modulus) % 2 ^ 32 = 2 ^ 32 - 1 := by decide

namespace Mont32Field

instance factPrime (modulus : ℕ) [P : Mont32Field modulus] : Fact (Nat.Prime modulus) :=
  ⟨P.prime⟩

theorem modulus_pos {modulus : ℕ} [P : Mont32Field modulus] : 0 < modulus := by
  exact Nat.zero_lt_of_lt P.two_lt_modulus

theorem modulus_lt_two_pow_32 {modulus : ℕ} [P : Mont32Field modulus] :
    modulus < 2 ^ 32 := by
  have h := P.two_mul_modulus_lt_two_pow_32
  omega

theorem modulus_sq_lt_two_pow_64 {modulus : ℕ} [P : Mont32Field modulus] :
    modulus ^ 2 < 2 ^ 64 := by
  nlinarith [P.modulus_lt_two_pow_32]

theorem two_pow_32_ne_zero_in_field {modulus : ℕ} [P : Mont32Field modulus] :
    ((2 ^ 32 : ℕ) : ZMod modulus) ≠ 0 := by
  have htwo : (2 : ZMod modulus) ≠ 0 := by
    intro h
    have hdvd : modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 modulus).mp h
    exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)
  rw [Nat.cast_pow]
  exact pow_ne_zero 32 htwo

theorem r2ModModulus_lt_modulus {modulus : ℕ} [P : Mont32Field modulus] :
    P.r2ModModulus.toNat < modulus := by
  rw [P.r2ModModulus_toNat]
  exact Nat.mod_lt _ P.modulus_pos

end Mont32Field

/-- The fast carrier for a prime modulus: a native word below `modulus`,
interpreted as a Montgomery residue. At runtime this erases to `UInt32`. -/
def FastField (modulus : ℕ) [Mont32Field modulus] : Type :=
  { x : UInt32 // x.toNat < modulus }

instance (modulus : ℕ) [Mont32Field modulus] : DecidableEq (FastField modulus) :=
  inferInstanceAs (DecidableEq { x : UInt32 // x.toNat < modulus })

section
variable {modulus : ℕ} [P : Mont32Field modulus]

instance : NeZero modulus := ⟨P.modulus_pos.ne'⟩

/-! ## Montgomery reduction -/

/-- Reduce a native word known to be below twice the prime. -/
@[inline]
def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * modulus) :
    FastField modulus :=
  ⟨conditionalSubtract P.modulus32 x, by
    simpa only [P.modulus32_toNat] using
      conditionalSubtract_lt (p32 := P.modulus32) (u := x) (by
        simpa only [P.modulus32_toNat] using h)⟩

theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * modulus) :
    ((reduceUInt32Lt2Modulus (modulus := modulus) x h).val.toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) := by
  change ((conditionalSubtract P.modulus32 x).toNat : ZMod modulus) =
    (x.toNat : ZMod modulus)
  have hraw := conditionalSubtract_cast (p32 := P.modulus32) (u := x)
  rw [P.modulus32_toNat] at hraw
  exact hraw

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduce (x : UInt64)
    (h : x.toNat < modulus * 2 ^ 32) : FastField modulus :=
  ⟨reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv x, by
    simpa only [P.modulus32_toNat] using
      reduceRaw_lt (p32 := P.modulus32) (p64 := P.modulus64)
        (negInv := P.montgomeryNegInv) (x := x)
        (by rw [P.modulus32_toNat, P.modulus64_toNat])
        (by simpa only [P.modulus64_toNat] using P.modulus_pos)
        (by
          rw [P.modulus64_toNat]
          have hp := P.two_mul_modulus_lt_two_pow_32
          omega)
        (by simpa only [P.modulus64_toNat] using h)⟩

theorem montgomeryReduce_cast (x : UInt64)
    (h : x.toNat < modulus * 2 ^ 32) :
    ((montgomeryReduce (modulus := modulus) x h).val.toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  exact reduceRaw_cast (modulus := modulus) (p32 := P.modulus32)
    (p64 := P.modulus64) (negInv := P.montgomeryNegInv) (x := x)
    P.modulus32_toNat P.modulus64_toNat P.modulus_pos
    (by
      have hp := P.two_mul_modulus_lt_two_pow_32
      omega)
    P.montgomeryNegInv_mul_modulus_mod_two_pow_32
    P.two_pow_32_ne_zero_in_field h

/-! ## Conversions -/

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : ℕ) (_h : n < modulus) : FastField modulus :=
  montgomeryReduce (UInt64.ofNat n * P.r2ModModulus.toUInt64) (by
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
def reduceUInt64 (modulus : ℕ) [P : Mont32Field modulus]
    (x : UInt64) : FastField modulus :=
  let y := x % P.modulus64
  montgomeryReduce (y * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : (x % P.modulus64).toNat < modulus := by
      rw [UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.modulus_pos
    have hprod : (x % P.modulus64).toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_modulus])

/-- The zero fast element. -/
private def zero (modulus : ℕ) [P : Mont32Field modulus] : FastField modulus := ⟨0, by
  have h0 : (0 : UInt32).toNat = 0 := by decide
  have hp := P.modulus_pos
  omega⟩

/-- The one fast element. -/
private def one (modulus : ℕ) [P : Mont32Field modulus] : FastField modulus := ⟨P.rModModulus, by
  rw [P.rModModulus_toNat]
  exact Nat.mod_lt _ P.modulus_pos⟩

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
private def ofNat (modulus : ℕ) [P : Mont32Field modulus] (n : ℕ) : FastField modulus :=
  ofCanonicalNat (n % modulus) (Nat.mod_lt _ P.modulus_pos)

namespace FastField

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (modulus : ℕ) [P : Mont32Field modulus]
    (x : UInt32) : FastField modulus :=
  reduceUInt64 modulus x.toUInt64
end FastField

/-- Convert from the canonical `ZMod` field into fast Montgomery form. -/
@[inline]
def ofField (x : ZMod modulus) : FastField modulus :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
private def ofInt (modulus : ℕ) [P : Mont32Field modulus] (n : Int) : FastField modulus :=
  ofField (n : ZMod modulus)

namespace FastField

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toUInt32 (x : FastField modulus) : UInt32 :=
  montgomeryReduce (modulus := modulus) x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos])
  |>.val

/-- Convert a fast element to its canonical natural representative. -/
@[inline]
def toNat (x : FastField modulus) : ℕ :=
  x.toUInt32.toNat

/-- Convert a fast element to the canonical `ZMod` field. -/
@[inline]
def toField (x : FastField modulus) : ZMod modulus :=
  (x.toNat : ZMod modulus)
end FastField

open FastField

theorem toNat_lt_modulus (x : FastField modulus) : toNat x < modulus := by
  unfold FastField.toNat FastField.toUInt32
  change (reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
    x.val.toUInt64).toNat < modulus
  exact (montgomeryReduce (modulus := modulus) x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos])).property

theorem toField_eq_raw_mul_inv (x : FastField modulus) :
    toField x =
      (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  unfold FastField.toField FastField.toNat FastField.toUInt32
  have hred := montgomeryReduce_cast (modulus := modulus) x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos])
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
    x.val.toUInt64).toNat : ZMod modulus) =
      (x.val.toUInt64.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ at hred
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
    x.val.toUInt64).toNat : ZMod modulus) =
      (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹
  rw [hred]
  rw [UInt32.toNat_toUInt64]

theorem raw_cast_eq_toField_mul (x : FastField modulus) :
    (x.val.toNat : ZMod modulus) =
      toField x * ((2 ^ 32 : ℕ) : ZMod modulus) := by
  rw [toField_eq_raw_mul_inv]
  rw [mul_assoc]
  rw [inv_mul_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

theorem nat_eq_of_field_eq {a b : ℕ} (ha : a < modulus)
    (hb : b < modulus) (h : (a : ZMod modulus) = (b : ZMod modulus)) :
    a = b :=
  natCast_inj_of_lt h ha hb

theorem ofCanonicalNat_raw_cast (n : ℕ) (h : n < modulus) :
    ((ofCanonicalNat (modulus := modulus) n h).val.toNat : ZMod modulus) =
      (n : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus) := by
  unfold ofCanonicalNat
  have hred := montgomeryReduce_cast (modulus := modulus)
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
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
      (UInt64.ofNat n * P.r2ModModulus.toUInt64)).toNat : ZMod modulus) =
        ((UInt64.ofNat n * P.r2ModModulus.toUInt64).toNat : ZMod modulus) *
          ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ at hred
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
      (UInt64.ofNat n * P.r2ModModulus.toUInt64)).toNat : ZMod modulus) =
        (n : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  have hnmod : n % 2 ^ 64 = n := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans h (Nat.lt_trans P.modulus_lt_two_pow_32 (by decide))
  rw [hnmod]
  have hprod : n * P.r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul, P.r2ModModulus_toNat, ZMod.natCast_mod, Nat.cast_pow]
  rw [pow_two]
  rw [mul_assoc (n : ZMod modulus) (((2 ^ 32 : ℕ) : ZMod modulus) *
    ((2 ^ 32 : ℕ) : ZMod modulus)) (((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)]
  rw [mul_assoc ((2 ^ 32 : ℕ) : ZMod modulus) ((2 ^ 32 : ℕ) : ZMod modulus)
    (((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

theorem toField_ofCanonicalNat_aux (n : ℕ) (h : n < modulus) :
    toField (ofCanonicalNat (modulus := modulus) n h) = (n : ZMod modulus) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 modulus x).val.toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus) := by
  unfold reduceUInt64
  let y := x % P.modulus64
  have hred := montgomeryReduce_cast (modulus := modulus)
    (y * P.r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : y.toNat < modulus := by
      rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
      exact Nat.mod_lt _ P.modulus_pos
    have hprod : y.toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [P.r2ModModulus_lt_modulus])
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
      (y * P.r2ModModulus.toUInt64)).toNat :
      ZMod modulus) =
        ((y * P.r2ModModulus.toUInt64).toNat : ZMod modulus) *
          ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ at hred
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
      (y * P.r2ModModulus.toUInt64)).toNat :
      ZMod modulus) =
        (x.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hy_lt : y.toNat < modulus := by
    rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
    exact Nat.mod_lt _ P.modulus_pos
  have hprod : y.toNat * P.r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [hy_lt, P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  have hy_cast : (y.toNat : ZMod modulus) = (x.toNat : ZMod modulus) := by
    rw [show y = x % P.modulus64 by rfl, UInt64.toNat_mod, P.modulus64_toNat]
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_modEq _ _
  rw [Nat.cast_mul, P.r2ModModulus_toNat, ZMod.natCast_mod, Nat.cast_pow, hy_cast]
  rw [pow_two]
  rw [mul_assoc (x.toNat : ZMod modulus) (((2 ^ 32 : ℕ) : ZMod modulus) *
    ((2 ^ 32 : ℕ) : ZMod modulus)) (((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)]
  rw [mul_assoc ((2 ^ 32 : ℕ) : ZMod modulus) ((2 ^ 32 : ℕ) : ZMod modulus)
    (((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

@[simp]
theorem toNat_ofCanonicalNat (n : ℕ) (h : n < modulus) :
    toNat (ofCanonicalNat (modulus := modulus) n h) = n :=
  nat_eq_of_field_eq (toNat_lt_modulus _) h (toField_ofCanonicalNat_aux n h)

@[simp]
theorem toField_ofCanonicalNat (n : ℕ) (h : n < modulus) :
    toField (ofCanonicalNat (modulus := modulus) n h) = (n : ZMod modulus) :=
  toField_ofCanonicalNat_aux n h

@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 modulus x) = x.toNat % modulus := by
  apply nat_eq_of_field_eq (toNat_lt_modulus _) (Nat.mod_lt _ P.modulus_pos)
  change toField (reduceUInt64 modulus x) = ((x.toNat % modulus : ℕ) : ZMod modulus)
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq _ _).symm

@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 modulus x) = (x.toNat : ZMod modulus) := by
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field]
  rw [mul_one]

/-! ## Field operations -/

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : FastField modulus) : FastField modulus :=
  reduceUInt32Lt2Modulus (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by
      have := x.property; have := y.property; omega))

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : FastField modulus) : FastField modulus :=
  if hx : x.val = 0 then
    zero modulus
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
def sub (x y : FastField modulus) : FastField modulus :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt32.toNat_sub_of_le _ _ hyx]
      have := x.property; omega⟩
  else
    ⟨x.val + P.modulus32 - y.val, by
      have hsum_lt : x.val.toNat + modulus < 2 ^ 32 := by
        have htwo := P.two_mul_modulus_lt_two_pow_32
        have := x.property; omega
      have hsum_eq : (x.val + P.modulus32).toNat = x.val.toNat + modulus := by
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
def mul (x y : FastField modulus) : FastField modulus :=
  montgomeryReduce (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.modulus_lt_two_pow_32, P.modulus_pos])

/-- Fast squaring. -/
@[inline]
def square (x : FastField modulus) : FastField modulus :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[specialize]
def pow (x : FastField modulus) (n : ℕ) : FastField modulus :=
  @npowBinRec (FastField modulus) ⟨one modulus⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the prime field. -/
def invExponent (modulus : ℕ) : ℕ := modulus - 2

/-- Inversion in Montgomery form via Fermat's little theorem (`x⁻¹ = x^(p-2)`),
by binary exponentiation (`pow`). -/
@[inline]
def inv (x : FastField modulus) : FastField modulus :=
  pow x (invExponent modulus)

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : FastField modulus) : FastField modulus :=
  mul x (inv y)

instance instZero : Zero (FastField modulus) where
  zero := zero modulus

instance instOne : One (FastField modulus) where
  one := one modulus

instance instAdd : Add (FastField modulus) where
  add := add

instance instNeg : Neg (FastField modulus) where
  neg := neg

instance instSub : Sub (FastField modulus) where
  sub := sub

instance instMul : Mul (FastField modulus) where
  mul := mul

instance instInv : Inv (FastField modulus) where
  inv := inv

instance instDiv : Div (FastField modulus) where
  div := div

instance instNatCast : NatCast (FastField modulus) where
  natCast := ofNat modulus

instance instIntCast : IntCast (FastField modulus) where
  intCast := ofInt modulus

instance instNatSMul : SMul ℕ (FastField modulus) where
  smul n x := ofNat modulus n * x

instance instIntSMul : SMul Int (FastField modulus) where
  smul n x := ofInt modulus n * x

instance instPowNat : Pow (FastField modulus) ℕ where
  pow := pow

instance instPowInt : Pow (FastField modulus) Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance instNNRatCast : NNRatCast (FastField modulus) where
  nnratCast q := ofField (q : ZMod modulus)

instance instRatCast : RatCast (FastField modulus) where
  ratCast q := ofField (q : ZMod modulus)

instance instNNRatSMul : SMul ℚ≥0 (FastField modulus) where
  smul q x := ofField (q • toField x)

instance instRatSMul : SMul ℚ (FastField modulus) where
  smul q x := ofField (q • toField x)

/-- Fermat-style inversion in `ZMod modulus`. -/
theorem inv_eq_pow_field (a : ZMod modulus) (ha : a ≠ 0) :
    a⁻¹ = a ^ (modulus - 2) := by
  have hcard : Fintype.card (ZMod modulus) = modulus := ZMod.card modulus
  have h1 : a ^ (modulus - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (modulus - 2) = 1 := by
    rw [← pow_succ']; show a ^ (modulus - 2 + 1) = 1
    have : modulus - 2 + 1 = modulus - 1 := by
      have := P.two_lt_modulus; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod modulus) : toField (ofField (modulus := modulus) x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : FastField modulus) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  apply nat_eq_of_field_eq (modulus := modulus)
  · exact (ofField (toField x)).property
  · exact x.property
  · rw [raw_cast_eq_toField_mul]
    rw [toField_ofField]
    rw [raw_cast_eq_toField_mul]

/-- The canonical-field interpretation distinguishes fast values. -/
theorem toField_injective : Function.Injective (toField (modulus := modulus)) :=
  Function.LeftInverse.injective ofField_toField

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : FastField modulus) = 0 := by
  rw [toField_eq_raw_mul_inv]
  change ((0 : ℕ) : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ = 0
  rw [Nat.cast_zero, zero_mul]

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : FastField modulus) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (P.rModModulus.toNat : ZMod modulus) *
      ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ = 1
  rw [P.rModModulus_toNat, ZMod.natCast_mod]
  exact mul_inv_cancel₀ P.two_pow_32_ne_zero_in_field

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : FastField modulus) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instAdd add
  have hred := reduceUInt32Lt2Modulus_cast (modulus := modulus) (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by
      have hx := x.property; have hy := y.property; omega))
  change ((conditionalSubtract P.modulus32 (x.val + y.val)).toNat : ZMod modulus) =
      ((x.val + y.val).toNat : ZMod modulus) at hred
  change ((conditionalSubtract P.modulus32 (x.val + y.val)).toNat : ZMod modulus) *
      ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ =
        (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ +
          (y.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹
  rw [hred]
  rw [UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < 2 ^ 32 := by
    nlinarith [x.property, y.property, P.two_mul_modulus_lt_two_pow_32]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.cast_add]
  ring

/-- Fast subtraction agrees with subtraction in the canonical field. -/
@[simp]
theorem toField_sub (x y : FastField modulus) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hsubval : (x - y : FastField modulus).val = x.val - y.val := by
      change (sub x y).val = x.val - y.val
      unfold sub
      rw [dif_pos hyx]
    rw [hsubval]
    change (((x.val - y.val).toNat : ZMod modulus) *
        ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹) =
        (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ -
          (y.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyx]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hyx
      exact hyx)]
    ring
  · have hsum_lt : x.val.toNat + modulus < 2 ^ 32 := by
      have htwo := P.two_mul_modulus_lt_two_pow_32
      have := x.property; omega
    have hsum_eq : (x.val + P.modulus32).toNat = x.val.toNat + modulus := by
      rw [UInt32.toNat_add, P.modulus32_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hyle : y.val ≤ x.val + P.modulus32 := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      have := y.property; omega
    have hsubval : (x - y : FastField modulus).val = x.val + P.modulus32 - y.val := by
      change (sub x y).val = x.val + P.modulus32 - y.val
      unfold sub
      rw [dif_neg hyx]
    rw [hsubval]
    change (((x.val + P.modulus32 - y.val).toNat : ZMod modulus) *
        ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹) =
        (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ -
          (y.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, hsum_eq] at hyle
      exact hyle)]
    rw [Nat.cast_add, ZMod.natCast_self]
    ring

/-- Fast negation agrees with negation in the canonical field. -/
@[simp]
theorem toField_neg (x : FastField modulus) : toField (-x) = -toField x := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegval : (-x : FastField modulus).val = (zero modulus).val := by
      change (neg x).val = (zero modulus).val
      unfold neg
      rw [dif_pos hx]
    rw [hnegval]
    change ((zero modulus).val.toNat : ZMod modulus) *
        ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ =
        -((x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)
    have hxNat : x.val.toNat = 0 := by
      simpa using congrArg UInt32.toNat hx
    rw [hxNat]
    change ((0 : ℕ) : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ =
      -(((0 : ℕ) : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)
    simp
  · have hle : x.val ≤ P.modulus32 := by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
      exact Nat.le_of_lt x.property
    have hnegval : (-x : FastField modulus).val = P.modulus32 - x.val := by
      change (neg x).val = P.modulus32 - x.val
      unfold neg
      rw [dif_neg hx]
    rw [hnegval]
    change (((P.modulus32 - x.val).toNat : ZMod modulus) *
        ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹) =
        -((x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)
    rw [UInt32.toNat_sub_of_le _ _ hle, P.modulus32_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    ring

/-- Fast multiplication agrees with multiplication in the canonical field. -/
@[simp]
theorem toField_mul (x y : FastField modulus) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instMul mul
  have hred := montgomeryReduce_cast (modulus := modulus)
    (x.val.toUInt64 * y.val.toUInt64) (by
      simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
      have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
        nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
      rw [Nat.mod_eq_of_lt hprod]
      nlinarith [x.property, y.property, P.modulus_lt_two_pow_32, P.modulus_pos])
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
      (x.val.toUInt64 * y.val.toUInt64)).toNat : ZMod modulus) =
        ((x.val.toUInt64 * y.val.toUInt64).toNat : ZMod modulus) *
          ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ at hred
  change ((reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv
      (x.val.toUInt64 * y.val.toUInt64)).toNat : ZMod modulus) *
        ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ =
        (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ *
          ((y.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul]
  ring

/-- Ring equivalence between the fast Montgomery representation and the canonical field. -/
def ringEquiv (modulus : ℕ) [P : Mont32Field modulus] : FastField modulus ≃+* ZMod modulus where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp]
theorem ringEquiv_apply (x : FastField modulus) : ringEquiv modulus x = toField x := rfl

@[simp]
theorem ringEquiv_symm_apply (x : ZMod modulus) :
    (ringEquiv modulus).symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : FastField modulus) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : FastField modulus) (n : ℕ) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup (FastField modulus) := {
    mul := (· * ·)
    mul_assoc := mul_assoc_field
  }
  exact npowBinRec_succ n x

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : FastField modulus) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

/-- Fast natural-power computation agrees with powers in the canonical field. -/
@[simp]
theorem toField_pow (x : FastField modulus) (n : ℕ) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero]
      rw [toField_one]
      simp
  | succ n ih =>
      rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

private theorem toField_inv_pow (x : FastField modulus) :
    toField (inv x) = toField x ^ invExponent modulus := by
  unfold inv
  exact toField_pow x (invExponent modulus)

private theorem toField_inv_raw (x : FastField modulus) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero]
    exact zero_pow (by unfold invExponent; have := P.two_lt_modulus; omega)
  · simpa [invExponent] using (inv_eq_pow_field (toField x) hx).symm

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : FastField modulus) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_mul_raw (x y : FastField modulus) :
    toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

private theorem toField_div_mul_inv (x y : FastField modulus) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  exact toField_mul_raw x (inv y)

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : FastField modulus) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : ZMod modulus, c = b⁻¹ → a * c = a / b := by
    intro a b c hc
    rw [hc]
    rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : ℕ) : toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofNat modulus n) = (n : ZMod modulus)
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofInt modulus n) = (n : ZMod modulus)
  unfold ofInt
  rw [toField_ofField]

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : ℕ) (x : FastField modulus) : toField (n • x) = n • toField x := by
  change toField ((n : FastField modulus) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : FastField modulus) : toField (n • x) = n • toField x := by
  change toField ((n : FastField modulus) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : FastField modulus) (n : ℕ) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : FastField modulus) (n : Int) : toField (x ^ n) = toField x ^ n := by
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
theorem toField_nnratCast (q : ℚ≥0) : toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus)) = (q : ZMod modulus)
  rw [toField_ofField]

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus)) = (q : ZMod modulus)
  rw [toField_ofField]

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Field instance transferred from the canonical field through `toField`. -/
instance (priority := low) instField : _root_.Field (FastField modulus) :=
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
instance (priority := low) instCommRing : CommRing (FastField modulus) := by
  infer_instance

/-- A fast 32-bit-word field is non-binary. -/
instance (priority := low) instNonBinaryField : NonBinaryField (FastField modulus) where
  char_neq_2 := by
    change ((2 : ℕ) : FastField modulus) ≠ 0
    intro h
    have htwo : (2 : ZMod modulus) = 0 := by
      calc
        (2 : ZMod modulus) = ((2 : ℕ) : ZMod modulus) := by norm_cast
        _ = toField ((2 : ℕ) : FastField modulus) := (toField_natCast 2).symm
        _ = toField (0 : FastField modulus) := congrArg toField h
        _ = 0 := toField_zero
    have hdvd : modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 modulus).mp htwo
    exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)

end

end Native32
end Montgomery
