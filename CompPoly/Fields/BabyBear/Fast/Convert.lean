/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.BabyBear.Fast.Montgomery

/-!
# Fast BabyBear Field — Conversions

Conversions between the fast Montgomery representation and the canonical
`BabyBear.Field` / `Nat` views (`ofField`, `toField`, `ofNat`, `toNat`, …), the
`zero`/`one` constants, and the round-trip cast lemmas relating them. The field
operations and ring/field instances build on this module.
-/

namespace BabyBear
namespace Fast

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (_h : n < BabyBear.fieldSize) : Field :=
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

/-- Reduce a `UInt64` modulo the BabyBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  let y := x % modulus64
  montgomeryReduceBounded (y * r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : (x % modulus64).toNat < BabyBear.fieldSize := by
      rw [UInt64.toNat_mod, modulus64_toNat]
      exact Nat.mod_lt _ fieldSize_pos
    have hprod : (x % modulus64).toNat * r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [r2ModModulus_lt_fieldSize])

/-- The zero fast BabyBear element. -/
def zero : Field := ⟨0, by decide⟩

/-- The one fast BabyBear element. -/
def one : Field := ⟨rModModulus, by decide⟩

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (n : Nat) : Field :=
  ofCanonicalNat (n % BabyBear.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  reduceUInt64 x.toUInt64

/-- Convert from the canonical `ZMod` BabyBear field into fast Montgomery form. -/
@[inline]
def ofField (x : BabyBear.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (n : Int) : Field :=
  ofField (n : BabyBear.Field)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : Field) : UInt32 :=
  raw (montgomeryReduceBounded x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, fieldSize_pos]))

/-- Convert a fast BabyBear element to its canonical natural representative. -/
@[inline]
def toNat (x : Field) : Nat :=
  (toCanonicalUInt32 x).toNat

/-- Convert a fast BabyBear element to the canonical `ZMod` BabyBear field. -/
@[inline]
def toField (x : Field) : BabyBear.Field :=
  (toNat x : BabyBear.Field)

theorem toNat_lt_fieldSize (x : Field) : toNat x < BabyBear.fieldSize := by
  unfold toNat toCanonicalUInt32 raw
  change (montgomeryReduceBoundedRaw x.val.toUInt64).toNat < BabyBear.fieldSize
  exact montgomeryReduceBoundedRaw_lt x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, fieldSize_pos])

theorem toField_eq_raw_mul_inv (x : Field) :
    toField x =
      (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ := by
  unfold toField toNat toCanonicalUInt32 raw
  have hred := montgomeryReduceBounded_cast x.val.toUInt64 (by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, fieldSize_pos])
  change ((montgomeryReduceBoundedRaw x.val.toUInt64).toNat : BabyBear.Field) =
      (x.val.toUInt64.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw x.val.toUInt64).toNat : BabyBear.Field) =
      (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  rw [hred]
  rw [UInt32.toNat_toUInt64]

theorem raw_cast_eq_toField_mul (x : Field) :
    (x.val.toNat : BabyBear.Field) =
      toField x * (UInt32.size : BabyBear.Field) := by
  rw [toField_eq_raw_mul_inv]
  rw [mul_assoc]
  rw [inv_mul_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

theorem nat_eq_of_field_eq {a b : Nat} (ha : a < BabyBear.fieldSize)
    (hb : b < BabyBear.fieldSize) (h : (a : BabyBear.Field) = (b : BabyBear.Field)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < BabyBear.fieldSize) :
    ((ofCanonicalNat n h).val.toNat : BabyBear.Field) =
      (n : BabyBear.Field) * (UInt32.size : BabyBear.Field) := by
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
      (UInt64.ofNat n * r2ModModulus.toUInt64)).toNat : BabyBear.Field) =
        ((UInt64.ofNat n * r2ModModulus.toUInt64).toNat : BabyBear.Field) *
          (UInt32.size : BabyBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw
      (UInt64.ofNat n * r2ModModulus.toUInt64)).toNat : BabyBear.Field) =
        (n : BabyBear.Field) * (UInt32.size : BabyBear.Field)
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
  rw [mul_assoc (n : BabyBear.Field) ((UInt32.size : BabyBear.Field) *
    (UInt32.size : BabyBear.Field)) ((UInt32.size : BabyBear.Field)⁻¹)]
  rw [mul_assoc (UInt32.size : BabyBear.Field) (UInt32.size : BabyBear.Field)
    ((UInt32.size : BabyBear.Field)⁻¹)]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

theorem toField_ofCanonicalNat_aux (n : Nat) (h : n < BabyBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : BabyBear.Field) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field) := by
  unfold reduceUInt64
  let y := x % modulus64
  have hred := montgomeryReduceBounded_cast (y * r2ModModulus.toUInt64) (by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hy_lt : y.toNat < BabyBear.fieldSize := by
      rw [show y = x % modulus64 by rfl, UInt64.toNat_mod, modulus64_toNat]
      exact Nat.mod_lt _ fieldSize_pos
    have hprod : y.toNat * r2ModModulus.toNat < 2 ^ 64 := by
      nlinarith [hy_lt, r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [r2ModModulus_lt_fieldSize])
  change ((montgomeryReduceBoundedRaw (y * r2ModModulus.toUInt64)).toNat :
      BabyBear.Field) =
        ((y * r2ModModulus.toUInt64).toNat : BabyBear.Field) *
          (UInt32.size : BabyBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (y * r2ModModulus.toUInt64)).toNat :
      BabyBear.Field) =
        (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hy_lt : y.toNat < BabyBear.fieldSize := by
    rw [show y = x % modulus64 by rfl, UInt64.toNat_mod, modulus64_toNat]
    exact Nat.mod_lt _ fieldSize_pos
  have hprod : y.toNat * r2ModModulus.toNat < 2 ^ 64 := by
    nlinarith [hy_lt, r2ModModulus_lt_fieldSize, fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  have hy_cast : (y.toNat : BabyBear.Field) = (x.toNat : BabyBear.Field) := by
    rw [show y = x % modulus64 by rfl, UInt64.toNat_mod, modulus64_toNat]
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.mod_modEq _ _
  rw [Nat.cast_mul, r2ModModulus_cast, hy_cast]
  rw [pow_two]
  rw [mul_assoc (x.toNat : BabyBear.Field) ((UInt32.size : BabyBear.Field) *
    (UInt32.size : BabyBear.Field)) ((UInt32.size : BabyBear.Field)⁻¹)]
  rw [mul_assoc (UInt32.size : BabyBear.Field) (UInt32.size : BabyBear.Field)
    ((UInt32.size : BabyBear.Field)⁻¹)]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  exact nat_eq_of_field_eq (toNat_lt_fieldSize _) h (toField_ofCanonicalNat_aux n h)

/-- `ofCanonicalNat` embeds a canonical representative into the canonical field. -/
@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : BabyBear.Field) := by
  exact toField_ofCanonicalNat_aux n h

/-- Reducing a `UInt64` gives the canonical natural residue modulo BabyBear. -/
@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 x) = x.toNat % BabyBear.fieldSize := by
  apply nat_eq_of_field_eq (toNat_lt_fieldSize _) (Nat.mod_lt _ fieldSize_pos)
  change toField (reduceUInt64 x) = ((x.toNat % BabyBear.fieldSize : Nat) : BabyBear.Field)
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]
  rw [ZMod.natCast_eq_natCast_iff]
  exact (Nat.mod_modEq _ _).symm

/-- Reducing a `UInt64` agrees with casting that word into the canonical field. -/
@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 x) = (x.toNat : BabyBear.Field) := by
  rw [toField_eq_raw_mul_inv, reduceUInt64_raw_cast]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ uint32Size_ne_zero_in_field]
  rw [mul_one]

end Fast
end BabyBear
