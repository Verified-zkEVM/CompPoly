/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Mersenne31.Basic

/-!
# FastMersenne31 — UInt32-backed Mersenne-31 field arithmetic

modulus = 2^31 - 1. The key identity: 2^31 ≡ 1 (mod modulus), so reduction is
"split at bit 31, add the halves".
-/

namespace Mersenne31
namespace Fast

abbrev Field : Type := { x : UInt32 // x.toNat < Mersenne31.Basic.fieldSize }

/-- The Mersenne prime 2^31 - 1 -/
@[inline] def modulus : UInt32 := 2147483647

/-- P as UInt64 -/
@[inline] def modulus64 : UInt64 := 2147483647

@[simp] theorem modulus_toNat : modulus.toNat = Mersenne31.Basic.fieldSize := by
  decide

@[simp] theorem modulus64_toNat : modulus64.toNat = Mersenne31.Basic.fieldSize := by
  decide

private theorem fieldSize_pos : 0 < Mersenne31.Basic.fieldSize := by
  decide

private theorem fieldSize_lt_uint32Size : Mersenne31.Basic.fieldSize < UInt32.size := by
  decide

private theorem fieldSize_mul_fieldSize_lt_two64 :
    Mersenne31.Basic.fieldSize * Mersenne31.Basic.fieldSize < 2 ^ 64 := by
  decide

private theorem fieldSize_add_fieldSize_lt_uint32Size :
    Mersenne31.Basic.fieldSize + Mersenne31.Basic.fieldSize < UInt32.size := by
  decide

@[inline] def raw (x : Field) : UInt32 := x.val

def zero : Field := ⟨0, by decide⟩
def one : Field := ⟨1, by decide⟩

def ofCanonicalNat (n : Nat) (h : n < Mersenne31.Basic.fieldSize) : Field :=
  ⟨UInt32.ofNat n, by
    -- prove UInt32.ofNat n has Nat value n
    rw [UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    exact h
    exact Nat.lt_trans h fieldSize_lt_uint32Size⟩

def ofNat (n : Nat) : Field :=
  ofCanonicalNat (n % Mersenne31.Basic.fieldSize) (Nat.mod_lt _ fieldSize_pos)

def ofCanonicalField (x : Mersenne31.Basic.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

def toNat (x : Field) : Nat :=
  x.val.toNat

def toCanonicalField (x : Field) : Mersenne31.Basic.Field :=
  (toNat x : Mersenne31.Basic.Field)

@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < Mersenne31.Basic.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  unfold toNat ofCanonicalNat
  have hn : n < 2 ^ 32 := by
    simpa [UInt32.size] using Nat.lt_trans h fieldSize_lt_uint32Size
  simpa [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]

@[simp]
theorem toCanonicalField_ofCanonicalNat (n : Nat) (h : n < Mersenne31.Basic.fieldSize) :
    toCanonicalField (ofCanonicalNat n h) = (n : Mersenne31.Basic.Field) := by
  unfold toCanonicalField
  rw [toNat_ofCanonicalNat]

@[simp]
theorem toCanonicalField_ofCanonicalField (x : Mersenne31.Basic.Field) :
    toCanonicalField (ofCanonicalField x) = x := by
  unfold ofCanonicalField
  rw [toCanonicalField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

@[simp]
theorem ofCanonicalField_toCanonicalField (x : Field) :
    ofCanonicalField (toCanonicalField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  change toNat (ofCanonicalField (toCanonicalField x)) = toNat x
  unfold ofCanonicalField toCanonicalField
  rw [toNat_ofCanonicalNat]
  exact ZMod.val_natCast_of_lt x.property

theorem toField_injective : Function.Injective toCanonicalField :=
  Function.LeftInverse.injective ofCanonicalField_toCanonicalField

/-- Reduce a native word known to be below twice the Mersenne31 prime. -/
@[inline]
private def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  if x < modulus then x else x - modulus

private theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * Mersenne31.Basic.fieldSize) :
    (reduceUInt32Lt2ModulusRaw x).toNat < Mersenne31.Basic.fieldSize := by
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

/-- Reduce a native word known to be below twice the Mersenne31 prime. -/
@[inline]
private def reduceUInt32Lt2Modulus (x : UInt32)
    (h : x.toNat < 2 * Mersenne31.Basic.fieldSize) : Field :=
  ⟨reduceUInt32Lt2ModulusRaw x, reduceUInt32Lt2ModulusRaw_lt x h⟩

private theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * Mersenne31.Basic.fieldSize) :
    ((reduceUInt32Lt2Modulus x h).val.toNat : Mersenne31.Basic.Field) =
      (x.toNat : Mersenne31.Basic.Field) := by
  change ((reduceUInt32Lt2ModulusRaw x).toNat : Mersenne31.Basic.Field) =
    (x.toNat : Mersenne31.Basic.Field)
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

/-- Fast modular addition. -/
@[inline]
def add (x y : Field) : Field :=
  reduceUInt32Lt2Modulus (x.val + y.val) (by
    rw [UInt32.toNat_add]
    have hsum_lt : x.val.toNat + y.val.toNat < UInt32.size := by
      nlinarith [x.property, y.property, fieldSize_add_fieldSize_lt_uint32Size]
    rw [Nat.mod_eq_of_lt hsum_lt]
    nlinarith [x.property, y.property])

instance instAddField : Add Field where
  add := add

@[simp]
theorem toCanonicalField_add (x y : Field) :
    toCanonicalField (x + y) = toCanonicalField x + toCanonicalField y := by
  unfold instAddField add toCanonicalField toNat
  have hbound : (x.val + y.val).toNat < 2 * Mersenne31.Basic.fieldSize := by
    rw [UInt32.toNat_add]
    have hsum_lt : x.val.toNat + y.val.toNat < UInt32.size := by
      nlinarith [x.property, y.property, fieldSize_add_fieldSize_lt_uint32Size]
    rw [Nat.mod_eq_of_lt hsum_lt]
    nlinarith [x.property, y.property]
  have hred := reduceUInt32Lt2Modulus_cast (x.val + y.val) hbound
  change ((reduceUInt32Lt2ModulusRaw (x.val + y.val)).toNat :
      Mersenne31.Basic.Field) =
        ((x.val + y.val).toNat : Mersenne31.Basic.Field) at hred
  change ((reduceUInt32Lt2ModulusRaw (x.val + y.val)).toNat :
      Mersenne31.Basic.Field) =
        (x.val.toNat : Mersenne31.Basic.Field) + (y.val.toNat : Mersenne31.Basic.Field)
  rw [hred]
  rw [UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < UInt32.size := by
    nlinarith [x.property, y.property, fieldSize_add_fieldSize_lt_uint32Size]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.cast_add]

end Fast
end Mersenne31
