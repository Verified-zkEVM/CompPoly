/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Mersenne31.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Data.Nat.Bitwise
import Mathlib.FieldTheory.Finite.Basic

/-!
# FastMersenne31 — UInt32-backed Mersenne-31 field arithmetic

This module provides a native-word implementation of Mersenne31 arithmetic as a
sidecar to the canonical `Mersenne31.Basic.Field := ZMod Mersenne31.Basic.fieldSize`
model.

Fast field values are stored as canonical `UInt32` representatives below
`2^31 - 1`. Multiplication reduces a bounded `UInt64` product using the Mersenne
identity `2^31 ≡ 1 (mod 2^31 - 1)`: split at bit 31, add the halves, then perform
one final subtraction if needed.
-/

namespace Mersenne31
namespace Fast

/-- The fast native-word Mersenne31 field carrier, stored as a canonical `UInt32`
representative below the prime modulus. -/
abbrev Field : Type := { x : UInt32 // x.toNat < Mersenne31.Basic.fieldSize }

/-- Fast representatives have decidable equality through their `UInt32` value. -/
instance : DecidableEq Field := inferInstance

/-- The Mersenne31 prime `2^31 - 1` as a native `UInt32`. -/
@[inline]
def modulus : UInt32 := 2147483647

/-- The Mersenne31 prime `2^31 - 1` as a native `UInt64`. -/
@[inline]
private def modulus64 : UInt64 := 2147483647

/-- The native `UInt32` modulus agrees with the mathematical Mersenne31 modulus. -/
@[simp]
theorem modulus_toNat : modulus.toNat = Mersenne31.Basic.fieldSize := by
  decide

/-- The native `UInt64` modulus agrees with the mathematical Mersenne31 modulus. -/
@[simp]
private theorem modulus64_toNat : modulus64.toNat = Mersenne31.Basic.fieldSize := by
  decide

/-- The Mersenne31 modulus is positive. -/
private theorem fieldSize_pos : 0 < Mersenne31.Basic.fieldSize := by
  decide

/-- The Mersenne31 modulus fits in a `UInt32`. -/
private theorem fieldSize_lt_uint32Size : Mersenne31.Basic.fieldSize < UInt32.size := by
  decide

/-- A product of two canonical Mersenne31 representatives fits in a `UInt64`. -/
private theorem fieldSize_mul_fieldSize_lt_two64 :
    Mersenne31.Basic.fieldSize * Mersenne31.Basic.fieldSize < 2 ^ 64 := by
  decide

/-- A sum of two canonical Mersenne31 representatives does not overflow `UInt32`. -/
private theorem fieldSize_add_fieldSize_lt_uint32Size :
    Mersenne31.Basic.fieldSize + Mersenne31.Basic.fieldSize < UInt32.size := by
  decide

/-- The raw native word backing a fast Mersenne31 element. -/
@[inline]
def raw (x : Field) : UInt32 := x.val

/-- Reading the raw word from a subtype literal returns its stored word. -/
@[simp]
theorem raw_mk (x : UInt32) (h : x.toNat < Mersenne31.Basic.fieldSize) :
    raw ⟨x, h⟩ = x := rfl

/-- `raw` is the underlying `UInt32` value. -/
@[simp]
theorem raw_eq_val (x : Field) : raw x = x.val := rfl

/-- The zero fast Mersenne31 element. -/
@[inline]
private def zero : Field := ⟨0, by decide⟩

/-- The one fast Mersenne31 element. -/
@[inline]
private def one : Field := ⟨1, by decide⟩

/-- Use `zero` for the standard `0` notation on fast Mersenne31 elements. -/
instance instZeroField : Zero Field where
  zero := zero

/-- Use `one` for the standard `1` notation on fast Mersenne31 elements. -/
instance instOneField : One Field where
  one := one

/-- Build a fast element from a canonical natural representative. -/
@[inline]
private def ofCanonicalNat (n : Nat) (h : n < Mersenne31.Basic.fieldSize) : Field :=
  ⟨UInt32.ofNat n, by
    have hn : n < UInt32.size := Nat.lt_trans h fieldSize_lt_uint32Size
    simpa [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn] using h⟩

/-- Convert a natural number into fast representation by reducing modulo Mersenne31. -/
@[inline]
def ofNat (n : Nat) : Field :=
  ofCanonicalNat (n % Mersenne31.Basic.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a fast Mersenne31 element to its canonical natural representative. -/
@[inline]
def toNat (x : Field) : Nat :=
  x.val.toNat

/-- Reading the natural representative from a subtype literal returns the stored word's
natural value. -/
@[simp]
theorem toNat_mk (x : UInt32) (h : x.toNat < Mersenne31.Basic.fieldSize) :
    toNat ⟨x, h⟩ = x.toNat := rfl

/-- `toNat` is the natural value of the underlying `UInt32` word. -/
@[simp]
theorem toNat_eq_val_toNat (x : Field) : toNat x = x.val.toNat := rfl

/-- Convert from the canonical `ZMod` Mersenne31 field into fast representation. -/
@[inline]
def ofField (x : Mersenne31.Basic.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert a fast Mersenne31 element to the canonical `ZMod` field. -/
@[inline]
def toField (x : Field) : Mersenne31.Basic.Field :=
  (toNat x : Mersenne31.Basic.Field)

/-- Convert a 32-bit word into fast representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  ofNat x.toNat

/-- Convert an integer into fast representation. -/
@[inline]
def ofInt (z : Int) : Field :=
  ofField (z : Mersenne31.Basic.Field)

/-- Use `ofNat` for natural-number casts into fast Mersenne31. -/
instance instNatCastField : NatCast Field where
  natCast := ofNat

/-- Interpret integer casts through the canonical Mersenne31 field. -/
instance instIntCastField : IntCast Field where
  intCast := ofInt

/-- Interpret nonnegative rational casts through the canonical Mersenne31 field. -/
instance instNNRatCastField : NNRatCast Field where
  nnratCast q := ofField (q : Mersenne31.Basic.Field)

/-- Interpret rational casts through the canonical Mersenne31 field. -/
instance instRatCastField : RatCast Field where
  ratCast q := ofField (q : Mersenne31.Basic.Field)

/-- The raw word backing fast zero is zero. -/
@[simp]
theorem raw_zero : raw (0 : Field) = 0 := rfl

/-- The raw word backing fast one is one. -/
@[simp]
theorem raw_one : raw (1 : Field) = 1 := rfl

/-- The natural representative of fast zero is zero. -/
@[simp]
theorem toNat_zero : toNat (0 : Field) = 0 := rfl

/-- The natural representative of fast one is one. -/
@[simp]
theorem toNat_one : toNat (1 : Field) = 1 := rfl

/-- Convert a canonical natural representative to fast form and read it back unchanged. -/
@[simp]
private theorem toNat_ofCanonicalNat (n : Nat) (h : n < Mersenne31.Basic.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  unfold toNat ofCanonicalNat
  have hn : n < UInt32.size := Nat.lt_trans h fieldSize_lt_uint32Size
  simp [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]

/-- Converting a canonical natural representative to fast form agrees with the same
natural cast in the canonical `ZMod` field. -/
@[simp]
private theorem toField_ofCanonicalNat (n : Nat) (h : n < Mersenne31.Basic.fieldSize) :
    toField (ofCanonicalNat n h) = (n : Mersenne31.Basic.Field) := by
  unfold toField
  rw [toNat_ofCanonicalNat]

/-- Converting a natural number to fast form and reading it back gives its canonical
representative modulo Mersenne31. -/
@[simp]
theorem toNat_ofNat (n : Nat) :
    toNat (ofNat n) = n % Mersenne31.Basic.fieldSize := by
  unfold ofNat
  rw [toNat_ofCanonicalNat]

/-- Converting a natural number to fast form agrees with the same natural cast in the
canonical field. -/
@[simp]
theorem toField_ofNat (n : Nat) :
    toField (ofNat n) = (n : Mersenne31.Basic.Field) := by
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [← ZMod.natCast_zmod_val (n : Mersenne31.Basic.Field)]
  rw [ZMod.val_natCast]

/-- Converting a `UInt32` to fast form agrees with casting its natural value into the
canonical field. -/
@[simp]
theorem toField_ofUInt32 (x : UInt32) :
    toField (ofUInt32 x) = (x.toNat : Mersenne31.Basic.Field) := by
  unfold ofUInt32
  rw [toField_ofNat]

/-- Converting a `UInt32` to fast form and reading it back gives its value modulo
Mersenne31. -/
@[simp]
theorem toNat_ofUInt32 (x : UInt32) :
    toNat (ofUInt32 x) = x.toNat % Mersenne31.Basic.fieldSize := by
  unfold ofUInt32
  rw [toNat_ofNat]

/-- Converting from the canonical field to fast form and reading the natural
representative returns the canonical `ZMod` representative. -/
@[simp]
theorem toNat_ofField (x : Mersenne31.Basic.Field) : toNat (ofField x) = x.val := by
  unfold ofField
  rw [toNat_ofCanonicalNat]

/-- Converting from the canonical `ZMod` field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : Mersenne31.Basic.Field) :
    toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting an integer to fast form agrees with casting it into the canonical field. -/
@[simp]
theorem toField_ofInt (z : Int) :
    toField (ofInt z) = (z : Mersenne31.Basic.Field) := by
  unfold ofInt
  rw [toField_ofField]

/-- Converting from fast form to the canonical `ZMod` field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) :
    ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  change toNat (ofField (toField x)) = toNat x
  unfold ofField toField
  rw [toNat_ofCanonicalNat]
  exact ZMod.val_natCast_of_lt x.property

/-- The canonical-field projection is injective because `ofField` is its left inverse. -/
private theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- The fast zero maps to zero in the canonical field. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by
  decide

/-- The fast one maps to one in the canonical field. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by
  decide

/-- Natural casts in the fast field agree with natural casts in the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) :
    toField (n : Field) = (n : Mersenne31.Basic.Field) := by
  change toField (ofNat n) = (n : Mersenne31.Basic.Field)
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [← ZMod.natCast_zmod_val (n : Mersenne31.Basic.Field)]
  rw [ZMod.val_natCast]

/-- Integer casts in the fast field agree with integer casts in the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) :
    toField (n : Field) = (n : Mersenne31.Basic.Field) := by
  change toField (ofInt n) = (n : Mersenne31.Basic.Field)
  rw [toField_ofInt]

/-- Nonnegative rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) :
    toField (q : Field) = (q : Mersenne31.Basic.Field) := by
  change toField (ofField (q : Mersenne31.Basic.Field)) = (q : Mersenne31.Basic.Field)
  rw [toField_ofField]

/-- Rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) :
    toField (q : Field) = (q : Mersenne31.Basic.Field) := by
  change toField (ofField (q : Mersenne31.Basic.Field)) = (q : Mersenne31.Basic.Field)
  rw [toField_ofField]

/-- Raw one-step reduction for a `UInt32` known to represent a value below `2 * p`.

If the word is already below `p`, keep it; otherwise subtract `p`. -/
@[inline]
private def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  if x < modulus then x else x - modulus

/-- The raw one-step reducer returns a canonical representative below the modulus. -/
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

/-- Reduce a `UInt32` known to represent a value below `2 * p` into fast field form. -/
@[inline]
private def reduceUInt32Lt2Modulus (x : UInt32)
    (h : x.toNat < 2 * Mersenne31.Basic.fieldSize) : Field :=
  ⟨reduceUInt32Lt2ModulusRaw x, reduceUInt32Lt2ModulusRaw_lt x h⟩

/-- One-step `UInt32` reduction preserves the represented canonical field element.

This is the semantic correctness lemma for `reduceUInt32Lt2Modulus`: subtracting the
Mersenne31 modulus when needed changes the native representative, but not its value
in `ZMod fieldSize`. -/
private theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * Mersenne31.Basic.fieldSize) :
    ((reduceUInt32Lt2Modulus x h).val.toNat : Mersenne31.Basic.Field) =
      (x.toNat : Mersenne31.Basic.Field) := by
  change ((reduceUInt32Lt2ModulusRaw x).toNat : Mersenne31.Basic.Field) =
    (x.toNat : Mersenne31.Basic.Field)
  unfold reduceUInt32Lt2ModulusRaw
  by_cases hx : x < modulus
  · rw [if_pos hx]
  · rw [if_neg hx]
    have hmod_le_x : modulus ≤ x := by
      rw [UInt32.le_iff_toNat_le, modulus_toNat]
      rw [UInt32.lt_iff_toNat_lt, modulus_toNat] at hx
      exact Nat.le_of_not_gt hx
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

/-- Use fast modular addition for the standard `+` notation on Mersenne31 fast elements. -/
instance instAddField : Add Field where
  add := add

/-- Fast addition agrees with addition in the canonical `ZMod` Mersenne31 field. -/
@[simp]
theorem toField_add (x y : Field) :
    toField (x + y) = toField x + toField y := by
  unfold instAddField add toField toNat
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

/-- Fast modular subtraction, using `x - y` when no underflow occurs and
`x + p - y` otherwise. -/
@[inline]
def sub (x y : Field) : Field :=
  if hxy : x.val ≥ y.val then
    ⟨x.val - y.val, by
      have hy_le_x : y.val.toNat ≤ x.val.toNat := by
        simpa [UInt32.le_iff_toNat_le] using hxy
      rw [UInt32.toNat_sub_of_le _ _ hxy]
      omega⟩
  else
    ⟨x.val + modulus - y.val, by
      have hsum_lt : x.val.toNat + Mersenne31.Basic.fieldSize < UInt32.size := by
        nlinarith [x.property, fieldSize_add_fieldSize_lt_uint32Size]
      have hsum_eq :
          (x.val + modulus).toNat = x.val.toNat + Mersenne31.Basic.fieldSize := by
        rw [UInt32.toNat_add, modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
      have hy_le_sum : y.val ≤ x.val + modulus := by
        rw [UInt32.le_iff_toNat_le, hsum_eq]
        omega
      have hx_lt_y : x.val.toNat < y.val.toNat := by
        have hx_not_ge : ¬y.val.toNat ≤ x.val.toNat := by
          intro hle
          apply hxy
          rw [ge_iff_le, UInt32.le_iff_toNat_le]
          exact hle
        omega
      rw [UInt32.toNat_sub_of_le _ _ hy_le_sum, hsum_eq]
      omega⟩

/-- Use fast modular subtraction for the standard `-` notation on Mersenne31 fast elements. -/
instance instSubField : Sub Field where
  sub := sub

/-- Fast subtraction agrees with subtraction in the canonical `ZMod` Mersenne31 field. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y := by
  change (((sub x y).val.toNat : Mersenne31.Basic.Field) =
    (x.val.toNat : Mersenne31.Basic.Field) - (y.val.toNat : Mersenne31.Basic.Field))
  unfold sub
  by_cases hxy : x.val ≥ y.val
  · rw [dif_pos hxy]
    rw [UInt32.toNat_sub_of_le _ _ hxy]
    rw [Nat.cast_sub (by
      rw [ge_iff_le, UInt32.le_iff_toNat_le] at hxy
      exact hxy)]
  · rw [dif_neg hxy]
    have hsum_lt : x.val.toNat + Mersenne31.Basic.fieldSize < UInt32.size := by
      nlinarith [x.property, fieldSize_add_fieldSize_lt_uint32Size]
    have hsum_eq :
        (x.val + modulus).toNat = x.val.toNat + Mersenne31.Basic.fieldSize := by
      rw [UInt32.toNat_add, modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hy_le_sum : y.val ≤ x.val + modulus := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      omega
    rw [UInt32.toNat_sub_of_le _ _ hy_le_sum, hsum_eq]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, hsum_eq] at hy_le_sum
      exact hy_le_sum)]
    rw [Nat.cast_add]
    simp

/-- Fast modular negation. Zero remains zero; nonzero `x` maps to `p - x`. -/
@[inline]
def neg (x : Field) : Field :=
  if hx : x.val = 0 then
    zero
  else
    ⟨modulus - x.val, by
      have hle : x.val ≤ modulus := by
        rw [UInt32.le_iff_toNat_le, modulus_toNat]
        exact Nat.le_of_lt x.property
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt32.toNat_inj.mp
        simpa using hzero
      rw [UInt32.toNat_sub_of_le _ _ hle, modulus_toNat]
      omega⟩

/-- Use fast modular negation for the standard unary `-` notation on Mersenne31 fast elements. -/
instance instNegField : Neg Field where
  neg := neg

/-- Fast negation agrees with negation in the canonical `ZMod` Mersenne31 field. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x := by
  change (((neg x).val.toNat : Mersenne31.Basic.Field) =
    -(x.val.toNat : Mersenne31.Basic.Field))
  unfold neg
  by_cases hx : x.val = 0
  · rw [dif_pos hx]
    have hxNat : x.val.toNat = 0 := by
      simpa using congrArg UInt32.toNat hx
    rw [hxNat]
    simp [zero]
  · rw [dif_neg hx]
    have hle : x.val ≤ modulus := by
      rw [UInt32.le_iff_toNat_le, modulus_toNat]
      exact Nat.le_of_lt x.property
    rw [UInt32.toNat_sub_of_le _ _ hle, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, modulus_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    simp

/-- Raw Mersenne reduction for bounded `UInt64` inputs below `p * p`.

This splits the native word at bit 31 and uses `2^31 ≡ 1 mod p`. For inputs
below `p * p`, the split sum is below `2 * p`, so one `UInt32` reduction
canonicalizes it. -/
@[inline]
private def reduceUInt64Raw (x : UInt64) : UInt32 :=
  let lo := x &&& modulus64
  let hi := x >>> 31
  let s := (lo + hi).toUInt32
  reduceUInt32Lt2ModulusRaw s

/-- The native bit split used by `reduceUInt64Raw` agrees with the Nat-level
Mersenne split. -/
private theorem reduceUInt64Raw_split_toNat (x : UInt64)
    (hsum_lt_uint32 : x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 < 2 ^ 32) :
    ((x &&& modulus64) + (x >>> 31)).toUInt32.toNat =
      x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 := by
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_and,
    UInt64.toNat_shiftRight, modulus64_toNat, Nat.shiftRight_eq_div_pow]
  rw [show Mersenne31.Basic.fieldSize = 2 ^ 31 - 1 by decide]
  rw [show UInt64.toNat 31 % 64 = 31 by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hsum_lt_uint32 (by decide : 2 ^ 32 < 2 ^ 64))]
  rw [Nat.mod_eq_of_lt hsum_lt_uint32]

/-- The bounded `UInt64` Mersenne reducer returns a canonical representative below `p`. -/
private theorem reduceUInt64Raw_lt (x : UInt64)
    (h : x.toNat < Mersenne31.Basic.fieldSize * Mersenne31.Basic.fieldSize) :
    (reduceUInt64Raw x).toNat < Mersenne31.Basic.fieldSize := by
  unfold reduceUInt64Raw
  apply reduceUInt32Lt2ModulusRaw_lt
  have hlow_le : x.toNat % 2 ^ 31 ≤ Mersenne31.Basic.fieldSize := by
    have hlow_lt : x.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have hfield : Mersenne31.Basic.fieldSize = 2 ^ 31 - 1 := by
      decide
    omega
  have hhi_lt : x.toNat / 2 ^ 31 < Mersenne31.Basic.fieldSize := by
    rw [Nat.div_lt_iff_lt_mul]
    · have hfield_lt_pow31 : Mersenne31.Basic.fieldSize < 2 ^ 31 := by
        decide
      nlinarith [h, hfield_lt_pow31, fieldSize_pos]
    · decide
  have hsum_lt_two_fieldSize :
      x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 <
        2 * Mersenne31.Basic.fieldSize := by
    have hsum := Nat.add_lt_add_of_le_of_lt hlow_le hhi_lt
    nlinarith
  have hsum_lt_uint32 :
      x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 < 2 ^ 32 := by
    have htwo_lt_uint32 : 2 * Mersenne31.Basic.fieldSize < 2 ^ 32 := by
      simpa [UInt32.size, two_mul] using fieldSize_add_fieldSize_lt_uint32Size
    nlinarith
  rw [reduceUInt64Raw_split_toNat x hsum_lt_uint32]
  exact hsum_lt_two_fieldSize

/-- Reduce a bounded `UInt64` modulo Mersenne31. -/
@[inline]
private def reduceUInt64 (x : UInt64)
    (h : x.toNat < Mersenne31.Basic.fieldSize * Mersenne31.Basic.fieldSize) : Field :=
  ⟨reduceUInt64Raw x, reduceUInt64Raw_lt x h⟩

/-- Bounded `UInt64` reduction preserves the represented canonical field element. -/
private theorem reduceUInt64_cast (x : UInt64)
    (h : x.toNat < Mersenne31.Basic.fieldSize * Mersenne31.Basic.fieldSize) :
    ((reduceUInt64 x h).val.toNat : Mersenne31.Basic.Field) =
      (x.toNat : Mersenne31.Basic.Field) := by
  change ((reduceUInt64Raw x).toNat : Mersenne31.Basic.Field) =
    (x.toNat : Mersenne31.Basic.Field)
  unfold reduceUInt64Raw
  have hlow_le : x.toNat % 2 ^ 31 ≤ Mersenne31.Basic.fieldSize := by
    have hlow_lt : x.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have hfield : Mersenne31.Basic.fieldSize = 2 ^ 31 - 1 := by
      decide
    omega
  have hhi_lt : x.toNat / 2 ^ 31 < Mersenne31.Basic.fieldSize := by
    rw [Nat.div_lt_iff_lt_mul]
    · have hfield_lt_pow31 : Mersenne31.Basic.fieldSize < 2 ^ 31 := by
        decide
      nlinarith [h, hfield_lt_pow31, fieldSize_pos]
    · decide
  have hsum_lt_two_fieldSize :
      x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 <
        2 * Mersenne31.Basic.fieldSize := by
    have hsum := Nat.add_lt_add_of_le_of_lt hlow_le hhi_lt
    nlinarith
  have hsum_lt_uint32 :
      x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 < 2 ^ 32 := by
    have htwo_lt_uint32 : 2 * Mersenne31.Basic.fieldSize < 2 ^ 32 := by
      simpa [UInt32.size, two_mul] using fieldSize_add_fieldSize_lt_uint32Size
    nlinarith
  have hword :
      ((x &&& modulus64) + (x >>> 31)).toUInt32.toNat =
        x.toNat % 2 ^ 31 + x.toNat / 2 ^ 31 :=
    reduceUInt64Raw_split_toNat x hsum_lt_uint32
  have hred := reduceUInt32Lt2Modulus_cast
    ((x &&& modulus64) + (x >>> 31)).toUInt32 (by
      rw [hword]
      exact hsum_lt_two_fieldSize)
  change ((reduceUInt32Lt2ModulusRaw
      ((x &&& modulus64) + (x >>> 31)).toUInt32).toNat :
        Mersenne31.Basic.Field) =
      (((x &&& modulus64) + (x >>> 31)).toUInt32.toNat :
        Mersenne31.Basic.Field) at hred
  rw [hred, hword]
  conv_rhs => rw [← Nat.mod_add_div x.toNat (2 ^ 31)]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul]
  have hpow : ((2 ^ 31 : Nat) : Mersenne31.Basic.Field) = 1 := by
    decide
  rw [hpow, one_mul, add_comm]

/-- Interpreting a bounded `UInt64` reduction in the canonical field gives the original
`UInt64` value modulo `p`. -/
@[simp]
private theorem toField_reduceUInt64 (x : UInt64)
    (h : x.toNat < Mersenne31.Basic.fieldSize * Mersenne31.Basic.fieldSize) :
    toField (reduceUInt64 x h) = (x.toNat : Mersenne31.Basic.Field) := by
  exact reduceUInt64_cast x h

/-- Fast modular multiplication. -/
@[inline]
def mul (x y : Field) : Field :=
  reduceUInt64 (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property])

/-- Use fast modular multiplication for the standard `*` notation on Mersenne31 fast
elements. -/
instance instMulField : Mul Field where
  mul := mul

/-- Natural scalar multiplication is multiplication by the corresponding fast natural cast. -/
instance instNatSMulField : SMul Nat Field where
  smul n x := (n : Field) * x

/-- Integer scalar multiplication is multiplication by the corresponding fast integer cast. -/
instance instIntSMulField : SMul Int Field where
  smul n x := (n : Field) * x

/-- Nonnegative rational scalar multiplication is transported through the canonical field. -/
instance instNNRatSMulField : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

/-- Rational scalar multiplication is transported through the canonical field. -/
instance instRatSMulField : SMul ℚ Field where
  smul q x := ofField (q • toField x)

/-- Fast multiplication agrees with multiplication in the canonical `ZMod` Mersenne31
field. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y := by
  change toField (mul x y) = toField x * toField y
  unfold mul
  rw [toField_reduceUInt64]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul]
  rfl

/-- Fast squaring. -/
@[inline]
def square (x : Field) : Field :=
  mul x x

/-- Fast squaring agrees with multiplying the canonical field value by itself. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x := by
  unfold square
  exact toField_mul x x

/-- Exponentiation over the fast representation using binary exponentiation. -/
@[inline]
def pow (x : Field) (n : Nat) : Field :=
  @npowBinRec Field ⟨one⟩ ⟨mul⟩ n x

/-- Use fast binary exponentiation for natural powers. -/
instance instPowFieldNat : Pow Field Nat where
  pow := pow

/-- Fast multiplication is associative because it agrees with canonical-field
multiplication. -/
private theorem mul_assoc_field (x y z : Field) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

/-- Successor rule for the local binary exponentiation routine. -/
private theorem pow_succ (x : Field) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup Field := {
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

/-- The concrete Fermat exponent `p - 2` used for inversion in the Mersenne31 prime field.

For a nonzero field element `x` over a prime field of size `p`, Fermat's little
theorem gives `x^(p - 1) = 1`, so `x^(p - 2)` is the multiplicative inverse of
`x`. -/
@[inline]
private def invExponent : Nat := Mersenne31.Basic.fieldSize - 2

/-- Four squarings followed by multiplication by the next 4-bit exponent digit. -/
@[inline]
private def shift4Mul (acc digit : Field) : Field :=
  mul (square (square (square (square acc)))) digit

/-- Fast modular inversion using a fixed Fermat addition chain for `x^(p - 2)`.

The exponent is `p - 2 = 2147483645 = 0x7FFFFFFD`. The chain builds the
hex digits `7 F F F F F F D` by repeatedly applying `shift4Mul`, which raises
the accumulator to the 16th power and multiplies by the next 4-bit digit.

This sends zero to zero, matching Lean's field inverse convention. -/
@[inline]
def inv (x : Field) : Field :=
  let x2 := square x -- x^2
  let x3 := mul x2 x -- x^3
  let x6 := square x3 -- x^6
  let x7 := mul x6 x -- x^7
  let x13 := mul x7 x6 -- x^13
  let x14 := square x7 -- x^14
  let x15 := mul x14 x -- x^15
  let acc := shift4Mul x7 x15 -- x^127
  let acc := shift4Mul acc x15 -- x^2047
  let acc := shift4Mul acc x15 -- x^32767
  let acc := shift4Mul acc x15 -- x^524287
  let acc := shift4Mul acc x15 -- x^8388607
  let acc := shift4Mul acc x15 -- x^134217727
  shift4Mul acc x13 -- x^2147483645

/-- Use Fermat-based fast inversion for the standard inverse notation. -/
instance instInvField : Inv Field where
  inv := inv

/-- Multiplication of two fast values adds their tracked exponents after projection to
the canonical field. -/
private theorem toField_mul_pow (base x y : Field) (m n : Nat)
    (hx : toField x = toField base ^ m) (hy : toField y = toField base ^ n) :
    toField (mul x y) = toField base ^ (m + n) := by
  change toField (x * y) = toField base ^ (m + n)
  rw [toField_mul, hx, hy, ← pow_add]

/-- `shift4Mul acc digit` projects to `acc^16 * digit` in the canonical field. -/
private theorem toField_shift4Mul (acc digit : Field) :
    toField (shift4Mul acc digit) = toField acc ^ 16 * toField digit := by
  unfold shift4Mul
  change toField (square (square (square (square acc))) * digit) =
    toField acc ^ 16 * toField digit
  rw [toField_mul]
  repeat rw [toField_square]
  ring

/-- Exponent-tracking form of `toField_shift4Mul`: shift by one hexadecimal digit and
add the next digit exponent. -/
private theorem toField_shift4Mul_pow (base acc digit : Field) (e d : Nat)
    (hacc : toField acc = toField base ^ e) (hdigit : toField digit = toField base ^ d) :
    toField (shift4Mul acc digit) = toField base ^ (16 * e + d) := by
  rw [toField_shift4Mul, hacc, hdigit]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- The fixed inversion chain computes exactly the Fermat exponent `p - 2`. -/
private theorem toField_inv_pow (x : Field) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv
  let x2 := square x
  let x3 := mul x2 x
  let x6 := square x3
  let x7 := mul x6 x
  let x13 := mul x7 x6
  let x14 := square x7
  let x15 := mul x14 x
  let acc1 := shift4Mul x7 x15
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
  have hx6 : toField x6 = toField x ^ 6 := by
    dsimp [x6]
    rw [toField_square, hx3, ← pow_add]
  have hx7 : toField x7 = toField x ^ 7 := by
    dsimp [x7]
    simpa using toField_mul_pow x x6 x 6 1 hx6 hx1
  have hx13 : toField x13 = toField x ^ 13 := by
    dsimp [x13]
    simpa using toField_mul_pow x x7 x6 7 6 hx7 hx6
  have hx14 : toField x14 = toField x ^ 14 := by
    dsimp [x14]
    rw [toField_square, hx7, ← pow_add]
  have hx15 : toField x15 = toField x ^ 15 := by
    dsimp [x15]
    simpa using toField_mul_pow x x14 x 14 1 hx14 hx1
  have hacc1 : toField acc1 = toField x ^ 127 := by
    dsimp [acc1]
    simpa using toField_shift4Mul_pow x x7 x15 7 15 hx7 hx15
  have hacc2 : toField acc2 = toField x ^ 2047 := by
    dsimp [acc2]
    simpa using toField_shift4Mul_pow x acc1 x15 127 15 hacc1 hx15
  have hacc3 : toField acc3 = toField x ^ 32767 := by
    dsimp [acc3]
    simpa using toField_shift4Mul_pow x acc2 x15 2047 15 hacc2 hx15
  have hacc4 : toField acc4 = toField x ^ 524287 := by
    dsimp [acc4]
    simpa using toField_shift4Mul_pow x acc3 x15 32767 15 hacc3 hx15
  have hacc5 : toField acc5 = toField x ^ 8388607 := by
    dsimp [acc5]
    simpa using toField_shift4Mul_pow x acc4 x15 524287 15 hacc4 hx15
  have hacc6 : toField acc6 = toField x ^ 134217727 := by
    dsimp [acc6]
    simpa using toField_shift4Mul_pow x acc5 x15 8388607 15 hacc5 hx15
  have hfinal := toField_shift4Mul_pow x acc6 x13 134217727 13 hacc6 hx13
  simpa [invExponent, Mersenne31.Basic.fieldSize] using hfinal

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx]
    simp [invExponent, Mersenne31.Basic.fieldSize]
  · symm
    apply inv_eq_of_mul_eq_one_right
    calc
      toField x * toField x ^ invExponent = toField x ^ (invExponent + 1) := by
        rw [pow_succ']
      _ = toField x ^ (Mersenne31.Basic.fieldSize - 1) := by
        congr 1
      _ = 1 := by
        exact ZMod.pow_card_sub_one_eq_one hx

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field :=
  mul x (inv y)

/-- Use fast inversion and multiplication for the standard `/` notation. -/
instance instDivField : Div Field where
  div := div

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  unfold div
  change toField (x * inv y) = toField x / toField y
  rw [toField_mul]
  change toField x * toField y⁻¹ = toField x / toField y
  rw [toField_inv]
  rfl

/-- Use fast natural powers and inversion for integer powers. -/
instance instPowFieldInt : Pow Field Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

/-- Fast natural scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

/-- Fast integer scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

/-- Standard fast natural powers agree with powers in the canonical field. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  exact toField_pow x n

/-- Standard fast integer powers agree with integer powers in the canonical field. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat k =>
      change toField (pow x k) = toField x ^ (k : Int)
      rw [toField_pow, zpow_natCast]
  | negSucc k =>
      change toField (pow (inv x) (k + 1)) = toField x ^ Int.negSucc k
      rw [toField_pow]
      change toField x⁻¹ ^ (k + 1) = toField x ^ Int.negSucc k
      rw [toField_inv, zpow_negSucc, inv_pow]

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

/-- Ring equivalence between the fast representation and canonical `Mersenne31.Field`. -/
def ringEquiv : Field ≃+* Mersenne31.Basic.Field where
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
theorem ringEquiv_symm_apply (x : Mersenne31.Basic.Field) : ringEquiv.symm x = ofField x := rfl

/-- Field instance transferred from canonical Mersenne31 through `toField`. -/
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

/-- Fast Mersenne31 is a non-binary field. -/
instance (priority := low) instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    change ((2 : Nat) : Field) ≠ 0
    intro h
    exact NonBinaryField.char_neq_2 (F := Mersenne31.Basic.Field) (by
      calc
        (2 : Mersenne31.Basic.Field) = toField ((2 : Nat) : Field) := (toField_natCast 2).symm
        _ = toField (0 : Field) := congrArg toField h
        _ = 0 := toField_zero)

end Fast
end Mersenne31
