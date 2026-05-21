/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.BabyBear.Basic
import Mathlib.Algebra.Field.TransferInstance

/-!
# Fast BabyBear Field Operations

This module provides a native-word implementation of BabyBear arithmetic as a sidecar
to the canonical `BabyBear.Field := ZMod BabyBear.fieldSize` model.

Elements are stored as canonical `UInt32` residues below `BabyBear.fieldSize`.
Addition, subtraction, negation, and multiplication use fixed-size words and reduce
through a native `UInt64` remainder before returning to the canonical representation.
-/

namespace BabyBear
namespace Fast

/-- BabyBear modulus as a native word. -/
def modulus : UInt32 := 0x78000001

/-- BabyBear modulus as a 64-bit word for modular reduction. -/
def modulus64 : UInt64 := 0x78000001

/-- `2^32 mod BabyBear.fieldSize`. Kept for compatibility with Montgomery-oriented callers. -/
def rModModulus : UInt32 := 0x0FFFFFFE

/-- `(2^32)^2 mod BabyBear.fieldSize`. Kept for compatibility with Montgomery-oriented callers. -/
def r2ModModulus : UInt32 := 0x45DDDDE3

/-- `-BabyBear.fieldSize⁻¹ mod 2^32`. Kept for compatibility with Montgomery-oriented callers. -/
def montgomeryNegInv : UInt32 := 0x77FFFFFF

/-- A native-word BabyBear element stored as a canonical residue. -/
abbrev Element : Type := { x : UInt32 // x.toNat < BabyBear.fieldSize }

instance : DecidableEq Element := inferInstance

/-- The raw canonical word backing a fast BabyBear element. -/
@[inline]
def raw (x : Element) : UInt32 := x.val

@[simp] theorem modulus_toNat : modulus.toNat = BabyBear.fieldSize := by
  decide

@[simp] theorem modulus64_toNat : modulus64.toNat = BabyBear.fieldSize := by
  decide

private theorem fieldSize_pos : 0 < BabyBear.fieldSize := by
  decide

private theorem fieldSize_lt_uint32Size : BabyBear.fieldSize < UInt32.size := by
  decide

private theorem fieldSize_add_fieldSize_lt_two64 :
    BabyBear.fieldSize + BabyBear.fieldSize < 2 ^ 64 := by
  decide

private theorem fieldSize_mul_fieldSize_lt_two64 :
    BabyBear.fieldSize * BabyBear.fieldSize < 2 ^ 64 := by
  decide

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) : Element :=
  ⟨UInt32.ofNat n, by
    rw [UInt32.toNat_ofNat_of_lt' (Nat.lt_trans h fieldSize_lt_uint32Size)]
    exact h⟩

/-- Reduce a `UInt64` modulo the BabyBear prime and return a canonical fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Element :=
  ⟨(x % modulus64).toUInt32, by
    have hmod : (x % modulus64).toNat < BabyBear.fieldSize := by
      rw [UInt64.toNat_mod, modulus64_toNat]
      exact Nat.mod_lt _ fieldSize_pos
    rw [UInt64.toNat_toUInt32]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hmod fieldSize_lt_uint32Size)]
    exact hmod⟩

/--
Compatibility alias for the previous reducer name.

The fast representation is canonical rather than Montgomery, so this computes ordinary
reduction modulo `BabyBear.fieldSize`.
-/
@[inline]
def montgomeryReduce (x : UInt64) : Element :=
  reduceUInt64 x

/-- The zero fast BabyBear element. -/
def zero : Element := ofCanonicalNat 0 fieldSize_pos

/-- The one fast BabyBear element. -/
def one : Element := ofCanonicalNat 1 (by decide)

/-- Convert a natural number into fast canonical representation. -/
@[inline]
def ofNat (n : Nat) : Element :=
  ofCanonicalNat (n % BabyBear.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 32-bit word into fast canonical representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Element :=
  reduceUInt64 x.toUInt64

/-- Convert from the canonical `ZMod` BabyBear field into fast canonical form. -/
@[inline]
def ofField (x : BabyBear.Field) : Element :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast canonical representation. -/
@[inline]
def ofInt (n : Int) : Element :=
  ofField (n : BabyBear.Field)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : Element) : UInt32 :=
  raw x

/-- Convert a fast BabyBear element to its canonical natural representative. -/
@[inline]
def toNat (x : Element) : Nat :=
  x.val.toNat

/-- Convert a fast BabyBear element to the canonical `ZMod` BabyBear field. -/
@[inline]
def toField (x : Element) : BabyBear.Field :=
  (toNat x : BabyBear.Field)

@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  simp [toNat, ofCanonicalNat, UInt32.toNat_ofNat_of_lt'
    (Nat.lt_trans h fieldSize_lt_uint32Size)]

@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : BabyBear.Field) := by
  simp [toField]

@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 x) = x.toNat % BabyBear.fieldSize := by
  unfold reduceUInt64 toNat
  rw [UInt64.toNat_toUInt32, UInt64.toNat_mod, modulus64_toNat]
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans (Nat.mod_lt _ fieldSize_pos) fieldSize_lt_uint32Size)

@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 x) = (x.toNat : BabyBear.Field) := by
  simp [toField, BabyBear.Field]

private theorem toNat_addUInt64 (x y : Element) :
    (x.val.toUInt64 + y.val.toUInt64).toNat = x.val.toNat + y.val.toNat := by
  rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  rw [Nat.mod_eq_of_lt]
  have hx := x.property
  have hy := y.property
  have hbound := fieldSize_add_fieldSize_lt_two64
  omega

private theorem toNat_subUInt64 (x y : Element) :
    (x.val.toUInt64 + modulus64 - y.val.toUInt64).toNat =
      x.val.toNat + BabyBear.fieldSize - y.val.toNat := by
  have hadd :
      (x.val.toUInt64 + modulus64).toNat = x.val.toNat + BabyBear.fieldSize := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, modulus64_toNat]
    rw [Nat.mod_eq_of_lt]
    have hx := x.property
    have hbound := fieldSize_add_fieldSize_lt_two64
    omega
  have hle : y.val.toUInt64 ≤ x.val.toUInt64 + modulus64 := by
    rw [UInt64.le_iff_toNat_le, hadd, UInt32.toNat_toUInt64]
    have hx := x.property
    have hy := y.property
    omega
  rw [UInt64.toNat_sub_of_le _ _ hle, hadd, UInt32.toNat_toUInt64]

private theorem toNat_negUInt64 (x : Element) :
    (modulus64 - x.val.toUInt64).toNat = BabyBear.fieldSize - x.val.toNat := by
  have hle : x.val.toUInt64 ≤ modulus64 := by
    rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64, modulus64_toNat]
    exact Nat.le_of_lt x.property
  rw [UInt64.toNat_sub_of_le _ _ hle, modulus64_toNat, UInt32.toNat_toUInt64]

private theorem toNat_mulUInt64 (x y : Element) :
    (x.val.toUInt64 * y.val.toUInt64).toNat = x.val.toNat * y.val.toNat := by
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  rw [Nat.mod_eq_of_lt]
  have hx := x.property
  have hy := y.property
  have hbound := fieldSize_mul_fieldSize_lt_two64
  nlinarith

/-- Fast modular addition in canonical form. -/
@[inline]
def add (x y : Element) : Element :=
  reduceUInt64 (x.val.toUInt64 + y.val.toUInt64)

/-- Fast modular negation in canonical form. -/
@[inline]
def neg (x : Element) : Element :=
  reduceUInt64 (modulus64 - x.val.toUInt64)

/-- Fast modular subtraction in canonical form. -/
@[inline]
def sub (x y : Element) : Element :=
  reduceUInt64 (x.val.toUInt64 + modulus64 - y.val.toUInt64)

/-- Fast modular multiplication in canonical form. -/
@[inline]
def mul (x y : Element) : Element :=
  reduceUInt64 (x.val.toUInt64 * y.val.toUInt64)

/-- Fast squaring. -/
@[inline]
def square (x : Element) : Element :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : Element) (n : Nat) : Element :=
  @npowBinRec Element ⟨one⟩ ⟨mul⟩ n x

/-- Inversion transported through the canonical `BabyBear.Field` model. -/
@[inline]
def inv (x : Element) : Element :=
  ofField (toField x)⁻¹

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
  pow x n := ofField (toField x ^ n)

instance instNNRatCastElement : NNRatCast Element where
  nnratCast q := ofField (q : BabyBear.Field)

instance instRatCastElement : RatCast Element where
  ratCast q := ofField (q : BabyBear.Field)

instance instNNRatSMulElement : SMul ℚ≥0 Element where
  smul q x := ofField (q • toField x)

instance instRatSMulElement : SMul ℚ Element where
  smul q x := ofField (q • toField x)

@[simp]
theorem toField_ofField (x : BabyBear.Field) : toField (ofField x) = x := by
  simp [ofField, toField]

@[simp]
theorem ofField_toField (x : Element) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat.inj
  change (UInt32.ofNat (ZMod.val (toField x))).toNat = x.val.toNat
  have hval : ZMod.val (toField x) = x.val.toNat := by
    unfold toField toNat
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.property]
  rw [hval]
  exact UInt32.toNat_ofNat_of_lt' (Nat.lt_trans x.property fieldSize_lt_uint32Size)

theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

@[simp]
theorem toField_zero : toField (0 : Element) = 0 := by
  change toField zero = 0
  simp [zero]

@[simp]
theorem toField_one : toField (1 : Element) = 1 := by
  change toField one = 1
  simp [one]

@[simp]
theorem toField_add (x y : Element) : toField (x + y) = toField x + toField y := by
  change toField (add x y) = toField x + toField y
  unfold add
  rw [toField_reduceUInt64, toNat_addUInt64]
  simp [toField, toNat, Nat.cast_add]

@[simp]
theorem toField_sub (x y : Element) : toField (x - y) = toField x - toField y := by
  change toField (sub x y) = toField x - toField y
  unfold sub
  rw [toField_reduceUInt64, toNat_subUInt64]
  change ((x.val.toNat + BabyBear.fieldSize - y.val.toNat : Nat) : BabyBear.Field) =
    (x.val.toNat : BabyBear.Field) - (y.val.toNat : BabyBear.Field)
  apply eq_sub_of_add_eq
  rw [← Nat.cast_add]
  have hy_le : y.val.toNat ≤ x.val.toNat + BabyBear.fieldSize := by
    have hx := x.property
    have hy := y.property
    omega
  rw [Nat.sub_add_cancel hy_le]
  simp [BabyBear.Field]

@[simp]
theorem toField_neg (x : Element) : toField (-x) = -toField x := by
  change toField (neg x) = -toField x
  unfold neg
  rw [toField_reduceUInt64, toNat_negUInt64]
  change ((BabyBear.fieldSize - x.val.toNat : Nat) : BabyBear.Field) =
    -(x.val.toNat : BabyBear.Field)
  apply eq_neg_of_add_eq_zero_left
  rw [← Nat.cast_add]
  rw [Nat.sub_add_cancel (Nat.le_of_lt x.property)]
  simp [BabyBear.Field]

@[simp]
theorem toField_mul (x y : Element) : toField (x * y) = toField x * toField y := by
  change toField (mul x y) = toField x * toField y
  unfold mul
  rw [toField_reduceUInt64, toNat_mulUInt64]
  simp [toField, toNat, Nat.cast_mul]

private theorem mul_assoc_element (x y z : Element) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  simp only [toField_mul]
  ring

private theorem pow_succ (x : Element) (n : Nat) : pow x (n + 1) = pow x n * x := by
  letI : Semigroup Element := {
    mul_assoc := mul_assoc_element
  }
  unfold pow
  rw [npowBinRec_succ]

@[simp]
theorem toField_square (x : Element) : toField (square x) = toField x * toField x := by
  unfold square
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

@[simp]
theorem toField_pow (x : Element) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      change toField one = (1 : BabyBear.Field)
      simp [one]
  | succ n ih =>
      rw [BabyBear.Fast.pow_succ, toField_mul, ih, _root_.pow_succ]

@[simp]
theorem toField_inv (x : Element) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  simp [inv]

@[simp]
theorem toField_div (x y : Element) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  unfold div
  change toField (x * inv y) = toField x / toField y
  rw [toField_mul]
  rw [show toField (inv y) = (toField y)⁻¹ by
    change toField y⁻¹ = (toField y)⁻¹
    exact toField_inv y]
  rfl

@[simp]
theorem toField_natCast (n : Nat) : toField (n : Element) = (n : BabyBear.Field) := by
  change toField (ofNat n) = (n : BabyBear.Field)
  simp [ofNat, toField, BabyBear.Field]

@[simp]
theorem toField_intCast (n : Int) : toField (n : Element) = (n : BabyBear.Field) := by
  change toField (ofInt n) = (n : BabyBear.Field)
  simp [ofInt]

@[simp]
theorem toField_nsmul (n : Nat) (x : Element) : toField (n • x) = n • toField x := by
  change toField (ofNat n * x) = n • toField x
  change toField ((n : Element) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  simp

@[simp]
theorem toField_zsmul (n : Int) (x : Element) : toField (n • x) = n • toField x := by
  change toField (ofInt n * x) = n • toField x
  change toField ((n : Element) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  simp

@[simp]
theorem toField_npow (x : Element) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  exact toField_pow x n

@[simp]
theorem toField_zpow (x : Element) (n : Int) : toField (x ^ n) = toField x ^ n := by
  change toField (ofField (toField x ^ n)) = toField x ^ n
  simp

@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Element) = (q : BabyBear.Field) := by
  change toField (ofField (q : BabyBear.Field)) = (q : BabyBear.Field)
  simp

@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Element) = (q : BabyBear.Field) := by
  change toField (ofField (q : BabyBear.Field)) = (q : BabyBear.Field)
  simp

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Element) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  simp

@[simp]
theorem toField_qsmul (q : ℚ) (x : Element) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  simp

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
    exact NonBinaryField.char_neq_2 (F := BabyBear.Field) (by
      calc
        (2 : BabyBear.Field) = toField ((2 : Nat) : Element) := (toField_natCast 2).symm
        _ = toField (0 : Element) := congrArg toField h
        _ = 0 := toField_zero)

end Fast
end BabyBear
