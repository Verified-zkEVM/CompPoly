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

Elements are stored as Montgomery `UInt32` residues below `BabyBear.fieldSize`,
representing `x * 2^32` modulo the BabyBear prime. Addition, subtraction, and
negation operate directly on Montgomery words; multiplication uses Montgomery
reduction on a native `UInt64` product.
-/

namespace BabyBear
namespace Fast

/-- BabyBear modulus as a native word. -/
def modulus : UInt32 := 0x78000001

/-- BabyBear modulus as a 64-bit word for modular reduction. -/
def modulus64 : UInt64 := 0x78000001

/-- `2^32 mod BabyBear.fieldSize`. This is the Montgomery representation of one. -/
def rModModulus : UInt32 := 0x0FFFFFFE

/-- `(2^32)^2 mod BabyBear.fieldSize`, used to enter Montgomery representation. -/
def r2ModModulus : UInt32 := 0x45DDDDE3

/-- `-BabyBear.fieldSize⁻¹ mod 2^32`, used by Montgomery reduction. -/
def montgomeryNegInv : UInt32 := 0x77FFFFFF

/-- A native-word BabyBear element stored as a Montgomery residue. -/
abbrev Element : Type := { x : UInt32 // x.toNat < BabyBear.fieldSize }

instance : DecidableEq Element := inferInstance

/-- The raw Montgomery word backing a fast BabyBear element. -/
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

private theorem uint32Size_lt_three_fieldSize :
    UInt32.size < BabyBear.fieldSize + BabyBear.fieldSize + BabyBear.fieldSize := by
  decide

/-- Reduce a native word below `2^32` modulo the BabyBear prime. -/
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

/-- Montgomery reduction of a bounded 64-bit product. -/
@[inline]
def montgomeryReduce (x : UInt64) : Element :=
  let m : UInt32 := x.toUInt32 * montgomeryNegInv
  let u : UInt32 := ((x + m.toUInt64 * modulus64) >>> 32).toUInt32
  reduceUInt32 u

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (_h : n < BabyBear.fieldSize) : Element :=
  montgomeryReduce (UInt64.ofNat n * r2ModModulus.toUInt64)

/-- Reduce a `UInt64` modulo the BabyBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Element :=
  let y := x % modulus64
  montgomeryReduce (y * r2ModModulus.toUInt64)

/-- The zero fast BabyBear element. -/
def zero : Element := ⟨0, by decide⟩

/-- The one fast BabyBear element. -/
def one : Element := ⟨rModModulus, by decide⟩

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (n : Nat) : Element :=
  ofCanonicalNat (n % BabyBear.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Element :=
  reduceUInt64 x.toUInt64

/-- Convert from the canonical `ZMod` BabyBear field into fast Montgomery form. -/
@[inline]
def ofField (x : BabyBear.Field) : Element :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (n : Int) : Element :=
  ofField (n : BabyBear.Field)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : Element) : UInt32 :=
  raw (montgomeryReduce x.val.toUInt64)

/-- Convert a fast BabyBear element to its canonical natural representative. -/
@[inline]
def toNat (x : Element) : Nat :=
  (toCanonicalUInt32 x).toNat

/-- Convert a fast BabyBear element to the canonical `ZMod` BabyBear field. -/
@[inline]
def toField (x : Element) : BabyBear.Field :=
  (toNat x : BabyBear.Field)

@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  sorry

@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : BabyBear.Field) := by
  sorry

@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 x) = x.toNat % BabyBear.fieldSize := by
  sorry

@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 x) = (x.toNat : BabyBear.Field) := by
  sorry

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : Element) : Element :=
  reduceUInt32 (x.val + y.val)

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : Element) : Element :=
  reduceUInt32 (modulus - x.val)

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : Element) : Element :=
  reduceUInt32 (x.val + modulus - y.val)

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : Element) : Element :=
  montgomeryReduce (x.val.toUInt64 * y.val.toUInt64)

/-- Fast squaring. -/
@[inline]
def square (x : Element) : Element :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : Element) (n : Nat) : Element :=
  @npowBinRec Element ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the BabyBear prime field. -/
def invExponent : Nat := BabyBear.fieldSize - 2

/-- Inversion in Montgomery form by Fermat exponentiation. -/
@[inline]
def inv (x : Element) : Element :=
  pow x invExponent

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
  nnratCast q := ofField (q : BabyBear.Field)

instance instRatCastElement : RatCast Element where
  ratCast q := ofField (q : BabyBear.Field)

instance instNNRatSMulElement : SMul ℚ≥0 Element where
  smul q x := ofField (q • toField x)

instance instRatSMulElement : SMul ℚ Element where
  smul q x := ofField (q • toField x)

@[simp]
theorem toField_ofField (x : BabyBear.Field) : toField (ofField x) = x := by
  sorry

@[simp]
theorem ofField_toField (x : Element) : ofField (toField x) = x := by
  sorry

theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

@[simp]
theorem toField_zero : toField (0 : Element) = 0 := by
  sorry

@[simp]
theorem toField_one : toField (1 : Element) = 1 := by
  sorry

@[simp]
theorem toField_add (x y : Element) : toField (x + y) = toField x + toField y := by
  sorry

@[simp]
theorem toField_sub (x y : Element) : toField (x - y) = toField x - toField y := by
  sorry

@[simp]
theorem toField_neg (x : Element) : toField (-x) = -toField x := by
  sorry

@[simp]
theorem toField_mul (x y : Element) : toField (x * y) = toField x * toField y := by
  sorry

private theorem mul_assoc_element (x y z : Element) : (x * y) * z = x * (y * z) := by
  sorry

private theorem pow_succ (x : Element) (n : Nat) : pow x (n + 1) = pow x n * x := by
  sorry

@[simp]
theorem toField_square (x : Element) : toField (square x) = toField x * toField x := by
  sorry

@[simp]
theorem toField_pow (x : Element) (n : Nat) : toField (pow x n) = toField x ^ n := by
  sorry

@[simp]
theorem toField_inv (x : Element) : toField x⁻¹ = (toField x)⁻¹ := by
  sorry

@[simp]
theorem toField_div (x y : Element) : toField (x / y) = toField x / toField y := by
  sorry

@[simp]
theorem toField_natCast (n : Nat) : toField (n : Element) = (n : BabyBear.Field) := by
  sorry

@[simp]
theorem toField_intCast (n : Int) : toField (n : Element) = (n : BabyBear.Field) := by
  sorry

@[simp]
theorem toField_nsmul (n : Nat) (x : Element) : toField (n • x) = n • toField x := by
  sorry

@[simp]
theorem toField_zsmul (n : Int) (x : Element) : toField (n • x) = n • toField x := by
  sorry

@[simp]
theorem toField_npow (x : Element) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  sorry

@[simp]
theorem toField_zpow (x : Element) (n : Int) : toField (x ^ n) = toField x ^ n := by
  sorry

@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Element) = (q : BabyBear.Field) := by
  sorry

@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Element) = (q : BabyBear.Field) := by
  sorry

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Element) : toField (q • x) = q • toField x := by
  sorry

@[simp]
theorem toField_qsmul (q : ℚ) (x : Element) : toField (q • x) = q • toField x := by
  sorry

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
