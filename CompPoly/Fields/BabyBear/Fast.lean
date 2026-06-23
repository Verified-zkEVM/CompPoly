/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Convert
import Mathlib.Algebra.Field.TransferInstance

/-!
# Fast BabyBear Field Operations

This module provides a native-word implementation of BabyBear arithmetic as a sidecar
to the canonical `BabyBear.Field := ZMod BabyBear.fieldSize` model.

Fast field values are stored as Montgomery `UInt32` residues below `BabyBear.fieldSize`,
representing `x * 2^32` modulo the BabyBear prime. Addition, subtraction, and
negation operate directly on Montgomery words; multiplication uses Montgomery
reduction on a native `UInt64` product.

Supporting layers live in sibling modules: field basics in
`CompPoly.Fields.BabyBear.Fast.Prelude`, Montgomery reduction in
`CompPoly.Fields.BabyBear.Fast.Montgomery`, and conversions/casts in
`CompPoly.Fields.BabyBear.Fast.Convert`. This module defines the field operations,
their instances, and the `toField` bridge to `BabyBear.Field`.
-/

namespace BabyBear
namespace Fast

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : Field) : Field :=
  reduceUInt32Lt2Modulus (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega))

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : Field) : Field :=
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
def sub (x y : Field) : Field :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt32.toNat_sub_of_le _ _ hyx]
      omega⟩
  else
    ⟨x.val + modulus - y.val, by
      have hsum_lt : x.val.toNat + BabyBear.fieldSize < UInt32.size := by
        have htwo := fieldSize_add_fieldSize_lt_uint32Size
        omega
      have hsum_eq : (x.val + modulus).toNat = x.val.toNat + BabyBear.fieldSize := by
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
def mul (x y : Field) : Field :=
  montgomeryReduceBounded (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, fieldSize_lt_uint32Size, fieldSize_pos])

/-- Fast squaring. -/
@[inline]
def square (x : Field) : Field :=
  mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : Field) (n : Nat) : Field :=
  @npowBinRec Field ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the BabyBear prime field. -/
def invExponent : Nat := BabyBear.fieldSize - 2

/-- Four squarings followed by multiplication by the next 4-bit exponent digit. -/
@[inline]
private def shift4Mul (acc digit : Field) : Field :=
  mul (square (square (square (square acc)))) digit

/-- Inversion in Montgomery form by a fixed 4-bit Fermat chain. -/
@[inline]
def inv (x : Field) : Field :=
  let x2 := square x
  let x3 := mul x2 x
  let x5 := mul x3 x2
  let x7 := mul x5 x2
  let x14 := square x7
  let x15 := mul x14 x
  let acc := shift4Mul x7 x7
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  let acc := shift4Mul acc x15
  shift4Mul acc x15

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field :=
  mul x (inv y)

instance instZeroField : Zero Field where
  zero := zero

instance instOneField : One Field where
  one := one

instance instAddField : Add Field where
  add := add

instance instNegField : Neg Field where
  neg := neg

instance instSubField : Sub Field where
  sub := sub

instance instMulField : Mul Field where
  mul := mul

instance instInvField : Inv Field where
  inv := inv

instance instDivField : Div Field where
  div := div

instance instNatCastField : NatCast Field where
  natCast := ofNat

instance instIntCastField : IntCast Field where
  intCast := ofInt

instance instNatSMulField : SMul Nat Field where
  smul n x := ofNat n * x

instance instIntSMulField : SMul Int Field where
  smul n x := ofInt n * x

instance instPowFieldNat : Pow Field Nat where
  pow := pow

instance instPowFieldInt : Pow Field Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance instNNRatCastField : NNRatCast Field where
  nnratCast q := ofField (q : BabyBear.Field)

instance instRatCastField : RatCast Field where
  ratCast q := ofField (q : BabyBear.Field)

instance instNNRatSMulField : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

instance instRatSMulField : SMul ℚ Field where
  smul q x := ofField (q • toField x)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : BabyBear.Field) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  apply nat_eq_of_field_eq
  · exact (ofField (toField x)).property
  · exact x.property
  · rw [raw_cast_eq_toField_mul]
    rw [toField_ofField]
    rw [raw_cast_eq_toField_mul]

/-- The canonical-field interpretation distinguishes fast BabyBear values. -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by
  rw [toField_eq_raw_mul_inv]
  change ((0 : Nat) : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ = 0
  exact zero_mul _

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (rModModulus.toNat : BabyBear.Field) *
      (UInt32.size : BabyBear.Field)⁻¹ = 1
  rw [rModModulus_cast]
  exact mul_inv_cancel₀ uint32Size_ne_zero_in_field

/-- Fast addition agrees with addition in the canonical BabyBear field. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instAddField add
  have hred := reduceUInt32Lt2Modulus_cast (x.val + y.val) (by
    rw [UInt32.toNat_add]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega))
  change ((reduceUInt32Lt2ModulusRaw (x.val + y.val)).toNat : BabyBear.Field) =
      ((x.val + y.val).toNat : BabyBear.Field) at hred
  change ((reduceUInt32Lt2ModulusRaw (x.val + y.val)).toNat : BabyBear.Field) *
      (UInt32.size : BabyBear.Field)⁻¹ =
        (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ +
          (y.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
  rw [hred]
  rw [UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < UInt32.size := by
    nlinarith [x.property, y.property, fieldSize_add_fieldSize_lt_uint32Size]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.cast_add]
  ring

/-- Fast subtraction agrees with subtraction in the canonical BabyBear field. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hsubval : (x - y : Field).val = x.val - y.val := by
      change (sub x y).val = x.val - y.val
      unfold sub
      rw [dif_pos hyx]
    rw [hsubval]
    change (((x.val - y.val).toNat : BabyBear.Field) *
        (UInt32.size : BabyBear.Field)⁻¹) =
        (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ -
          (y.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyx]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hyx
      exact hyx)]
    ring
  · have hsum_lt : x.val.toNat + BabyBear.fieldSize < UInt32.size := by
      have htwo := fieldSize_add_fieldSize_lt_uint32Size
      omega
    have hsum_eq : (x.val + modulus).toNat = x.val.toNat + BabyBear.fieldSize := by
      rw [UInt32.toNat_add, modulus_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hyle : y.val ≤ x.val + modulus := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      omega
    have hsubval : (x - y : Field).val = x.val + modulus - y.val := by
      change (sub x y).val = x.val + modulus - y.val
      unfold sub
      rw [dif_neg hyx]
    rw [hsubval]
    change (((x.val + modulus - y.val).toNat : BabyBear.Field) *
        (UInt32.size : BabyBear.Field)⁻¹) =
        (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ -
          (y.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹
    rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, hsum_eq] at hyle
      exact hyle)]
    rw [Nat.cast_add, ZMod.natCast_self]
    ring

/-- Fast negation agrees with negation in the canonical BabyBear field. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegval : (-x : Field).val = zero.val := by
      change (neg x).val = zero.val
      unfold neg
      rw [dif_pos hx]
    rw [hnegval]
    change ((zero.val.toNat : BabyBear.Field) *
        (UInt32.size : BabyBear.Field)⁻¹) =
        -((x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹)
    have hxNat : x.val.toNat = 0 := by
      simpa using congrArg UInt32.toNat hx
    rw [hxNat]
    change ((0 : Nat) : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ =
      -(((0 : Nat) : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹)
    simp
  · have hle : x.val ≤ modulus := by
      rw [UInt32.le_iff_toNat_le, modulus_toNat]
      exact Nat.le_of_lt x.property
    have hnegval : (-x : Field).val = modulus - x.val := by
      change (neg x).val = modulus - x.val
      unfold neg
      rw [dif_neg hx]
    rw [hnegval]
    change (((modulus - x.val).toNat : BabyBear.Field) *
        (UInt32.size : BabyBear.Field)⁻¹) =
        -((x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹)
    rw [UInt32.toNat_sub_of_le _ _ hle, modulus_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, modulus_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    ring

/-- Fast multiplication agrees with multiplication in the canonical BabyBear field. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv, toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  unfold instMulField mul
  have hred := montgomeryReduceBounded_cast (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, fieldSize_lt_uint32Size, fieldSize_pos])
  change ((montgomeryReduceBoundedRaw (x.val.toUInt64 * y.val.toUInt64)).toNat :
      BabyBear.Field) =
        ((x.val.toUInt64 * y.val.toUInt64).toNat : BabyBear.Field) *
          (UInt32.size : BabyBear.Field)⁻¹ at hred
  change ((montgomeryReduceBoundedRaw (x.val.toUInt64 * y.val.toUInt64)).toNat :
      BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ =
        (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ *
          ((y.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹)
  rw [hred]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, fieldSize_mul_fieldSize_lt_two64]
  rw [Nat.mod_eq_of_lt hprod]
  rw [Nat.cast_mul]
  ring

/-- Ring equivalence between the fast Montgomery representation and canonical `BabyBear.Field`. -/
def ringEquiv : Field ≃+* BabyBear.Field where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x := rfl

/-- Applying the inverse `ringEquiv` is conversion into fast Montgomery form. -/
@[simp]
theorem ringEquiv_symm_apply (x : BabyBear.Field) : ringEquiv.symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : Field) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ (x : Field) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup Field := {
    mul := (· * ·)
    mul_assoc := mul_assoc_field
  }
  exact npowBinRec_succ n x

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

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

private theorem toField_mul_pow (base x y : Field) (m n : Nat)
    (hx : toField x = toField base ^ m) (hy : toField y = toField base ^ n) :
    toField (mul x y) = toField base ^ (m + n) := by
  change toField (x * y) = toField base ^ (m + n)
  rw [toField_mul, hx, hy, ← pow_add]

private theorem toField_shift4Mul (acc digit : Field) :
    toField (shift4Mul acc digit) = toField acc ^ 16 * toField digit := by
  unfold shift4Mul
  change toField (square (square (square (square acc))) * digit) =
    toField acc ^ 16 * toField digit
  rw [toField_mul]
  repeat rw [toField_square]
  ring

private theorem toField_shift4Mul_pow (base acc digit : Field) (e d : Nat)
    (hacc : toField acc = toField base ^ e) (hdigit : toField digit = toField base ^ d) :
    toField (shift4Mul acc digit) = toField base ^ (16 * e + d) := by
  rw [toField_shift4Mul, hacc, hdigit]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

private theorem toField_inv_pow (x : Field) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv
  let x2 := square x
  let x3 := mul x2 x
  let x5 := mul x3 x2
  let x7 := mul x5 x2
  let x14 := square x7
  let x15 := mul x14 x
  let acc1 := shift4Mul x7 x7
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
  have hacc1 : toField acc1 = toField x ^ 119 := by
    dsimp [acc1]
    simpa using toField_shift4Mul_pow x x7 x7 7 7 hx7 hx7
  have hacc2 : toField acc2 = toField x ^ 1919 := by
    dsimp [acc2]
    simpa using toField_shift4Mul_pow x acc1 x15 119 15 hacc1 hx15
  have hacc3 : toField acc3 = toField x ^ 30719 := by
    dsimp [acc3]
    simpa using toField_shift4Mul_pow x acc2 x15 1919 15 hacc2 hx15
  have hacc4 : toField acc4 = toField x ^ 491519 := by
    dsimp [acc4]
    simpa using toField_shift4Mul_pow x acc3 x15 30719 15 hacc3 hx15
  have hacc5 : toField acc5 = toField x ^ 7864319 := by
    dsimp [acc5]
    simpa using toField_shift4Mul_pow x acc4 x15 491519 15 hacc4 hx15
  have hacc6 : toField acc6 = toField x ^ 125829119 := by
    dsimp [acc6]
    simpa using toField_shift4Mul_pow x acc5 x15 7864319 15 hacc5 hx15
  have hfinal := toField_shift4Mul_pow x acc6 x15 125829119 15 hacc6 hx15
  simpa [invExponent, BabyBear.fieldSize] using hfinal

private theorem toField_inv_raw (x : Field) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx]
    simp [invExponent, BabyBear.fieldSize]
  · simpa [invExponent] using (BabyBear.inv_eq_pow (toField x) hx).symm

/-- Fast inversion agrees with inversion in the canonical BabyBear field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_mul_raw (x y : Field) : toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

private theorem toField_div_mul_inv (x y : Field) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  exact toField_mul_raw x (inv y)

/-- Fast division agrees with division in the canonical BabyBear field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : BabyBear.Field, c = b⁻¹ → a * c = a / b := by
    intro a b c hc
    rw [hc]
    rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : Field) = (n : BabyBear.Field) := by
  change toField (ofNat n) = (n : BabyBear.Field)
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : Field) = (n : BabyBear.Field) := by
  change toField (ofInt n) = (n : BabyBear.Field)
  unfold ofInt
  rw [toField_ofField]

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n := by
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
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : BabyBear.Field) := by
  change toField (ofField (q : BabyBear.Field)) = (q : BabyBear.Field)
  rw [toField_ofField]

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : BabyBear.Field) := by
  change toField (ofField (q : BabyBear.Field)) = (q : BabyBear.Field)
  rw [toField_ofField]

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Field instance transferred from canonical BabyBear through `toField`. -/
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

/-- Fast BabyBear is a non-binary field. -/
instance (priority := low) instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    change ((2 : Nat) : Field) ≠ 0
    intro h
    exact NonBinaryField.char_neq_2 (F := BabyBear.Field) (by
      calc
        (2 : BabyBear.Field) = toField ((2 : Nat) : Field) := (toField_natCast 2).symm
        _ = toField (0 : Field) := congrArg toField h
        _ = 0 := toField_zero)

end Fast
end BabyBear
