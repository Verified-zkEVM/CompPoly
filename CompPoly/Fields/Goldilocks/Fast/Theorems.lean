/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast.Arithmetic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Correctness Theorems for Fast Goldilocks Arithmetic

This module proves that the fast `UInt64` operations agree with the canonical
`ZMod` Goldilocks field.
-/

namespace Goldilocks
namespace Fast

/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
private theorem toField_ofCanonicalNat (n : Nat) (h : n < Goldilocks.Basic.fieldSize) :
    toField (ofCanonicalNat n h) = (n : Goldilocks.Basic.Field) := by
  unfold toField toNat ofCanonicalNat
  have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
  rw [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by simpa [UInt64.size] using hn)]

/-- Converting a canonical natural representative to fast form and reading it back is
the identity. -/
@[simp]
private theorem toNat_ofCanonicalNat (n : Nat) (h : n < Goldilocks.Basic.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  unfold toNat ofCanonicalNat
  have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using hn)

/-- Converting a natural number to fast form agrees with the same natural cast in the
canonical field. -/
@[simp]
theorem toField_ofNat (n : Nat) :
    toField (ofNat n) = (n : Goldilocks.Basic.Field) := by
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [← ZMod.natCast_zmod_val (n : Goldilocks.Basic.Field)]
  rw [ZMod.val_natCast]

/-- Converting a `UInt64` to fast form agrees with casting its natural value into the
canonical field. -/
@[simp]
theorem toField_ofUInt64 (x : UInt64) :
    toField (ofUInt64 x) = (x.toNat : Goldilocks.Basic.Field) := by
  unfold toField toNat ofUInt64
  exact reduceUInt64_cast x

/-- Converting an integer to fast form agrees with casting it into the canonical field. -/
@[simp]
theorem toField_ofInt (z : Int) :
    toField (ofInt z) = (z : Goldilocks.Basic.Field) := by
  unfold ofInt ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val (z : Goldilocks.Basic.Field)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : Goldilocks.Basic.Field) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  change toNat (ofField (toField x)) = toNat x
  unfold ofField toField
  rw [toNat_ofCanonicalNat]
  exact ZMod.val_natCast_of_lt x.property

/-- The canonical-field interpretation distinguishes fast Goldilocks values. -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- Fermat-style inversion in the canonical Goldilocks field. -/
private lemma canonical_inv_eq_pow (a : Goldilocks.Basic.Field) (ha : a ≠ 0) :
    a⁻¹ = a ^ (Goldilocks.Basic.fieldSize - 2) := by
  have hcard : Fintype.card Goldilocks.Basic.Field = Goldilocks.Basic.fieldSize :=
    ZMod.card Goldilocks.Basic.fieldSize
  have h1 : a ^ (Goldilocks.Basic.fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h
    exact h
  have hmul : a * a ^ (Goldilocks.Basic.fieldSize - 2) = 1 := by
    rw [← pow_succ']
    show a ^ (Goldilocks.Basic.fieldSize - 2 + 1) = 1
    have : Goldilocks.Basic.fieldSize - 2 + 1 = Goldilocks.Basic.fieldSize - 1 := by
      unfold Goldilocks.Basic.fieldSize
      omega
    rw [this]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Fast zero maps to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by
  decide

/-- Fast one maps to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by
  decide

/-- Fast addition agrees with canonical-field addition. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y := by
  change
    (((add x y).val.toNat : Goldilocks.Basic.Field) =
      (x.val.toNat : Goldilocks.Basic.Field) + (y.val.toNat : Goldilocks.Basic.Field))
  unfold add
  rw [Reduction.reduceAddWithCarryRaw_cast _ _
    (Reduction.addWithCarry_bound x.val y.val x.property y.property)]
  let lo := x.val + y.val
  let carry := decide (lo < x.val)
  have hvalue := Reduction.addWithCarry_value x.val y.val
  change lo.toNat + (if carry then UInt64.size else 0) = x.val.toNat + y.val.toNat at hvalue
  change
    ((lo.toNat : Goldilocks.Basic.Field) +
        (if carry then (UInt64.size : Goldilocks.Basic.Field) else 0) =
      (x.val.toNat : Goldilocks.Basic.Field) + (y.val.toNat : Goldilocks.Basic.Field))
  by_cases hcarry : carry = true
  · simp only [hcarry, if_true] at hvalue ⊢
    rw [← Nat.cast_add, hvalue, Nat.cast_add]
  · simp only [hcarry, Bool.false_eq_true, if_false, add_zero] at hvalue ⊢
    rw [hvalue, Nat.cast_add]

/-- Fast negation agrees with canonical-field negation. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x := by
  change toField (neg x) = -(toField x)
  unfold neg toField toNat
  exact Reduction.negRaw_cast x.val x.property

/-- Fast subtraction agrees with canonical-field subtraction. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y := by
  change toField (sub x y) = toField x - toField y
  unfold sub toField toNat
  exact Reduction.subRaw_cast x.val y.val x.property y.property

/-- Fast multiplication agrees with canonical-field multiplication. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y := by
  change toField (mul x y) = toField x * toField y
  unfold mul toField toNat
  exact Reduction.reduceMulRaw_cast x.val y.val

/-- The named fast multiplication function agrees with canonical-field multiplication. -/
@[simp]
theorem toField_mul_def (x y : Field) : toField (mul x y) = toField x * toField y :=
  toField_mul x y

/-- Fast squaring agrees with multiplying the canonical field value by itself. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

/-- Repeated fast squaring agrees with raising to `2^n` in the canonical field. -/
@[simp]
theorem toField_squareN (x : Field) (n : Nat) :
    toField (squareN x n) = toField x ^ (2 ^ n) := by
  induction n generalizing x with
  | zero =>
      unfold squareN
      simp
  | succ n ih =>
      unfold squareN
      rw [toField_square, ih]
      rw [← pow_add]
      congr 1
      rw [Nat.pow_succ]
      omega

/-- Fast multiplication is associative, proved by transporting to the canonical field. -/
private theorem mul_assoc_field (x y z : Field) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

/-- Binary exponentiation satisfies the expected successor equation. -/
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

/-- The optimized inversion chain computes the Fermat inverse exponent. -/
private theorem toField_inv_chain (x : Field) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv
  simp only [toField_mul_def, toField_square, toField_squareN]
  ring_nf
  simp [invExponent, Goldilocks.Basic.fieldSize]

/-- Fast inversion agrees with canonical inversion before notation is unfolded. -/
private theorem toField_inv_raw (x : Field) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_chain]
  by_cases hx : toField x = 0
  · rw [hx]
    simp [invExponent, Goldilocks.Basic.fieldSize]
  · simpa [invExponent] using (canonical_inv_eq_pow (toField x) hx).symm

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

/-- Division is multiplication by inverse at the level of canonical interpretation. -/
private theorem toField_div_mul_inv (x y : Field) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  change toField (x * inv y) = toField x * toField (inv y)
  exact toField_mul x (inv y)

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  rw [toField_div_mul_inv, toField_inv_raw y]
  rfl

/-- Natural casts in the fast field agree with natural casts in the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : Field) = (n : Goldilocks.Basic.Field) := by
  change toField (ofNat n) = (n : Goldilocks.Basic.Field)
  rw [toField_ofNat]

/-- Integer casts in the fast field agree with integer casts in the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : Field) = (n : Goldilocks.Basic.Field) := by
  change toField (ofInt n) = (n : Goldilocks.Basic.Field)
  rw [toField_ofInt]

/-- Fast natural scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

/-- Fast integer scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

/-- Standard fast natural powers agree with powers in the canonical field. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Standard fast integer powers agree with integer powers in the canonical field. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := toField_inv_raw x
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

/-- Nonnegative rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : Goldilocks.Basic.Field) := by
  change toField (ofField (q : Goldilocks.Basic.Field)) = (q : Goldilocks.Basic.Field)
  rw [toField_ofField]

/-- Rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : Goldilocks.Basic.Field) := by
  change toField (ofField (q : Goldilocks.Basic.Field)) = (q : Goldilocks.Basic.Field)
  rw [toField_ofField]

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


end Fast
end Goldilocks
