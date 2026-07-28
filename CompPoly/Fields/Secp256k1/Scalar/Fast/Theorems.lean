/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Secp256k1.Scalar.Fast.Arithmetic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Correctness Theorems for Fast secp256k1 Scalar Field Arithmetic

This module proves that conversion to the canonical scalar field preserves the
fast representation's constructors, arithmetic operations, powers, casts, and
scalar actions. These theorems support the field transfer and ring equivalence.
-/

namespace Secp256k1.Scalar.Fast

/-- Converting `ofNat n` to the canonical scalar field gives the canonical cast of `n`. -/
@[simp]
theorem toField_ofNat (n : Nat) :
    toField (ofNat n) = (n : Secp256k1.Scalar.Basic.Field) := by
  unfold toField toNat ofNat
  exact Repr.ofNat_cast n

/-- Converting a canonical scalar to fast representation and back is the identity. -/
@[simp]
theorem toField_ofField (x : Secp256k1.Scalar.Basic.Field) :
    toField (ofField x) = x := by
  unfold ofField ofNat toField toNat
  rw [Repr.ofNat_cast]
  exact ZMod.natCast_zmod_val x

/-- Converting a fast scalar to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x := by
  apply Subtype.ext
  change Repr.ofNat ((x.val.toNat : Secp256k1.Scalar.Basic.Field).val) = x.val
  rw [ZMod.val_natCast_of_lt x.property]
  exact Repr.ofNat_toNat x.val x.property

/-- Canonical interpretation is injective on fast scalar values. -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- Fast zero maps to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by
  rfl

/-- Fast one maps to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by
  rfl

/-- Fast addition agrees with canonical scalar-field addition. -/
@[simp]
theorem toField_add (x y : Field) :
    toField (x + y) = toField x + toField y := by
  change toField (add x y) = toField x + toField y
  unfold add toField toNat
  exact Reduction.addModRaw_cast
    x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3
    x.property y.property

/-- Fast negation agrees with canonical scalar-field negation. -/
@[simp]
theorem toField_neg (x : Field) :
    toField (-x) = -toField x := by
  change toField (neg x) = -toField x
  unfold neg toField toNat
  exact Reduction.negRaw_cast x.val.d0 x.val.d1 x.val.d2 x.val.d3 x.property

/-- Fast subtraction agrees with canonical scalar-field subtraction. -/
@[simp]
theorem toField_sub (x y : Field) :
    toField (x - y) = toField x - toField y := by
  change toField (sub x y) = toField x - toField y
  unfold sub toField toNat
  exact Reduction.subModRaw_cast
    x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3
    x.property y.property

/-- Fast multiplication agrees with canonical scalar-field multiplication. -/
@[simp]
theorem toField_mul (x y : Field) :
    toField (x * y) = toField x * toField y := by
  change toField (mul x y) = toField x * toField y
  unfold mul toField toNat
  exact Reduction.mulRaw_cast
    x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3

/-- Fast squaring agrees with canonical multiplication by the same value. -/
@[simp]
theorem toField_square (x : Field) :
    toField (square x) = toField x * toField x := by
  unfold square toField toNat
  simpa only [pow_two] using
    Reduction.squareRaw_cast x.val.d0 x.val.d1 x.val.d2 x.val.d3

/-- Fast binary exponentiation agrees with canonical natural exponentiation. -/
@[simp]
theorem toField_pow (x : Field) (n : Nat) :
    toField (pow x n) = toField x ^ n := by
  letI : Semigroup Field := {
    mul_assoc := by
      intro a b c
      apply toField_injective
      rw [toField_mul (a * b) c, toField_mul a b,
        toField_mul a (b * c), toField_mul b c]
      exact mul_assoc (toField a) (toField b) (toField c) }
  induction n with
  | zero =>
      change toField (@npowBinRec Field ⟨one⟩ ⟨mul⟩ 0 x) = _
      rw [npowBinRec_zero, toField_one, pow_zero]
  | succ n ih =>
      change toField (@npowBinRec Field ⟨one⟩ ⟨mul⟩ (n + 1) x) = _
      rw [npowBinRec_succ]
      change toField (pow x n * x) = _
      rw [toField_mul, ih, pow_succ]

/-- Fermat inversion in the canonical secp256k1 scalar field. -/
private theorem pow_card_sub_two_eq_inv (a : Secp256k1.Scalar.Basic.Field) :
    a ^ (Secp256k1.Scalar.Basic.CARD - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst a
    norm_num [Secp256k1.Scalar.Basic.CARD]
  · have hfermat := ZMod.pow_card_sub_one_eq_one ha
    have hexp : Secp256k1.Scalar.Basic.CARD - 2 + 1 =
        Secp256k1.Scalar.Basic.CARD - 1 := by
      norm_num [Secp256k1.Scalar.Basic.CARD]
    calc
      a ^ (Secp256k1.Scalar.Basic.CARD - 2) =
          a ^ (Secp256k1.Scalar.Basic.CARD - 2) * (a * a⁻¹) := by
            rw [mul_inv_cancel₀ ha, mul_one]
      _ = (a ^ (Secp256k1.Scalar.Basic.CARD - 2) * a) * a⁻¹ := by ring
      _ = a ^ (Secp256k1.Scalar.Basic.CARD - 2 + 1) * a⁻¹ := by
            rw [pow_succ]
      _ = a ^ (Secp256k1.Scalar.Basic.CARD - 1) * a⁻¹ := by rw [hexp]
      _ = a⁻¹ := by rw [hfermat, one_mul]

/-- Fermat inversion agrees with inversion in the canonical scalar field. -/
@[simp] theorem toField_invFermat (x : Field) :
    toField (invFermat x) = (toField x)⁻¹ := by
  unfold invFermat
  rw [toField_pow, pow_card_sub_two_eq_inv]

/-- Default fast inversion agrees with inversion in the canonical scalar field. -/
@[simp] theorem toField_inv (x : Field) :
    toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  unfold inv
  exact toField_invFermat x

/-- Fast division agrees with division in the canonical scalar field. -/
@[simp]
theorem toField_div (x y : Field) :
    toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  unfold div
  calc
    toField (mul x (inv y)) = toField x * toField (inv y) :=
      toField_mul x (inv y)
    _ = toField x * (toField y)⁻¹ :=
      congrArg (fun z => toField x * z) (toField_inv y)
    _ = toField x / toField y := by rw [div_eq_mul_inv]

/-- Natural casts into the fast field agree with canonical scalar-field casts. -/
@[simp]
theorem toField_natCast (n : Nat) :
    toField (n : Field) = (n : Secp256k1.Scalar.Basic.Field) := by
  change toField (ofNat n) = (n : Secp256k1.Scalar.Basic.Field)
  rw [toField_ofNat]

/-- Integer casts into the fast field agree with canonical scalar-field casts. -/
@[simp]
theorem toField_intCast (z : Int) :
    toField (z : Field) = (z : Secp256k1.Scalar.Basic.Field) := by
  change toField (ofInt z) = (z : Secp256k1.Scalar.Basic.Field)
  unfold ofInt
  rw [toField_ofField]

/-- Fast natural scalar multiplication agrees with canonical scalar multiplication. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) :
    toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

/-- Fast integer scalar multiplication agrees with canonical scalar multiplication. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) :
    toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

/-- Standard natural powers agree with powers in the canonical scalar field. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) :
    toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  exact toField_pow x n

/-- Standard integer powers agree with powers in the canonical scalar field. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) :
    toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := by
        change toField x⁻¹ = (toField x)⁻¹
        exact toField_inv x
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

/-- Nonnegative rational casts agree with canonical scalar-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) :
    toField (q : Field) = (q : Secp256k1.Scalar.Basic.Field) := by
  change toField (ofField (q : Secp256k1.Scalar.Basic.Field)) = _
  exact toField_ofField _

/-- Rational casts agree with canonical scalar-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) :
    toField (q : Field) = (q : Secp256k1.Scalar.Basic.Field) := by
  change toField (ofField (q : Secp256k1.Scalar.Basic.Field)) = _
  exact toField_ofField _

/-- Fast nonnegative rational scalar multiplication agrees with the canonical operation. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) :
    toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  exact toField_ofField _

/-- Fast rational scalar multiplication agrees with the canonical operation. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) :
    toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  exact toField_ofField _

end Secp256k1.Scalar.Fast
