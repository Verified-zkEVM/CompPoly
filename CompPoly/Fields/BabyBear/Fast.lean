/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Convert

/-!
# Fast BabyBear Field Operations

A native-word implementation of BabyBear arithmetic as a sidecar to the canonical
`BabyBear.Field := ZMod BabyBear.fieldSize` model. Fast values are stored as Montgomery
`UInt32` residues below `BabyBear.fieldSize`, representing `x * 2^32` modulo the prime.

The operations, their `Field`/`CommRing`/`NonBinaryField` instances, the `toField` bridge,
and all correctness theorems are shared across every fast 32-bit-word field; they live once
in `CompPoly.Fields.Montgomery.Native32Field`, parameterized by the `Mont32Field` instance
in `CompPoly.Fields.BabyBear.Fast.Prelude`. Because `Field := Native32.FastField BabyBear.Field`,
the generic algebraic instances resolve here automatically. This module re-exports the
named operations and `simp` lemmas at the BabyBear instance.
-/

namespace BabyBear
namespace Fast

open Montgomery.Native32

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : Field) : Field := Montgomery.Native32.add x y

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : Field) : Field := Montgomery.Native32.neg x

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : Field) : Field := Montgomery.Native32.sub x y

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : Field) : Field := Montgomery.Native32.mul x y

/-- Fast squaring. -/
@[inline]
def square (x : Field) : Field := Montgomery.Native32.square x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : Field) (n : Nat) : Field := Montgomery.Native32.pow x n

/-- Fermat exponent used for inversion in the BabyBear prime field. -/
def invExponent : Nat := Montgomery.Native32.invExponent (F := BabyBear.Field)

/-- Inversion in Montgomery form via Fermat's little theorem (`x⁻¹ = x^(p-2)`). -/
@[inline]
def inv (x : Field) : Field := Montgomery.Native32.inv x

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field := Montgomery.Native32.div x y

/-- Ring equivalence between the fast Montgomery representation and canonical `BabyBear.Field`. -/
def ringEquiv : Field ≃+* BabyBear.Field :=
  Montgomery.Native32.ringEquiv (F := BabyBear.Field)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : BabyBear.Field) : toField (ofField x) = x :=
  Montgomery.Native32.toField_ofField (F := BabyBear.Field) x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x :=
  Montgomery.Native32.ofField_toField x

/-- The canonical-field interpretation distinguishes fast BabyBear values. -/
theorem toField_injective : Function.Injective (toField : Field → BabyBear.Field) :=
  Montgomery.Native32.toField_injective (F := BabyBear.Field)

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 :=
  Montgomery.Native32.toField_zero (F := BabyBear.Field)

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 :=
  Montgomery.Native32.toField_one (F := BabyBear.Field)

/-- Fast addition agrees with addition in the canonical BabyBear field. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y :=
  Montgomery.Native32.toField_add x y

/-- Fast subtraction agrees with subtraction in the canonical BabyBear field. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y :=
  Montgomery.Native32.toField_sub x y

/-- Fast negation agrees with negation in the canonical BabyBear field. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x :=
  Montgomery.Native32.toField_neg x

/-- Fast multiplication agrees with multiplication in the canonical BabyBear field. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y :=
  Montgomery.Native32.toField_mul x y

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x :=
  Montgomery.Native32.ringEquiv_apply x

/-- Applying the inverse `ringEquiv` is conversion into fast Montgomery form. -/
@[simp]
theorem ringEquiv_symm_apply (x : BabyBear.Field) : ringEquiv.symm x = ofField x :=
  Montgomery.Native32.ringEquiv_symm_apply (F := BabyBear.Field) x

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x :=
  Montgomery.Native32.toField_square x

/-- Fast inversion agrees with inversion in the canonical BabyBear field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ :=
  Montgomery.Native32.toField_inv x

/-- Fast division agrees with division in the canonical BabyBear field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y :=
  Montgomery.Native32.toField_div x y

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : Field) = (n : BabyBear.Field) :=
  Montgomery.Native32.toField_natCast n

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : Field) = (n : BabyBear.Field) :=
  Montgomery.Native32.toField_intCast n

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) : toField (n • x) = n • toField x :=
  Montgomery.Native32.toField_nsmul n x

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x :=
  Montgomery.Native32.toField_zsmul n x

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native32.toField_npow x n

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native32.toField_zpow x n

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : BabyBear.Field) :=
  Montgomery.Native32.toField_nnratCast q

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : BabyBear.Field) :=
  Montgomery.Native32.toField_ratCast q

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) : toField (q • x) = q • toField x :=
  Montgomery.Native32.toField_nnqsmul q x

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) : toField (q • x) = q • toField x :=
  Montgomery.Native32.toField_qsmul q x

end Fast
end BabyBear
