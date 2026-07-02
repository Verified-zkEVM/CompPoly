/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_377.Fast.Prelude

/-!
# Fast BLS12_377 Scalar Field — operations

A native-word implementation of BLS12_377 scalar arithmetic as a sidecar to the canonical
`BLS12_377.ScalarField := ZMod scalarFieldSize` model. Fast values are stored as 256-bit Montgomery
residues below the prime (`x · 2²⁵⁶ mod p`, four `UInt64` limbs).

The operations, their `Field`/`CommRing`/`NonBinaryField` instances, the `toField` bridge, and
all correctness theorems are shared across every fast 256-bit Montgomery field; they live once
in `CompPoly.Fields.Montgomery.Native256Field`, parameterized by the `Mont256Field` instance in
`CompPoly.Fields.BLS12_377.Fast.Prelude`. Because `ScalarField` is `Native256.FastField` at the
BLS12-377 tag, the generic algebraic instances resolve here automatically. This module re-exports
the named operations and `simp` lemmas at the BLS12-377 instance.
-/

namespace BLS12_377
namespace Fast

open Montgomery.Native256

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : ScalarField) : ScalarField := Montgomery.Native256.add x y

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : ScalarField) : ScalarField := Montgomery.Native256.neg x

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : ScalarField) : ScalarField := Montgomery.Native256.sub x y

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : ScalarField) : ScalarField := Montgomery.Native256.mul x y

/-- Fast squaring. -/
@[inline]
def square (x : ScalarField) : ScalarField := Montgomery.Native256.square x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : ScalarField) (n : Nat) : ScalarField := Montgomery.Native256.pow x n

/-- Fermat exponent used for inversion in the BLS12_377 scalar field. -/
def invExponent : Nat := Montgomery.Native256.invExponent (F := BLS12_377.ScalarField)

/-- Inversion in Montgomery form: Pornin binary GCD over limbs, runtime-verified, with the
proven 4-bit-window Fermat exponentiation as fallback. -/
@[inline]
def inv (x : ScalarField) : ScalarField := Montgomery.Native256.inv x

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : ScalarField) : ScalarField := Montgomery.Native256.div x y

/-- Exit Montgomery form: the canonical native-word representative of a fast element. -/
@[inline]
def toCanonicalUInt256L (x : ScalarField) : UInt256L := Montgomery.Native256.toCanonicalUInt256L x

/-- The canonical natural representative of a fast element. -/
@[inline]
def toNat (x : ScalarField) : Nat := Montgomery.Native256.toNat x

/-- Interpret a fast element in the canonical `BLS12_377.ScalarField` field. -/
@[inline]
def toField (x : ScalarField) : BLS12_377.ScalarField := Montgomery.Native256.toField x

/-- Build a fast element from a natural number (reducing modulo the prime). -/
@[inline]
def ofNat (n : Nat) : ScalarField := Montgomery.Native256.ofNat n

/-- Convert from the canonical `BLS12_377.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_377.ScalarField) : ScalarField :=
  Montgomery.Native256.ofField (F := BLS12_377.ScalarField) x

/-- Ring equivalence between the fast representation and the canonical `BLS12_377.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_377.ScalarField :=
  Montgomery.Native256.ringEquiv (F := BLS12_377.ScalarField)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : BLS12_377.ScalarField) : toField (ofField x) = x :=
  Montgomery.Native256.toField_ofField (F := BLS12_377.ScalarField) x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : ScalarField) : ofField (toField x) = x :=
  Montgomery.Native256.ofField_toField x

/-- The canonical-field interpretation distinguishes fast BLS12_377 values. -/
theorem toField_injective : Function.Injective (toField : ScalarField → BLS12_377.ScalarField) :=
  Montgomery.Native256.toField_injective

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : ScalarField) = 0 :=
  Montgomery.Native256.toField_zero (F := BLS12_377.ScalarField)

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : ScalarField) = 1 :=
  Montgomery.Native256.toField_one (F := BLS12_377.ScalarField)

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : ScalarField) : toField (x + y) = toField x + toField y :=
  Montgomery.Native256.toField_add x y

/-- Fast subtraction agrees with subtraction in the canonical field. -/
@[simp]
theorem toField_sub (x y : ScalarField) : toField (x - y) = toField x - toField y :=
  Montgomery.Native256.toField_sub x y

/-- Fast negation agrees with negation in the canonical field. -/
@[simp]
theorem toField_neg (x : ScalarField) : toField (-x) = -toField x :=
  Montgomery.Native256.toField_neg x

/-- Fast multiplication agrees with multiplication in the canonical field. -/
@[simp]
theorem toField_mul (x y : ScalarField) : toField (x * y) = toField x * toField y :=
  Montgomery.Native256.toField_mul x y

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : ScalarField) : ringEquiv x = toField x := rfl

/-- Applying the inverse `ringEquiv` is conversion into fast Montgomery form. -/
@[simp]
theorem ringEquiv_symm_apply (x : BLS12_377.ScalarField) : ringEquiv.symm x = ofField x := rfl

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : ScalarField) : toField (square x) = toField x * toField x :=
  Montgomery.Native256.toField_square x

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : ScalarField) : toField x⁻¹ = (toField x)⁻¹ :=
  Montgomery.Native256.toField_inv x

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : ScalarField) : toField (x / y) = toField x / toField y :=
  Montgomery.Native256.toField_div x y

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : ScalarField) = (n : BLS12_377.ScalarField) :=
  Montgomery.Native256.toField_natCast n

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : ScalarField) = (n : BLS12_377.ScalarField) :=
  Montgomery.Native256.toField_intCast n

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : ScalarField) : toField (n • x) = n • toField x :=
  Montgomery.Native256.toField_nsmul n x

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : ScalarField) : toField (n • x) = n • toField x :=
  Montgomery.Native256.toField_zsmul n x

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : ScalarField) (n : Nat) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native256.toField_npow x n

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : ScalarField) (n : Int) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native256.toField_zpow x n

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : ScalarField) = (q : BLS12_377.ScalarField) :=
  Montgomery.Native256.toField_nnratCast q

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : ScalarField) = (q : BLS12_377.ScalarField) :=
  Montgomery.Native256.toField_ratCast q

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : ScalarField) : toField (q • x) = q • toField x :=
  Montgomery.Native256.toField_nnqsmul q x

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : ScalarField) : toField (q • x) = q • toField x :=
  Montgomery.Native256.toField_qsmul q x

end Fast
end BLS12_377
