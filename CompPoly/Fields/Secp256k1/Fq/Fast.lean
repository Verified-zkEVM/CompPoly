/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1.Fq.Fast.Prelude

/-!
# Fast Secp256k1.Fq Base Field — operations

A native-word implementation of secp256k1 base-field arithmetic as a sidecar to the canonical
`Secp256k1.BaseField := ZMod BASE_FIELD_CARD` model. Fast values are stored as 256-bit Montgomery
residues below the prime (`x · 2²⁵⁶ mod p`, four `UInt64` limbs).

The operations, their `Field`/`CommRing`/`NonBinaryField` instances, the `toField` bridge, and
all correctness theorems are shared across every fast 256-bit Montgomery field; they live once
in `CompPoly.Fields.Montgomery.Native256Field`, parameterized by the `Mont256Field` instance in
`CompPoly.Fields.Secp256k1.Fq.Fast.Prelude`. Because `BaseField` is `Native256.FastField` at the
secp256k1 base-field tag, the generic algebraic instances resolve here automatically. This module
re-exports the named operations and `simp` lemmas at that instance.
-/

namespace Secp256k1.Fq
namespace Fast

open Montgomery.Native256

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : BaseField) : BaseField := Montgomery.Native256.add x y

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : BaseField) : BaseField := Montgomery.Native256.neg x

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : BaseField) : BaseField := Montgomery.Native256.sub x y

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : BaseField) : BaseField := Montgomery.Native256.mul x y

/-- Fast squaring. -/
@[inline]
def square (x : BaseField) : BaseField := Montgomery.Native256.square x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[inline]
def pow (x : BaseField) (n : Nat) : BaseField := Montgomery.Native256.pow x n

/-- Fermat exponent used for inversion in the Secp256k1.Fq scalar field. -/
def invExponent : Nat := Montgomery.Native256.invExponent (F := Secp256k1.BaseField)

/-- Inversion in Montgomery form via Fermat's little theorem, by fixed 4-bit window
exponentiation. -/
@[inline]
def inv (x : BaseField) : BaseField := Montgomery.Native256.inv x

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : BaseField) : BaseField := Montgomery.Native256.div x y

/-- Exit Montgomery form: the canonical native-word representative of a fast element. -/
@[inline]
def toCanonicalUInt256L (x : BaseField) : UInt256L := Montgomery.Native256.toCanonicalUInt256L x

/-- The canonical natural representative of a fast element. -/
@[inline]
def toNat (x : BaseField) : Nat := Montgomery.Native256.toNat x

/-- Interpret a fast element in the canonical `Secp256k1.BaseField` field. -/
@[inline]
def toField (x : BaseField) : Secp256k1.BaseField := Montgomery.Native256.toField x

/-- Build a fast element from a natural number (reducing modulo the prime). -/
@[inline]
def ofNat (n : Nat) : BaseField := Montgomery.Native256.ofNat n

/-- Convert from the canonical `Secp256k1.BaseField` field into fast Montgomery form. -/
@[inline]
def ofField (x : Secp256k1.BaseField) : BaseField :=
  Montgomery.Native256.ofField (F := Secp256k1.BaseField) x

/-- Ring equivalence between the fast representation and the canonical `Secp256k1.BaseField`. -/
def ringEquiv : BaseField ≃+* Secp256k1.BaseField :=
  Montgomery.Native256.ringEquiv (F := Secp256k1.BaseField)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : Secp256k1.BaseField) : toField (ofField x) = x :=
  Montgomery.Native256.toField_ofField (F := Secp256k1.BaseField) x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : BaseField) : ofField (toField x) = x :=
  Montgomery.Native256.ofField_toField x

/-- The canonical-field interpretation distinguishes fast Secp256k1.Fq values. -/
theorem toField_injective : Function.Injective (toField : BaseField → Secp256k1.BaseField) :=
  Montgomery.Native256.toField_injective

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : BaseField) = 0 :=
  Montgomery.Native256.toField_zero (F := Secp256k1.BaseField)

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : BaseField) = 1 :=
  Montgomery.Native256.toField_one (F := Secp256k1.BaseField)

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : BaseField) : toField (x + y) = toField x + toField y :=
  Montgomery.Native256.toField_add x y

/-- Fast subtraction agrees with subtraction in the canonical field. -/
@[simp]
theorem toField_sub (x y : BaseField) : toField (x - y) = toField x - toField y :=
  Montgomery.Native256.toField_sub x y

/-- Fast negation agrees with negation in the canonical field. -/
@[simp]
theorem toField_neg (x : BaseField) : toField (-x) = -toField x :=
  Montgomery.Native256.toField_neg x

/-- Fast multiplication agrees with multiplication in the canonical field. -/
@[simp]
theorem toField_mul (x y : BaseField) : toField (x * y) = toField x * toField y :=
  Montgomery.Native256.toField_mul x y

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : BaseField) : ringEquiv x = toField x := rfl

/-- Applying the inverse `ringEquiv` is conversion into fast Montgomery form. -/
@[simp]
theorem ringEquiv_symm_apply (x : Secp256k1.BaseField) : ringEquiv.symm x = ofField x := rfl

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : BaseField) : toField (square x) = toField x * toField x :=
  Montgomery.Native256.toField_square x

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : BaseField) : toField x⁻¹ = (toField x)⁻¹ :=
  Montgomery.Native256.toField_inv x

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : BaseField) : toField (x / y) = toField x / toField y :=
  Montgomery.Native256.toField_div x y

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : BaseField) = (n : Secp256k1.BaseField) :=
  Montgomery.Native256.toField_natCast n

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : BaseField) = (n : Secp256k1.BaseField) :=
  Montgomery.Native256.toField_intCast n

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : BaseField) : toField (n • x) = n • toField x :=
  Montgomery.Native256.toField_nsmul n x

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : BaseField) : toField (n • x) = n • toField x :=
  Montgomery.Native256.toField_zsmul n x

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : BaseField) (n : Nat) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native256.toField_npow x n

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : BaseField) (n : Int) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native256.toField_zpow x n

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : BaseField) = (q : Secp256k1.BaseField) :=
  Montgomery.Native256.toField_nnratCast q

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : BaseField) = (q : Secp256k1.BaseField) :=
  Montgomery.Native256.toField_ratCast q

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : BaseField) : toField (q • x) = q • toField x :=
  Montgomery.Native256.toField_nnqsmul q x

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : BaseField) : toField (q • x) = q • toField x :=
  Montgomery.Native256.toField_qsmul q x

end Fast
end Secp256k1.Fq
