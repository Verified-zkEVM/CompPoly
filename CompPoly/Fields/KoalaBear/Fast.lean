/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.KoalaBear.Basic
import CompPoly.Fields.Montgomery.Native32Field

/-!
# Fast KoalaBear Field

A native-word Montgomery implementation of KoalaBear arithmetic. The shared algorithms and
proofs live in `CompPoly.Fields.Montgomery.Native32Field`; this module supplies the KoalaBear
constants and its concrete API.
-/

namespace KoalaBear.Fast

open Montgomery.Native32 (Mont32Field FastField)
open Montgomery.Native32.FastField

/-! ## Parameters and carrier -/

/-- The per-field data realizing KoalaBear as a fast 32-bit-word Montgomery field. -/
instance instMont32Field : Mont32Field KoalaBear.fieldSize where
  prime := KoalaBear.is_prime
  modulus32 := 0x7F000001
  modulus64 := 0x7F000001
  rModModulus := 0x01FFFFFE
  r2ModModulus := 0x17F7EFE4
  montgomeryNegInv := 0x7EFFFFFF

/-- The fast native-word KoalaBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField KoalaBear.fieldSize

/-! ## Conversions -/

/-- Reduce a `UInt64` modulo the KoalaBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  Montgomery.Native32.reduceUInt64 KoalaBear.fieldSize x

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.FastField.ofUInt32 KoalaBear.fieldSize x

/-- Convert from the canonical `ZMod` KoalaBear field into fast Montgomery form. -/
@[inline]
def ofField (x : KoalaBear.Field) : Field :=
  Montgomery.Native32.ofField x

/-- Reducing a `UInt64` gives the canonical natural residue modulo KoalaBear. -/
@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    (reduceUInt64 x).toNat = x.toNat % KoalaBear.fieldSize :=
  Montgomery.Native32.toNat_reduceUInt64 x

/-- Reducing a `UInt64` agrees with casting that word into the canonical field. -/
@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    (reduceUInt64 x).toField = (x.toNat : KoalaBear.Field) :=
  Montgomery.Native32.toField_reduceUInt64 x

/-! ## Arithmetic -/

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
def pow (x : Field) (n : ℕ) : Field := Montgomery.Native32.pow x n

/-- Fermat exponent used for inversion in the KoalaBear prime field. -/
def invExponent : ℕ := Montgomery.Native32.invExponent KoalaBear.fieldSize

/-- Inversion in Montgomery form via Fermat's little theorem (`x⁻¹ = x^(p-2)`). -/
@[inline]
def inv (x : Field) : Field := Montgomery.Native32.inv x

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field := Montgomery.Native32.div x y

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and canonical `KoalaBear.Field`. -/
def ringEquiv : Field ≃+* KoalaBear.Field :=
  Montgomery.Native32.ringEquiv KoalaBear.fieldSize

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : KoalaBear.Field) : toField (ofField x) = x :=
  Montgomery.Native32.toField_ofField x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x :=
  Montgomery.Native32.ofField_toField x

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 :=
  Montgomery.Native32.toField_zero

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 :=
  Montgomery.Native32.toField_one

/-- Fast addition agrees with addition in the canonical KoalaBear field. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y :=
  Montgomery.Native32.toField_add x y

/-- Fast subtraction agrees with subtraction in the canonical KoalaBear field. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y :=
  Montgomery.Native32.toField_sub x y

/-- Fast negation agrees with negation in the canonical KoalaBear field. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x :=
  Montgomery.Native32.toField_neg x

/-- Fast multiplication agrees with multiplication in the canonical KoalaBear field. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y :=
  Montgomery.Native32.toField_mul x y

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x :=
  Montgomery.Native32.ringEquiv_apply x

/-- Applying the inverse `ringEquiv` is conversion into fast Montgomery form. -/
@[simp]
theorem ringEquiv_symm_apply (x : KoalaBear.Field) : ringEquiv.symm x = ofField x :=
  Montgomery.Native32.ringEquiv_symm_apply x

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x :=
  Montgomery.Native32.toField_square x

/-- Fast inversion agrees with inversion in the canonical KoalaBear field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ :=
  Montgomery.Native32.toField_inv x

/-- Fast division agrees with division in the canonical KoalaBear field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y :=
  Montgomery.Native32.toField_div x y

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : ℕ) : toField (n : Field) = (n : KoalaBear.Field) :=
  Montgomery.Native32.toField_natCast n

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : Field) = (n : KoalaBear.Field) :=
  Montgomery.Native32.toField_intCast n

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : ℕ) (x : Field) : toField (n • x) = n • toField x :=
  Montgomery.Native32.toField_nsmul n x

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x :=
  Montgomery.Native32.toField_zsmul n x

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : Field) (n : ℕ) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native32.toField_npow x n

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n :=
  Montgomery.Native32.toField_zpow x n

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : KoalaBear.Field) :=
  Montgomery.Native32.toField_nnratCast q

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : KoalaBear.Field) :=
  Montgomery.Native32.toField_ratCast q

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) : toField (q • x) = q • toField x :=
  Montgomery.Native32.toField_nnqsmul q x

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) : toField (q • x) = q • toField x :=
  Montgomery.Native32.toField_qsmul q x

/-! ## Two-adic roots -/

/-- Precomputed KoalaBear two-adic generators in Montgomery representation. -/
def twoAdicGenerators : List Field :=
  [
    ⟨0x01FFFFFE, by decide⟩,
    ⟨0x7D000003, by decide⟩,
    ⟨0x7B020407, by decide⟩,
    ⟨0x60F5EF4D, by decide⟩,
    ⟨0x6D249C01, by decide⟩,
    ⟨0x788529F3, by decide⟩,
    ⟨0x07F7373E, by decide⟩,
    ⟨0x6FE91D3C, by decide⟩,
    ⟨0x3FD49211, by decide⟩,
    ⟨0x1E056392, by decide⟩,
    ⟨0x6D969BAB, by decide⟩,
    ⟨0x439600CC, by decide⟩,
    ⟨0x150276FC, by decide⟩,
    ⟨0x68CACC36, by decide⟩,
    ⟨0x42336C40, by decide⟩,
    ⟨0x019B1972, by decide⟩,
    ⟨0x34E52F6D, by decide⟩,
    ⟨0x1C2EB437, by decide⟩,
    ⟨0x7CB65829, by decide⟩,
    ⟨0x29306FAE, by decide⟩,
    ⟨0x351C7FA7, by decide⟩,
    ⟨0x6E3E9A00, by decide⟩,
    ⟨0x47C2BDF7, by decide⟩,
    ⟨0x0C895820, by decide⟩,
    ⟨0x13C85195, by decide⟩
  ]

/-- The Montgomery root table represents the canonical KoalaBear roots. -/
theorem twoAdicGenerators_eq_map :
    twoAdicGenerators = KoalaBear.twoAdicGenerators.map ofField := by
  decide

end KoalaBear.Fast
