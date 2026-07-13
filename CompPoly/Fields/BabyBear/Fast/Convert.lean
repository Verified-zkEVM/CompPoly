/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Defs

/-!
# Fast BabyBear Field — Conversions

Conversions between the fast Montgomery representation and the canonical
`BabyBear.Field` / `Nat` views, re-exported from the shared implementation in
`CompPoly.Fields.Montgomery.Native32Field` at the BabyBear instance.
-/

namespace BabyBear
namespace Fast

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) : Field :=
  Montgomery.Native32.ofCanonicalNat n h

/-- Reduce a `UInt64` modulo the BabyBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  Montgomery.Native32.reduceUInt64 BabyBear.fieldSize x

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.FastField.ofUInt32 BabyBear.fieldSize x

/-- Convert from the canonical `ZMod` BabyBear field into fast Montgomery form. -/
@[inline]
def ofField (x : BabyBear.Field) : Field :=
  Montgomery.Native32.ofField x

theorem toNat_lt_fieldSize (x : Field) : x.toNat < BabyBear.fieldSize :=
  Montgomery.Native32.toNat_lt_modulus x

theorem toField_eq_raw_mul_inv (x : Field) :
    x.toField = (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ :=
  Montgomery.Native32.toField_eq_raw_mul_inv x

theorem raw_cast_eq_toField_mul (x : Field) :
    (x.val.toNat : BabyBear.Field) = x.toField * (UInt32.size : BabyBear.Field) :=
  Montgomery.Native32.raw_cast_eq_toField_mul x

theorem nat_eq_of_field_eq {a b : Nat} (ha : a < BabyBear.fieldSize)
    (hb : b < BabyBear.fieldSize) (h : (a : BabyBear.Field) = (b : BabyBear.Field)) :
    a = b :=
  Montgomery.Native32.nat_eq_of_field_eq ha hb h

theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < BabyBear.fieldSize) :
    ((ofCanonicalNat n h).val.toNat : BabyBear.Field) =
      (n : BabyBear.Field) * (UInt32.size : BabyBear.Field) :=
  Montgomery.Native32.ofCanonicalNat_raw_cast n h

theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field) :=
  Montgomery.Native32.reduceUInt64_raw_cast x

/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    (ofCanonicalNat n h).toNat = n :=
  Montgomery.Native32.toNat_ofCanonicalNat n h

/-- `ofCanonicalNat` embeds a canonical representative into the canonical field. -/
@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    (ofCanonicalNat n h).toField = (n : BabyBear.Field) :=
  Montgomery.Native32.toField_ofCanonicalNat n h

/-- Reducing a `UInt64` gives the canonical natural residue modulo BabyBear. -/
@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    (reduceUInt64 x).toNat = x.toNat % BabyBear.fieldSize :=
  Montgomery.Native32.toNat_reduceUInt64 x

/-- Reducing a `UInt64` agrees with casting that word into the canonical field. -/
@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    (reduceUInt64 x).toField = (x.toNat : BabyBear.Field) :=
  Montgomery.Native32.toField_reduceUInt64 x

end Fast
end BabyBear
