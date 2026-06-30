/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Montgomery

/-!
# Fast BabyBear Field — Conversions

Conversions between the fast Montgomery representation and the canonical
`BabyBear.Field` / `Nat` views, re-exported from the shared implementation in
`CompPoly.Fields.Montgomery.Native32Field` at the BabyBear instance.
-/

namespace BabyBear
namespace Fast

open Montgomery.Native32

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) : Field :=
  Montgomery.Native32.ofCanonicalNat (F := BabyBear.Field) n h

/-- Reduce a `UInt64` modulo the BabyBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  Montgomery.Native32.reduceUInt64 (F := BabyBear.Field) x

/-- The zero fast BabyBear element. -/
def zero : Field := Montgomery.Native32.zero (F := BabyBear.Field)

/-- The one fast BabyBear element. -/
def one : Field := Montgomery.Native32.one (F := BabyBear.Field)

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (n : Nat) : Field :=
  Montgomery.Native32.ofNat (F := BabyBear.Field) n

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.ofUInt32 (F := BabyBear.Field) x

/-- Convert from the canonical `ZMod` BabyBear field into fast Montgomery form. -/
@[inline]
def ofField (x : BabyBear.Field) : Field :=
  Montgomery.Native32.ofField (F := BabyBear.Field) x

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (n : Int) : Field :=
  Montgomery.Native32.ofInt (F := BabyBear.Field) n

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toCanonicalUInt32 (x : Field) : UInt32 :=
  Montgomery.Native32.toCanonicalUInt32 x

/-- Convert a fast BabyBear element to its canonical natural representative. -/
@[inline]
def toNat (x : Field) : Nat :=
  Montgomery.Native32.toNat x

/-- Convert a fast BabyBear element to the canonical `ZMod` BabyBear field. -/
@[inline]
def toField (x : Field) : BabyBear.Field :=
  Montgomery.Native32.toField x

theorem toNat_lt_fieldSize (x : Field) : toNat x < BabyBear.fieldSize :=
  Montgomery.Native32.toNat_lt_fieldSize x

theorem toField_eq_raw_mul_inv (x : Field) :
    toField x = (x.val.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ :=
  Montgomery.Native32.toField_eq_raw_mul_inv x

theorem raw_cast_eq_toField_mul (x : Field) :
    (x.val.toNat : BabyBear.Field) = toField x * (UInt32.size : BabyBear.Field) :=
  Montgomery.Native32.raw_cast_eq_toField_mul x

theorem nat_eq_of_field_eq {a b : Nat} (ha : a < BabyBear.fieldSize)
    (hb : b < BabyBear.fieldSize) (h : (a : BabyBear.Field) = (b : BabyBear.Field)) :
    a = b :=
  Montgomery.Native32.nat_eq_of_field_eq (F := BabyBear.Field) ha hb h

theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < BabyBear.fieldSize) :
    ((ofCanonicalNat n h).val.toNat : BabyBear.Field) =
      (n : BabyBear.Field) * (UInt32.size : BabyBear.Field) :=
  Montgomery.Native32.ofCanonicalNat_raw_cast (F := BabyBear.Field) n h

theorem reduceUInt64_raw_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field) :=
  Montgomery.Native32.reduceUInt64_raw_cast x

/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
theorem toNat_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toNat (ofCanonicalNat n h) = n :=
  Montgomery.Native32.toNat_ofCanonicalNat n h

/-- `ofCanonicalNat` embeds a canonical representative into the canonical field. -/
@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < BabyBear.fieldSize) :
    toField (ofCanonicalNat n h) = (n : BabyBear.Field) :=
  Montgomery.Native32.toField_ofCanonicalNat n h

/-- Reducing a `UInt64` gives the canonical natural residue modulo BabyBear. -/
@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    toNat (reduceUInt64 x) = x.toNat % BabyBear.fieldSize :=
  Montgomery.Native32.toNat_reduceUInt64 x

/-- Reducing a `UInt64` agrees with casting that word into the canonical field. -/
@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    toField (reduceUInt64 x) = (x.toNat : BabyBear.Field) :=
  Montgomery.Native32.toField_reduceUInt64 x

end Fast
end BabyBear
