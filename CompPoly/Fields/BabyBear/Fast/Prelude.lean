/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Basic
import CompPoly.Fields.Montgomery.Native32Field

/-!
# Fast BabyBear Field — Basics

The native-word constants and the `Field` carrier type for the fast BabyBear field. The
shared implementation lives in `CompPoly.Fields.Montgomery.Native32Field`; this module
supplies the per-field `Mont32Field` instance (the five word constants plus the
`decide`-checked numeric facts) and pins `Field := Native32.FastField BabyBear.Field`, so
the generic definitions, proofs, and algebraic instances specialize to BabyBear.

The Montgomery reducers are re-exported in `CompPoly.Fields.BabyBear.Fast.Montgomery`;
conversions in `...Fast.Convert`; the field operations and instances in
`CompPoly.Fields.BabyBear.Fast`.
-/

namespace BabyBear
namespace Fast

open Montgomery.Native32 (Mont32Field FastField)

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

/-- The native `UInt32` modulus agrees with the mathematical BabyBear modulus. -/
@[simp] theorem modulus_toNat : modulus.toNat = BabyBear.fieldSize := by decide

/-- The native `UInt64` modulus agrees with the mathematical BabyBear modulus. -/
@[simp] theorem modulus64_toNat : modulus64.toNat = BabyBear.fieldSize := by decide

theorem fieldSize_pos : 0 < BabyBear.fieldSize := by decide

theorem two_lt_fieldSize : 2 < BabyBear.fieldSize := by decide

theorem fieldSize_lt_uint32Size : BabyBear.fieldSize < UInt32.size := by decide

theorem fieldSize_add_fieldSize_lt_two64 :
    BabyBear.fieldSize + BabyBear.fieldSize < 2 ^ 64 := by decide

theorem fieldSize_add_fieldSize_lt_uint32Size :
    BabyBear.fieldSize + BabyBear.fieldSize < UInt32.size := by decide

theorem fieldSize_mul_fieldSize_lt_two64 :
    BabyBear.fieldSize * BabyBear.fieldSize < 2 ^ 64 := by decide

theorem uint32Size_lt_three_fieldSize :
    UInt32.size < BabyBear.fieldSize + BabyBear.fieldSize + BabyBear.fieldSize := by decide

theorem fieldSize_mul_uint32Size_lt_two64 :
    BabyBear.fieldSize * UInt32.size < 2 ^ 64 := by decide

theorem two_fieldSize_mul_uint32Size_lt_two64 :
    2 * BabyBear.fieldSize * UInt32.size < 2 ^ 64 := by decide

theorem uint32Size_ne_zero_in_field :
    (UInt32.size : BabyBear.Field) ≠ 0 := by decide

theorem rModModulus_lt_fieldSize : rModModulus.toNat < BabyBear.fieldSize := by decide

theorem r2ModModulus_lt_fieldSize : r2ModModulus.toNat < BabyBear.fieldSize := by decide

theorem rModModulus_cast :
    (rModModulus.toNat : BabyBear.Field) = (UInt32.size : BabyBear.Field) := by decide

theorem r2ModModulus_cast :
    (r2ModModulus.toNat : BabyBear.Field) = (UInt32.size : BabyBear.Field) ^ 2 := by decide

/-- The per-field data realizing BabyBear as a fast 32-bit-word Montgomery field. The five
word constants are the only runtime data; every other field is a `decide`-checked fact. -/
instance instMont32Field : Mont32Field BabyBear.Field where
  fieldSize := BabyBear.fieldSize
  prime := inferInstance
  modulus := modulus
  modulus64 := modulus64
  rModModulus := rModModulus
  r2ModModulus := r2ModModulus
  montgomeryNegInv := montgomeryNegInv
  modulus_toNat := modulus_toNat
  modulus64_toNat := modulus64_toNat
  fieldSize_pos := fieldSize_pos
  two_lt_fieldSize := two_lt_fieldSize
  fieldSize_lt_uint32Size := fieldSize_lt_uint32Size
  fieldSize_add_fieldSize_lt_two64 := fieldSize_add_fieldSize_lt_two64
  fieldSize_add_fieldSize_lt_uint32Size := fieldSize_add_fieldSize_lt_uint32Size
  fieldSize_mul_fieldSize_lt_two64 := fieldSize_mul_fieldSize_lt_two64
  uint32Size_lt_three_fieldSize := uint32Size_lt_three_fieldSize
  fieldSize_mul_uint32Size_lt_two64 := fieldSize_mul_uint32Size_lt_two64
  two_fieldSize_mul_uint32Size_lt_two64 := two_fieldSize_mul_uint32Size_lt_two64
  uint32Size_ne_zero_in_field := uint32Size_ne_zero_in_field
  rModModulus_lt_fieldSize := rModModulus_lt_fieldSize
  r2ModModulus_lt_fieldSize := r2ModModulus_lt_fieldSize
  rModModulus_cast := rModModulus_cast
  r2ModModulus_cast := r2ModModulus_cast
  negInv_congr := by decide
  two_ne_zero_in_field := by decide

/-- The fast native-word BabyBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField BabyBear.Field

/-- The raw Montgomery word backing a fast BabyBear element. -/
@[inline]
def raw (x : Field) : UInt32 := x.val

end Fast
end BabyBear
