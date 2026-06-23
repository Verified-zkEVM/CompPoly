/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.BabyBear.Basic

/-!
# Fast BabyBear Field — Basics

The native-word modulus and the `Field` carrier type for the fast BabyBear field,
plus the elementary numeric bounds reused throughout the Montgomery reduction layer.

The Montgomery-form constants and reduction machinery live in
`CompPoly.Fields.BabyBear.Fast.Montgomery`; conversions in `...Fast.Convert`; the
field operations and instances in `CompPoly.Fields.BabyBear.Fast`.
-/

namespace BabyBear
namespace Fast

/-- BabyBear modulus as a native word. -/
def modulus : UInt32 := 2013265921

/-- BabyBear modulus as a 64-bit word for modular reduction. -/
def modulus64 : UInt64 := 2013265921

/-- The fast native-word BabyBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := { x : UInt32 // x.toNat < BabyBear.fieldSize }

instance : DecidableEq Field := inferInstance

/-- The raw Montgomery word backing a fast BabyBear element. -/
@[inline]
def raw (x : Field) : UInt32 := x.val

/-- The native `UInt32` modulus agrees with the mathematical BabyBear modulus. -/
@[simp] theorem modulus_toNat : modulus.toNat = BabyBear.fieldSize := by
  decide

/-- The native `UInt64` modulus agrees with the mathematical BabyBear modulus. -/
@[simp] theorem modulus64_toNat : modulus64.toNat = BabyBear.fieldSize := by
  decide

theorem fieldSize_pos : 0 < BabyBear.fieldSize := by
  decide

theorem fieldSize_lt_uint32Size : BabyBear.fieldSize < UInt32.size := by
  decide

theorem fieldSize_add_fieldSize_lt_two64 :
    BabyBear.fieldSize + BabyBear.fieldSize < 2 ^ 64 := by
  decide

theorem fieldSize_add_fieldSize_lt_uint32Size :
    BabyBear.fieldSize + BabyBear.fieldSize < UInt32.size := by
  decide

theorem fieldSize_mul_fieldSize_lt_two64 :
    BabyBear.fieldSize * BabyBear.fieldSize < 2 ^ 64 := by
  decide

theorem uint32Size_lt_three_fieldSize :
    UInt32.size < BabyBear.fieldSize + BabyBear.fieldSize + BabyBear.fieldSize := by
  decide

theorem fieldSize_mul_uint32Size_lt_two64 :
    BabyBear.fieldSize * UInt32.size < 2 ^ 64 := by
  decide

theorem two_fieldSize_mul_uint32Size_lt_two64 :
    2 * BabyBear.fieldSize * UInt32.size < 2 ^ 64 := by
  decide

theorem uint32Size_ne_zero_in_field :
    (UInt32.size : BabyBear.Field) ≠ 0 := by
  decide

end Fast
end BabyBear
