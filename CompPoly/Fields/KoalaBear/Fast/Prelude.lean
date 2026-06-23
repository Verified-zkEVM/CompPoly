/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.KoalaBear.Basic

/-!
# Fast KoalaBear Field — Basics

The native-word modulus and the `Field` carrier type for the fast KoalaBear field,
plus the elementary numeric bounds reused throughout the Montgomery reduction layer.

The Montgomery-form constants and reduction machinery live in
`CompPoly.Fields.KoalaBear.Fast.Montgomery`; conversions in `...Fast.Convert`; the
field operations and instances in `CompPoly.Fields.KoalaBear.Fast`.
-/

namespace KoalaBear
namespace Fast

/-- KoalaBear modulus as a native word. -/
def modulus : UInt32 := 0x7F000001

/-- KoalaBear modulus as a 64-bit word for modular reduction. -/
def modulus64 : UInt64 := 0x7F000001

/-- The fast native-word KoalaBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := { x : UInt32 // x.toNat < KoalaBear.fieldSize }

instance : DecidableEq Field := inferInstance

/-- The raw Montgomery word backing a fast KoalaBear element. -/
@[inline]
def raw (x : Field) : UInt32 := x.val

/-- The native `UInt32` modulus agrees with the mathematical KoalaBear modulus. -/
@[simp] theorem modulus_toNat : modulus.toNat = KoalaBear.fieldSize := by
  decide

/-- The native `UInt64` modulus agrees with the mathematical KoalaBear modulus. -/
@[simp] theorem modulus64_toNat : modulus64.toNat = KoalaBear.fieldSize := by
  decide

theorem fieldSize_pos : 0 < KoalaBear.fieldSize := by
  decide

theorem fieldSize_lt_uint32Size : KoalaBear.fieldSize < UInt32.size := by
  decide

theorem fieldSize_add_fieldSize_lt_two64 :
    KoalaBear.fieldSize + KoalaBear.fieldSize < 2 ^ 64 := by
  decide

theorem fieldSize_add_fieldSize_lt_uint32Size :
    KoalaBear.fieldSize + KoalaBear.fieldSize < UInt32.size := by
  decide

theorem fieldSize_mul_fieldSize_lt_two64 :
    KoalaBear.fieldSize * KoalaBear.fieldSize < 2 ^ 64 := by
  decide

theorem uint32Size_lt_three_fieldSize :
    UInt32.size < KoalaBear.fieldSize + KoalaBear.fieldSize + KoalaBear.fieldSize := by
  decide

theorem fieldSize_mul_uint32Size_lt_two64 :
    KoalaBear.fieldSize * UInt32.size < 2 ^ 64 := by
  decide

theorem two_fieldSize_mul_uint32Size_lt_two64 :
    2 * KoalaBear.fieldSize * UInt32.size < 2 ^ 64 := by
  decide

theorem uint32Size_ne_zero_in_field :
    (UInt32.size : KoalaBear.Field) ≠ 0 := by
  decide

end Fast
end KoalaBear
