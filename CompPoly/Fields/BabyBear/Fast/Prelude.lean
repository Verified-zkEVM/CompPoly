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
`decide`-checked numeric facts) and pins `Field := Native32.FastField BabyBear.fieldSize`, so
the generic definitions, proofs, and algebraic instances specialize to BabyBear.

The Montgomery reducers are re-exported in `CompPoly.Fields.BabyBear.Fast.Montgomery`;
conversions in `...Fast.Convert`; the field operations and instances in
`CompPoly.Fields.BabyBear.Fast`.
-/

namespace BabyBear
namespace Fast

open Montgomery.Native32 (Mont32Field FastField)

/-- BabyBear modulus as a native word. -/
def modulus32 : UInt32 := 0x78000001

/-- BabyBear modulus as a 64-bit word for modular reduction. -/
def modulus64 : UInt64 := 0x78000001

/-- `2^32 mod BabyBear.fieldSize`. This is the Montgomery representation of one. -/
def rModModulus : UInt32 := 0x0FFFFFFE

/-- `(2^32)^2 mod BabyBear.fieldSize`, used to enter Montgomery representation. -/
def r2ModModulus : UInt32 := 0x45DDDDE3

/-- `-BabyBear.fieldSize⁻¹ mod 2^32`, used by Montgomery reduction. -/
def montgomeryNegInv : UInt32 := 0x77FFFFFF

/-- The native `UInt32` modulus agrees with the mathematical BabyBear modulus. -/
@[simp] theorem modulus32_toNat : modulus32.toNat = BabyBear.fieldSize := by decide

/-- The native `UInt64` modulus agrees with the mathematical BabyBear modulus. -/
@[simp] theorem modulus64_toNat : modulus64.toNat = BabyBear.fieldSize := by decide

theorem two_mul_modulus_lt_two_pow_32 : 2 * BabyBear.fieldSize < 2 ^ 32 := by decide

theorem two_pow_32_lt_three_mul_modulus : 2 ^ 32 < 3 * BabyBear.fieldSize := by decide

theorem rModModulus_toNat : rModModulus.toNat = 2 ^ 32 % BabyBear.fieldSize := by decide

theorem r2ModModulus_toNat :
    r2ModModulus.toNat = (2 ^ 32) ^ 2 % BabyBear.fieldSize := by decide

/-- The per-field data realizing BabyBear as a fast 32-bit-word Montgomery field. The five
word constants are the only runtime data; every other field is a `decide`-checked fact. -/
instance instMont32Field : Mont32Field BabyBear.fieldSize where
  prime := BabyBear.is_prime
  modulus32 := modulus32
  modulus64 := modulus64
  rModModulus := rModModulus
  r2ModModulus := r2ModModulus
  montgomeryNegInv := montgomeryNegInv
  modulus32_toNat := modulus32_toNat
  modulus64_toNat := modulus64_toNat
  two_mul_modulus_lt_two_pow_32 := two_mul_modulus_lt_two_pow_32
  two_pow_32_lt_three_mul_modulus := two_pow_32_lt_three_mul_modulus
  rModModulus_toNat := rModModulus_toNat
  r2ModModulus_toNat := r2ModModulus_toNat
  montgomeryNegInv_mul_modulus_mod_two_pow_32 := by decide

/-- The fast native-word BabyBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField BabyBear.fieldSize

/-- The raw Montgomery word backing a fast BabyBear element. -/
@[inline]
def raw (x : Field) : UInt32 := x.val

end Fast
end BabyBear
