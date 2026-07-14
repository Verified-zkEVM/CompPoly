/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Basic
import CompPoly.Fields.Montgomery.Native32Field

/-!
# Fast BabyBear Field

A native-word Montgomery implementation of BabyBear arithmetic. The shared algorithms and
proofs live in `CompPoly.Fields.Montgomery.Native32Field`; this module supplies the BabyBear
constants and its concrete API.
-/

namespace BabyBear.Fast

open Montgomery.Native32 (Mont32Field FastField)
open Montgomery.Native32.FastField

/-! ## Parameters and carrier -/

/-- The per-field data realizing BabyBear as a fast 32-bit-word Montgomery field. -/
instance instMont32Field : Mont32Field BabyBear.fieldSize where
  prime := BabyBear.is_prime
  modulus32 := 0x78000001
  modulus64 := 0x78000001
  rModModulus := 0x0FFFFFFE
  r2ModModulus := 0x45DDDDE3
  montgomeryNegInv := 0x77FFFFFF

/-- The fast native-word BabyBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField BabyBear.fieldSize

/-! ## Conversions -/

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.FastField.ofUInt32 BabyBear.fieldSize x

/-- Convert from the canonical `ZMod` BabyBear field into fast Montgomery form. -/
@[inline]
def ofField (x : BabyBear.Field) : Field :=
  Montgomery.Native32.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and canonical `BabyBear.Field`. -/
def ringEquiv : Field ≃+* BabyBear.Field :=
  Montgomery.Native32.ringEquiv BabyBear.fieldSize

end BabyBear.Fast
