/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/
import CompPoly.Fields.BabyBear.Basic
import CompPoly.Fields.Montgomery.Native32Field

/-! # Fast BabyBear field definitions -/

namespace BabyBear.Fast
open Montgomery.Native32 (Mont32Field FastField)

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

end BabyBear.Fast
