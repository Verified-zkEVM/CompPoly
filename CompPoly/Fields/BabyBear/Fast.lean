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

/-! ## Two-adic roots -/

/-- Precomputed BabyBear two-adic generators in Montgomery representation. -/
def twoAdicGenerators : List Field :=
  [
    ⟨0x0FFFFFFE, by decide⟩,
    ⟨0x68000003, by decide⟩,
    ⟨0x1C38D511, by decide⟩,
    ⟨0x3D85298F, by decide⟩,
    ⟨0x5F06E481, by decide⟩,
    ⟨0x3F5C39EC, by decide⟩,
    ⟨0x5516A97A, by decide⟩,
    ⟨0x3D6BE592, by decide⟩,
    ⟨0x5BB04149, by decide⟩,
    ⟨0x4907F9AB, by decide⟩,
    ⟨0x548B8E90, by decide⟩,
    ⟨0x1D8CA617, by decide⟩,
    ⟨0x2CE7F0E6, by decide⟩,
    ⟨0x621B371F, by decide⟩,
    ⟨0x6D4D2D78, by decide⟩,
    ⟨0x18716FCD, by decide⟩,
    ⟨0x3B30A682, by decide⟩,
    ⟨0x1C6F4728, by decide⟩,
    ⟨0x59B01F7C, by decide⟩,
    ⟨0x1A7F97AC, by decide⟩,
    ⟨0x0732561C, by decide⟩,
    ⟨0x2B5A1CD4, by decide⟩,
    ⟨0x6F7D26F9, by decide⟩,
    ⟨0x16E2F919, by decide⟩,
    ⟨0x285AB85B, by decide⟩,
    ⟨0x0DD5A9EC, by decide⟩,
    ⟨0x43F13568, by decide⟩,
    ⟨0x57FAB6EE, by decide⟩
  ]

/-- The Montgomery root table represents the canonical BabyBear roots. -/
theorem twoAdicGenerators_eq_map :
    twoAdicGenerators = BabyBear.twoAdicGenerators.map ofField := by
  decide

end BabyBear.Fast
