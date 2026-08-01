/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.Montgomery.Native32Field

/-!
# Fast KoalaBear Field

A native-word Montgomery implementation of KoalaBear arithmetic. The shared algorithms and
proofs live in `CompPoly.Fields.Montgomery.Native32Field`; this module supplies the KoalaBear
constants and its concrete API.
-/

@[expose] public section

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

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.FastField.ofUInt32 KoalaBear.fieldSize x

/-- Convert from the canonical `ZMod` KoalaBear field into fast Montgomery form. -/
@[inline]
def ofField (x : KoalaBear.Field) : Field :=
  Montgomery.Native32.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and canonical `KoalaBear.Field`. -/
def ringEquiv : Field ≃+* KoalaBear.Field :=
  Montgomery.Native32.ringEquiv KoalaBear.fieldSize

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
