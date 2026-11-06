/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Pasta.Basic
public import CompPoly.Fields.Montgomery.Native64x4Field

/-!
# Fast Pasta base fields

Native-word Montgomery implementations of the Pallas and Vesta base field arithmetic.  The
shared algorithms and proofs live in `CompPoly.Fields.Montgomery.Native64x4Field`; this module
supplies the two sets of constants and the concrete API.
-/

@[expose] public section

namespace Pallas.Fast

open Montgomery.Native64x4 (Mont64x4Field FastField)

/-! ## Parameters and carrier -/

/-- The per-field data realizing the Pallas base field as a fast four-limb Montgomery
field. -/
instance instMont64x4Field : Mont64x4Field Pallas.baseFieldSize where
  prime := Pallas.baseFieldSize_is_prime
  modulusLimbs := ⟨0x992d30ed00000001, 0x224698fc094cf91b, 0x0, 0x4000000000000000⟩
  rModModulus :=
    ⟨0x34786d38fffffffd, 0x992c350be41914ad, 0xffffffffffffffff, 0x3fffffffffffffff⟩
  r2ModModulus :=
    ⟨0x8c78ecb30000000f, 0xd7d30dbd8b0de0e7, 0x7797a99bc3c95d18, 0x96d41af7b9cb714⟩
  montgomeryNegInv := 0x992d30ecffffffff

/-- The fast native-word Pallas base field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField Pallas.baseFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `ZMod` Pallas base field into fast Montgomery form. -/
@[inline]
def ofField (x : Pallas.BaseField) : Field :=
  Montgomery.Native64x4.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and `Pallas.BaseField`. -/
def ringEquiv : Field ≃+* Pallas.BaseField :=
  Montgomery.Native64x4.FastField.ringEquiv Pallas.baseFieldSize

end Pallas.Fast

namespace Vesta.Fast

open Montgomery.Native64x4 (Mont64x4Field FastField)

/-! ## Parameters and carrier -/

/-- The per-field data realizing the Vesta base field as a fast four-limb Montgomery
field. -/
instance instMont64x4Field : Mont64x4Field Vesta.baseFieldSize where
  prime := Vesta.baseFieldSize_is_prime
  modulusLimbs := ⟨0x8c46eb2100000001, 0x224698fc0994a8dd, 0x0, 0x4000000000000000⟩
  rModModulus :=
    ⟨0x5b2b3e9cfffffffd, 0x992c350be3420567, 0xffffffffffffffff, 0x3fffffffffffffff⟩
  r2ModModulus :=
    ⟨0xfc9678ff0000000f, 0x67bb433d891a16e3, 0x7fae231004ccf590, 0x96d41af7ccfdaa9⟩
  montgomeryNegInv := 0x8c46eb20ffffffff

/-- The fast native-word Vesta base field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField Vesta.baseFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `ZMod` Vesta base field into fast Montgomery form. -/
@[inline]
def ofField (x : Vesta.BaseField) : Field :=
  Montgomery.Native64x4.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and `Vesta.BaseField`. -/
def ringEquiv : Field ≃+* Vesta.BaseField :=
  Montgomery.Native64x4.FastField.ringEquiv Vesta.baseFieldSize

end Vesta.Fast
