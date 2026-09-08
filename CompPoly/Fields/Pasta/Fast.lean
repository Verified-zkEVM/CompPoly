/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Pasta.Basic
public import CompPoly.Fields.Montgomery.Native64x8Field

/-!
# Fast Pasta base fields

Native-word Montgomery implementations of the Pallas and Vesta base field arithmetic.  The
shared algorithms and proofs live in `CompPoly.Fields.Montgomery.Native64x8Field`; this module
supplies the two sets of constants and the concrete API.

Both Pasta primes are `1 mod 2 ^ 32`, so both have `montgomeryNegInv = 2 ^ 32 - 1`.
-/

@[expose] public section

namespace Pallas.Fast

open Montgomery.Native64x8 (Mont64x8Field FastField)

/-! ## Parameters and carrier -/

/-- The per-field data realizing the Pallas base field as a fast eight-limb Montgomery
field. -/
instance instMont64x8Field : Mont64x8Field Pallas.baseFieldSize where
  prime := Pallas.baseFieldSize_is_prime
  modulusLimbs := ⟨0x1, 0x992d30ed, 0x94cf91b, 0x224698fc, 0x0, 0x0, 0x0, 0x40000000⟩
  rModModulus :=
    ⟨0xfffffffd, 0x34786d38, 0xe41914ad, 0x992c350b, 0xffffffff, 0xffffffff, 0xffffffff,
      0x3fffffff⟩
  r2ModModulus :=
    ⟨0xf, 0x8c78ecb3, 0x8b0de0e7, 0xd7d30dbd, 0xc3c95d18, 0x7797a99b, 0x7b9cb714, 0x96d41af⟩
  montgomeryNegInv := 0xffffffff

/-- The fast native-word Pallas base field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField Pallas.baseFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `ZMod` Pallas base field into fast Montgomery form. -/
@[inline]
def ofField (x : Pallas.BaseField) : Field :=
  Montgomery.Native64x8.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and `Pallas.BaseField`. -/
def ringEquiv : Field ≃+* Pallas.BaseField :=
  Montgomery.Native64x8.FastField.ringEquiv Pallas.baseFieldSize

end Pallas.Fast

namespace Vesta.Fast

open Montgomery.Native64x8 (Mont64x8Field FastField)

/-! ## Parameters and carrier -/

/-- The per-field data realizing the Vesta base field as a fast eight-limb Montgomery
field. -/
instance instMont64x8Field : Mont64x8Field Vesta.baseFieldSize where
  prime := Vesta.baseFieldSize_is_prime
  modulusLimbs := ⟨0x1, 0x8c46eb21, 0x994a8dd, 0x224698fc, 0x0, 0x0, 0x0, 0x40000000⟩
  rModModulus :=
    ⟨0xfffffffd, 0x5b2b3e9c, 0xe3420567, 0x992c350b, 0xffffffff, 0xffffffff, 0xffffffff,
      0x3fffffff⟩
  r2ModModulus :=
    ⟨0xf, 0xfc9678ff, 0x891a16e3, 0x67bb433d, 0x4ccf590, 0x7fae2310, 0x7ccfdaa9, 0x96d41af⟩
  montgomeryNegInv := 0xffffffff

/-- The fast native-word Vesta base field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField Vesta.baseFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `ZMod` Vesta base field into fast Montgomery form. -/
@[inline]
def ofField (x : Vesta.BaseField) : Field :=
  Montgomery.Native64x8.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and `Vesta.BaseField`. -/
def ringEquiv : Field ≃+* Vesta.BaseField :=
  Montgomery.Native64x8.FastField.ringEquiv Vesta.baseFieldSize

end Vesta.Fast
