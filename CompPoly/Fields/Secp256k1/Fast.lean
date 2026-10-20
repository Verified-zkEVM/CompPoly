/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Secp256k1.Basic
public import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast secp256k1 Fields

Native eight-limb Montgomery implementations of the secp256k1 scalar and base fields
(`CompPoly.Fields.Montgomery.Native64x8Field`). This module supplies the constants.
-/

@[expose] public section

namespace Secp256k1.Fast

open Montgomery.Native64x8 (Mont64x8Field FastField GcdData)

set_option exponentiation.threshold 1100

/-! ## Scalar field -/

/-- Divstep schedule of the binary-GCD inverse candidate over the scalar field. -/
instance instScalarGcdData : GcdData Secp256k1.scalarFieldSize where
  finalRounds := 45
  initU :=
    ⟨0x35d9e12a, 0x14d610c5, 0x309a5692, 0x8cb9c9b1, 0xf0698647, 0x6f341f1c, 0x9a5fd791,
      0x71a6f17⟩

/-- The per-field data realizing the secp256k1 scalar field as a fast eight-limb Montgomery
field. -/
instance instScalarMont64x8Field : Mont64x8Field Secp256k1.scalarFieldSize where
  prime := Secp256k1.ScalarField_is_prime
  modulusLimbs :=
    ⟨0xd0364141, 0xbfd25e8c, 0xaf48a03b, 0xbaaedce6, 0xfffffffe, 0xffffffff, 0xffffffff,
      0xffffffff⟩
  rModModulus :=
    ⟨0x2fc9bebf, 0x402da173, 0x50b75fc4, 0x45512319, 0x1, 0x0, 0x0, 0x0⟩
  r2ModModulus :=
    ⟨0x67d7d140, 0x896cf214, 0xe7cf878, 0x741496c2, 0x5bcd07c6, 0xe697f5e4, 0x81c69bc5,
      0x9d671cd5⟩
  montgomeryNegInv := 0x5588b13f

/-- The eight-limb secp256k1 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField Secp256k1.scalarFieldSize

/-- Convert from the canonical `Secp256k1.ScalarField` into fast Montgomery form. -/
@[inline]
def ofScalarField (x : Secp256k1.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the eight-limb representation and the canonical
`Secp256k1.ScalarField`. -/
def scalarRingEquiv : ScalarField ≃+* Secp256k1.ScalarField :=
  FastField.ringEquiv Secp256k1.scalarFieldSize

/-! ## Base field -/

/-- Divstep schedule of the binary-GCD inverse candidate over the base field. -/
instance instBaseGcdData : GcdData Secp256k1.baseFieldSize where
  finalRounds := 45
  initU := ⟨0x0, 0x3a4284, 0x1e88, 0x4, 0x0, 0x0, 0x0, 0x0⟩

/-- The per-field data realizing the secp256k1 base field as a fast eight-limb Montgomery
field. -/
instance instBaseMont64x8Field : Mont64x8Field Secp256k1.baseFieldSize where
  prime := Secp256k1.BaseField_is_prime
  modulusLimbs :=
    ⟨0xfffffc2f, 0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
      0xffffffff⟩
  rModModulus := ⟨0x3d1, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0⟩
  r2ModModulus := ⟨0xe90a1, 0x7a2, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0⟩
  montgomeryNegInv := 0xd2253531

/-- The eight-limb secp256k1 base field carrier, stored as a Montgomery residue. -/
abbrev BaseField : Type := FastField Secp256k1.baseFieldSize

/-- Convert from the canonical `Secp256k1.BaseField` into fast Montgomery form. -/
@[inline]
def ofBaseField (x : Secp256k1.BaseField) : BaseField :=
  FastField.ofField x

/-- Ring equivalence between the eight-limb representation and the canonical
`Secp256k1.BaseField`. -/
def baseRingEquiv : BaseField ≃+* Secp256k1.BaseField :=
  FastField.ringEquiv Secp256k1.baseFieldSize

end Secp256k1.Fast
