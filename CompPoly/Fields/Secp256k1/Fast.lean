/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Secp256k1.Basic
public import CompPoly.Fields.Montgomery.Native64x4Inv

/-!
# Fast secp256k1 Fields

Native four-limb Montgomery implementations of the secp256k1 scalar and base fields
(`CompPoly.Fields.Montgomery.Native64x4Field`). This module supplies the constants.
-/

@[expose] public section

namespace Secp256k1.Fast

open Montgomery.Native64x4 (Mont64x4Field FastField GcdData)

set_option exponentiation.threshold 1100

/-! ## Scalar field -/

/-- Divstep schedule of the binary-GCD inverse candidate over the scalar field. -/
instance instScalarGcdData : GcdData Secp256k1.scalarFieldSize where
  finalRounds := 45
  initU := ⟨0x5fbba3af31b96a9b, 0x4f4f0e1fb393fef9, 0x362b8d1280b4ca5e, 0x215bb648c78ffa6d⟩

/-- The per-field data realizing the secp256k1 scalar field as a fast four-limb Montgomery
field. -/
instance instScalarMont64x4Field : Mont64x4Field Secp256k1.scalarFieldSize where
  prime := Secp256k1.ScalarField_is_prime
  modulusLimbs :=
    ⟨0xbfd25e8cd0364141, 0xbaaedce6af48a03b, 0xfffffffffffffffe, 0xffffffffffffffff⟩
  rModModulus := ⟨0x402da1732fc9bebf, 0x4551231950b75fc4, 0x1, 0x0⟩
  r2ModModulus :=
    ⟨0x896cf21467d7d140, 0x741496c20e7cf878, 0xe697f5e45bcd07c6, 0x9d671cd581c69bc5⟩
  montgomeryNegInv := 0x4b0dff665588b13f

/-- The four-limb secp256k1 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField Secp256k1.scalarFieldSize

/-- Convert from the canonical `Secp256k1.ScalarField` into fast Montgomery form. -/
@[inline]
def ofScalarField (x : Secp256k1.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the four-limb representation and the canonical
`Secp256k1.ScalarField`. -/
def scalarRingEquiv : ScalarField ≃+* Secp256k1.ScalarField :=
  FastField.ringEquiv Secp256k1.scalarFieldSize

/-! ## Base field -/

/-- Divstep schedule of the binary-GCD inverse candidate over the base field. -/
instance instBaseGcdData : GcdData Secp256k1.baseFieldSize where
  finalRounds := 45
  initU := ⟨0x0, 0x795f6a608d461504, 0x3d10015d8f1b, 0x4⟩

/-- The per-field data realizing the secp256k1 base field as a fast four-limb Montgomery
field. -/
instance instBaseMont64x4Field : Mont64x4Field Secp256k1.baseFieldSize where
  prime := Secp256k1.BaseField_is_prime
  modulusLimbs :=
    ⟨0xfffffffefffffc2f, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩
  rModModulus := ⟨0x1000003d1, 0x0, 0x0, 0x0⟩
  r2ModModulus := ⟨0x7a2000e90a1, 0x1, 0x0, 0x0⟩
  montgomeryNegInv := 0xd838091dd2253531

/-- The four-limb secp256k1 base field carrier, stored as a Montgomery residue. -/
abbrev BaseField : Type := FastField Secp256k1.baseFieldSize

/-- Convert from the canonical `Secp256k1.BaseField` into fast Montgomery form. -/
@[inline]
def ofBaseField (x : Secp256k1.BaseField) : BaseField :=
  FastField.ofField x

/-- Ring equivalence between the four-limb representation and the canonical
`Secp256k1.BaseField`. -/
def baseRingEquiv : BaseField ≃+* Secp256k1.BaseField :=
  FastField.ringEquiv Secp256k1.baseFieldSize

end Secp256k1.Fast
