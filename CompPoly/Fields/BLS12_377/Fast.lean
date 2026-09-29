/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.BLS12_377.Basic
public import CompPoly.Fields.Montgomery.Native64x4Inv

/-!
# Fast BLS12-377 Scalar Field

A native four-limb Montgomery implementation of BLS12-377 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x4Field`). This module supplies the BLS12-377
constants.
-/

@[expose] public section

namespace BLS12_377.Fast

open Montgomery.Native64x4 (Mont64x4Field FastField GcdData)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- Divstep schedule of the binary-GCD inverse candidate. -/
instance instGcdData : GcdData BLS12_377.scalarFieldSize where
  finalRounds := 39
  initU := ⟨0x50d904ef75fb587f, 0x25a2b48c71615c44, 0x8203611dc5f581c3, 0xd6a3a20c872ad35⟩

/-- The per-field data realizing BLS12-377's scalar field as a fast four-limb Montgomery
field. -/
instance instMont64x4Field : Mont64x4Field BLS12_377.scalarFieldSize where
  prime := BLS12_377.ScalarField_is_prime
  modulusLimbs :=
    ⟨0xa11800000000001, 0x59aa76fed0000001, 0x60b44d1e5c37b001, 0x12ab655e9a2ca556⟩
  rModModulus :=
    ⟨0x7d1c7ffffffffff3, 0x7257f50f6ffffff2, 0x16d81575512c0fee, 0xd4bda322bbb9a9d⟩
  r2ModModulus :=
    ⟨0x25d577bab861857b, 0xcc2c27b58860591f, 0xa7cc008fe5dc8593, 0x11fdae7eff1c939⟩
  montgomeryNegInv := 0xa117fffffffffff

/-- The four-limb BLS12-377 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BLS12_377.scalarFieldSize

/-- Convert from the canonical `BLS12_377.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_377.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the four-limb representation and the canonical
`BLS12_377.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_377.ScalarField :=
  FastField.ringEquiv BLS12_377.scalarFieldSize

end BLS12_377.Fast
