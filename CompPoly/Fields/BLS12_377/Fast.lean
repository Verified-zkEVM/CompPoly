/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_377.Basic
import CompPoly.Fields.Montgomery.Native256Field
import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BLS12-377 Scalar Field

Native Montgomery implementations of BLS12-377 scalar arithmetic at both limb radices:
the four-limb (64-bit) carrier from `CompPoly.Fields.Montgomery.Native256Field` and the
eight-limb (32-bit) carrier from `CompPoly.Fields.Montgomery.Native64x8Field`. This
module supplies the BLS12-377 constants for each.
-/

namespace BLS12_377.Fast

open Montgomery.Native256 (Mont256Field FastField)
open Montgomery.Native256.FastField

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The per-field data realizing BLS12-377's scalar field as a fast 256-bit Montgomery
field. -/
instance instMont256Field : Mont256Field BLS12_377.scalarFieldSize where
  prime := BLS12_377.ScalarField_is_prime
  modulus256 := ⟨0x0a11800000000001, 0x59aa76fed0000001, 0x60b44d1e5c37b001, 0x12ab655e9a2ca556⟩
  montgomeryNegInv := 0x0a117fffffffffff
  rModModulus := ⟨0x7d1c7ffffffffff3, 0x7257f50f6ffffff2, 0x16d81575512c0fee, 0x0d4bda322bbb9a9d⟩
  r2ModModulus := ⟨0x25d577bab861857b, 0xcc2c27b58860591f, 0xa7cc008fe5dc8593, 0x011fdae7eff1c939⟩
  gcdFinalRounds := 39
  gcdInitU := ⟨0xf40f5e9a5a6ba1a2, 0xa5b1631855d84c9b, 0x091b4dd66483d66f, 0x03a25ffc01b45852⟩

/-- The fast native-word BLS12-377 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BLS12_377.scalarFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `BLS12_377.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_377.ScalarField) : ScalarField :=
  Montgomery.Native256.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and the canonical
`BLS12_377.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_377.ScalarField :=
  Montgomery.Native256.ringEquiv BLS12_377.scalarFieldSize

/-! ## Eight-limb carrier -/

/-- The per-field data realizing BLS12-377's scalar field as a fast eight-limb
(32-bit-limb) Montgomery field. -/
instance instMont64x8Field : Montgomery.Native64x8.Mont64x8Field BLS12_377.scalarFieldSize where
  prime := BLS12_377.ScalarField_is_prime
  modulusLimbs :=
    ⟨0x1, 0xa118000, 0xd0000001, 0x59aa76fe, 0x5c37b001, 0x60b44d1e, 0x9a2ca556,
      0x12ab655e⟩
  rModModulus :=
    ⟨0xfffffff3, 0x7d1c7fff, 0x6ffffff2, 0x7257f50f, 0x512c0fee, 0x16d81575, 0x2bbb9a9d,
      0xd4bda32⟩
  r2ModModulus :=
    ⟨0xb861857b, 0x25d577ba, 0x8860591f, 0xcc2c27b5, 0xe5dc8593, 0xa7cc008f, 0xeff1c939,
      0x11fdae7⟩
  montgomeryNegInv := 0xffffffff

/-- The eight-limb BLS12-377 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField32 : Type := Montgomery.Native64x8.FastField BLS12_377.scalarFieldSize

/-- Ring equivalence between the eight-limb representation and the canonical
`BLS12_377.ScalarField`. -/
def ringEquiv32 : ScalarField32 ≃+* BLS12_377.ScalarField :=
  Montgomery.Native64x8.FastField.ringEquiv BLS12_377.scalarFieldSize

end BLS12_377.Fast
