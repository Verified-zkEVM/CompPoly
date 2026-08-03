/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_377.Basic
import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BLS12-377 Scalar Field

A native eight-limb Montgomery implementation of BLS12-377 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x8Field`). This module supplies the BLS12-377
constants, including the 64-bit words of the shared GCD inverse candidate.
-/

namespace BLS12_377.Fast

open Montgomery.Native256 (Mont256Field)
open Montgomery.Native64x8 (Mont64x8Field FastField)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The 64-bit words and divstep schedule consumed by the shared binary-GCD inverse
candidate. -/
instance instMont256Field : Mont256Field BLS12_377.scalarFieldSize where
  modulus256 := ⟨0x0a11800000000001, 0x59aa76fed0000001, 0x60b44d1e5c37b001, 0x12ab655e9a2ca556⟩
  montgomeryNegInv := 0x0a117fffffffffff
  gcdFinalRounds := 39
  gcdInitU := ⟨0xa5707af094e01332, 0xf9af464a6f1abbfb, 0x65dbc6f77f75c179, 0x10e76cd3c9364c65⟩

/-- The per-field data realizing BLS12-377's scalar field as a fast eight-limb
(32-bit-limb) Montgomery field. -/
instance instMont64x8Field : Mont64x8Field BLS12_377.scalarFieldSize where
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
abbrev ScalarField : Type := FastField BLS12_377.scalarFieldSize

/-- Convert from the canonical `BLS12_377.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_377.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the eight-limb representation and the canonical
`BLS12_377.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_377.ScalarField :=
  FastField.ringEquiv BLS12_377.scalarFieldSize

end BLS12_377.Fast
