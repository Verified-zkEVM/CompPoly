/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Basic
import CompPoly.Fields.Montgomery.Native256Field
import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BN254 Scalar Field

Native Montgomery implementations of BN254 scalar arithmetic at both limb radices: the
four-limb (64-bit) carrier from `CompPoly.Fields.Montgomery.Native256Field` and the
eight-limb (32-bit) carrier from `CompPoly.Fields.Montgomery.Native64x8Field`. This module
supplies the BN254 constants for each.
-/

namespace BN254.Fast

open Montgomery.Native256 (Mont256Field FastField)
open Montgomery.Native256.FastField

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The per-field data realizing BN254's scalar field as a fast 256-bit Montgomery field. -/
instance instMont256Field : Mont256Field BN254.scalarFieldSize where
  prime := BN254.ScalarField_is_prime
  modulus256 := ⟨0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029⟩
  montgomeryNegInv := 0xc2e1f593efffffff
  rModModulus := ⟨0xac96341c4ffffffb, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f⟩
  r2ModModulus := ⟨0x1bb8e645ae216da7, 0x53fe3ab1e35c59e3, 0x8c49833d53bb8085, 0x0216d0b17f4e44a5⟩
  gcdFinalRounds := 41
  gcdInitU := ⟨0x1f7ca21e7fcb111b, 0x61a09399fcfe8a6c, 0x1438cc5aab55aedb, 0x020c9ba0aeb6b6c7⟩

/-- The fast native-word BN254 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BN254.scalarFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `BN254.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BN254.ScalarField) : ScalarField :=
  Montgomery.Native256.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and the canonical
`BN254.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BN254.ScalarField :=
  Montgomery.Native256.ringEquiv BN254.scalarFieldSize

/-! ## Eight-limb carrier -/

/-- The per-field data realizing BN254's scalar field as a fast eight-limb (32-bit-limb)
Montgomery field. -/
instance instMont64x8Field : Montgomery.Native64x8.Mont64x8Field BN254.scalarFieldSize where
  prime := BN254.ScalarField_is_prime
  modulusLimbs :=
    ⟨0xf0000001, 0x43e1f593, 0x79b97091, 0x2833e848, 0x8181585d, 0xb85045b6, 0xe131a029,
      0x30644e72⟩
  rModModulus :=
    ⟨0x4ffffffb, 0xac96341c, 0x9f60cd29, 0x36fc7695, 0x7879462e, 0x666ea36f, 0x9a07df2f,
      0xe0a77c1⟩
  r2ModModulus :=
    ⟨0xae216da7, 0x1bb8e645, 0xe35c59e3, 0x53fe3ab1, 0x53bb8085, 0x8c49833d, 0x7f4e44a5,
      0x216d0b1⟩
  montgomeryNegInv := 0xefffffff

/-- The eight-limb BN254 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField32 : Type := Montgomery.Native64x8.FastField BN254.scalarFieldSize

/-- Ring equivalence between the eight-limb representation and the canonical
`BN254.ScalarField`. -/
def ringEquiv32 : ScalarField32 ≃+* BN254.ScalarField :=
  Montgomery.Native64x8.FastField.ringEquiv BN254.scalarFieldSize

end BN254.Fast
