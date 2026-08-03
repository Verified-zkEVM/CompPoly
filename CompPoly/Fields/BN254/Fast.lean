/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Basic
import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BN254 Scalar Field

A native eight-limb Montgomery implementation of BN254 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x8Field`). This module supplies the BN254
constants, including the 64-bit words of the shared GCD inverse candidate.
-/

namespace BN254.Fast

open Montgomery.Native256 (Mont256Field)
open Montgomery.Native64x8 (Mont64x8Field FastField)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The 64-bit words and divstep schedule consumed by the shared binary-GCD inverse
candidate. -/
instance instMont256Field : Mont256Field BN254.scalarFieldSize where
  modulus256 := ⟨0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029⟩
  montgomeryNegInv := 0xc2e1f593efffffff
  gcdFinalRounds := 41
  gcdInitU := ⟨0xb542296a1cafd3b2, 0xec8811f19c820da9, 0x29bed6026bd1d274, 0x0fb316d8a8ab8d54⟩

/-- The per-field data realizing BN254's scalar field as a fast eight-limb (32-bit-limb)
Montgomery field. -/
instance instMont64x8Field : Mont64x8Field BN254.scalarFieldSize where
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
abbrev ScalarField : Type := FastField BN254.scalarFieldSize

/-- Convert from the canonical `BN254.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BN254.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the eight-limb representation and the canonical
`BN254.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BN254.ScalarField :=
  FastField.ringEquiv BN254.scalarFieldSize

end BN254.Fast
