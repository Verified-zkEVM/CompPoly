/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.BN254.Basic
public import CompPoly.Fields.Montgomery.Native64x4Inv

/-!
# Fast BN254 Scalar Field

A native four-limb Montgomery implementation of BN254 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x4Field`). This module supplies the BN254 constants.
-/

@[expose] public section

namespace BN254.Fast

open Montgomery.Native64x4 (Mont64x4Field FastField GcdData)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- Divstep schedule of the binary-GCD inverse candidate. -/
instance instGcdData : GcdData BN254.scalarFieldSize where
  finalRounds := 41
  initU := ⟨0x31db48599a71d3a, 0x21a9c717fffa68b1, 0xe09ca8b1e4e66050, 0x12e69c542f33d99a⟩

/-- The per-field data realizing BN254's scalar field as a fast four-limb Montgomery
field. -/
instance instMont64x4Field : Mont64x4Field BN254.scalarFieldSize where
  prime := BN254.ScalarField_is_prime
  modulusLimbs :=
    ⟨0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029⟩
  rModModulus :=
    ⟨0xac96341c4ffffffb, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0xe0a77c19a07df2f⟩
  r2ModModulus :=
    ⟨0x1bb8e645ae216da7, 0x53fe3ab1e35c59e3, 0x8c49833d53bb8085, 0x216d0b17f4e44a5⟩
  montgomeryNegInv := 0xc2e1f593efffffff

/-- The four-limb BN254 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BN254.scalarFieldSize

/-- Convert from the canonical `BN254.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BN254.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the four-limb representation and the canonical
`BN254.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BN254.ScalarField :=
  FastField.ringEquiv BN254.scalarFieldSize

end BN254.Fast
