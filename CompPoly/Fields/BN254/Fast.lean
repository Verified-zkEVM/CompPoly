/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.BN254.Basic
public import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BN254 Scalar Field

A native eight-limb Montgomery implementation of BN254 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x8Field`). This module supplies the BN254 constants.
-/

@[expose] public section

namespace BN254.Fast

open Montgomery.Native64x8 (Mont64x8Field FastField GcdData)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- Divstep schedule of the binary-GCD inverse candidate. -/
instance instGcdData : GcdData BN254.scalarFieldSize where
  finalRounds := 41
  initU :=
    ⟨0x1cafd3b2, 0xb542296a, 0x9c820da9, 0xec8811f1, 0x6bd1d274, 0x29bed602, 0xa8ab8d54,
      0x0fb316d8⟩

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
