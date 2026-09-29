/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.BLS12_381.Basic
public import CompPoly.Fields.Montgomery.Native64x4Inv

/-!
# Fast BLS12-381 Scalar Field

A native four-limb Montgomery implementation of BLS12-381 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x4Field`). This module supplies the BLS12-381
constants.
-/

@[expose] public section

namespace BLS12_381.Fast

open Montgomery.Native64x4 (Mont64x4Field FastField GcdData)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- Divstep schedule of the binary-GCD inverse candidate. -/
instance instGcdData : GcdData BLS12_381.scalarFieldSize where
  finalRounds := 43
  initU := ⟨0x92413fd93c25fbb9, 0x69ef6a08aca8f1e3, 0xbdff4014f383b8a5, 0x2d9fa11995e2391a⟩

/-- The per-field data realizing BLS12-381's scalar field as a fast four-limb Montgomery
field. -/
instance instMont64x4Field : Mont64x4Field BLS12_381.scalarFieldSize where
  prime := BLS12_381.ScalarField_is_prime
  modulusLimbs :=
    ⟨0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48⟩
  rModModulus :=
    ⟨0x1fffffffe, 0x5884b7fa00034802, 0x998c4fefecbc4ff5, 0x1824b159acc5056f⟩
  r2ModModulus :=
    ⟨0xc999e990f3f29c6d, 0x2b6cedcb87925c23, 0x5d314967254398f, 0x748d9d99f59ff11⟩
  montgomeryNegInv := 0xfffffffeffffffff

/-- The four-limb BLS12-381 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BLS12_381.scalarFieldSize

/-- Convert from the canonical `BLS12_381.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_381.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the four-limb representation and the canonical
`BLS12_381.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_381.ScalarField :=
  FastField.ringEquiv BLS12_381.scalarFieldSize

end BLS12_381.Fast
