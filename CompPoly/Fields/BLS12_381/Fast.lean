/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_381.Basic
import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BLS12-381 Scalar Field

A native eight-limb Montgomery implementation of BLS12-381 scalar arithmetic
(`CompPoly.Fields.Montgomery.Native64x8Field`). This module supplies the BLS12-381
constants, including the 64-bit words of the shared GCD inverse candidate.
-/

namespace BLS12_381.Fast

open Montgomery.Native256 (Mont256Field)
open Montgomery.Native64x8 (Mont64x8Field FastField)

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The 64-bit words and divstep schedule consumed by the shared binary-GCD inverse
candidate. -/
instance instMont256Field : Mont256Field BLS12_381.scalarFieldSize where
  modulus256 := ⟨0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48⟩
  montgomeryNegInv := 0xfffffffeffffffff
  gcdFinalRounds := 43
  gcdInitU := ⟨0x408b03b2fe9ec31c, 0x49ada1d522e5e5f4, 0x0a662f5800f31bd7, 0x1f758dcc6fc84e4d⟩

/-- The per-field data realizing BLS12-381's scalar field as a fast eight-limb
(32-bit-limb) Montgomery field. -/
instance instMont64x8Field : Mont64x8Field BLS12_381.scalarFieldSize where
  prime := BLS12_381.ScalarField_is_prime
  modulusLimbs :=
    ⟨0x1, 0xffffffff, 0xfffe5bfe, 0x53bda402, 0x9a1d805, 0x3339d808, 0x299d7d48,
      0x73eda753⟩
  rModModulus :=
    ⟨0xfffffffe, 0x1, 0x34802, 0x5884b7fa, 0xecbc4ff5, 0x998c4fef, 0xacc5056f,
      0x1824b159⟩
  r2ModModulus :=
    ⟨0xf3f29c6d, 0xc999e990, 0x87925c23, 0x2b6cedcb, 0x7254398f, 0x5d31496, 0x9f59ff11,
      0x748d9d9⟩
  montgomeryNegInv := 0xffffffff

/-- The eight-limb BLS12-381 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BLS12_381.scalarFieldSize

/-- Convert from the canonical `BLS12_381.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_381.ScalarField) : ScalarField :=
  FastField.ofField x

/-- Ring equivalence between the eight-limb representation and the canonical
`BLS12_381.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_381.ScalarField :=
  FastField.ringEquiv BLS12_381.scalarFieldSize

end BLS12_381.Fast
