/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_381.Basic
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast BLS12-381 Scalar Field

A native 256-bit Montgomery implementation of BLS12-381 scalar arithmetic. The shared
algorithms and proofs live in `CompPoly.Fields.Montgomery.Native256Field`; this module
supplies the BLS12-381 constants and its concrete API.
-/

namespace BLS12_381.Fast

open Montgomery.Native256 (Mont256Field FastField)
open Montgomery.Native256.FastField

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The per-field data realizing BLS12-381's scalar field as a fast 256-bit Montgomery
field. -/
instance instMont256Field : Mont256Field BLS12_381.scalarFieldSize where
  prime := BLS12_381.ScalarField_is_prime
  modulus256 := ⟨0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48⟩
  montgomeryNegInv := 0xfffffffeffffffff
  rModModulus := ⟨0x00000001fffffffe, 0x5884b7fa00034802, 0x998c4fefecbc4ff5, 0x1824b159acc5056f⟩
  r2ModModulus := ⟨0xc999e990f3f29c6d, 0x2b6cedcb87925c23, 0x05d314967254398f, 0x0748d9d99f59ff11⟩
  gcdFinalRounds := 43
  gcdInitU := ⟨0xb9c9191e0831ad2f, 0x3c16d933f8324ac2, 0x6150d8032caa9cfb, 0x1675ab15ed548587⟩

/-- The fast native-word BLS12-381 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField BLS12_381.scalarFieldSize

/-! ## Conversions -/

/-- Convert from the canonical `BLS12_381.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : BLS12_381.ScalarField) : ScalarField :=
  Montgomery.Native256.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and the canonical
`BLS12_381.ScalarField`. -/
def ringEquiv : ScalarField ≃+* BLS12_381.ScalarField :=
  Montgomery.Native256.ringEquiv BLS12_381.scalarFieldSize

end BLS12_381.Fast
