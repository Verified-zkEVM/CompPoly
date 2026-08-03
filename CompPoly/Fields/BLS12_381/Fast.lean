/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_381.Basic
import CompPoly.Fields.Montgomery.Native256Field
import CompPoly.Fields.Montgomery.Native64x8Inv

/-!
# Fast BLS12-381 Scalar Field

Native Montgomery implementations of BLS12-381 scalar arithmetic at both limb radices:
the four-limb (64-bit) carrier from `CompPoly.Fields.Montgomery.Native256Field` and the
eight-limb (32-bit) carrier from `CompPoly.Fields.Montgomery.Native64x8Field`. This
module supplies the BLS12-381 constants for each.
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

/-! ## Eight-limb carrier -/

/-- The per-field data realizing BLS12-381's scalar field as a fast eight-limb
(32-bit-limb) Montgomery field. -/
instance instMont64x8Field : Montgomery.Native64x8.Mont64x8Field BLS12_381.scalarFieldSize where
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
abbrev ScalarField32 : Type := Montgomery.Native64x8.FastField BLS12_381.scalarFieldSize

/-- Ring equivalence between the eight-limb representation and the canonical
`BLS12_381.ScalarField`. -/
def ringEquiv32 : ScalarField32 ≃+* BLS12_381.ScalarField :=
  Montgomery.Native64x8.FastField.ringEquiv BLS12_381.scalarFieldSize

end BLS12_381.Fast
