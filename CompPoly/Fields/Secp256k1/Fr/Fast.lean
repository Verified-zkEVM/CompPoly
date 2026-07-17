/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast secp256k1 Scalar Field

A native 256-bit Montgomery implementation of secp256k1 scalar-field arithmetic. The shared
algorithms and proofs live in `CompPoly.Fields.Montgomery.Native256Field`; this module
supplies the scalar-field constants and its concrete API.
-/

namespace Secp256k1.Fr.Fast

open Montgomery.Native256 (Mont256Field FastField)
open Montgomery.Native256.FastField

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The per-field data realizing the secp256k1 scalar field as a fast 256-bit Montgomery
field. -/
instance instMont256Field : Mont256Field Secp256k1.SCALAR_FIELD_CARD where
  prime := Secp256k1.ScalarField_is_prime
  modulus256 := ⟨0xbfd25e8cd0364141, 0xbaaedce6af48a03b, 0xfffffffffffffffe, 0xffffffffffffffff⟩
  montgomeryNegInv := 0x4b0dff665588b13f
  rModModulus := ⟨0x402da1732fc9bebf, 0x4551231950b75fc4, 0x0000000000000001, 0x0000000000000000⟩
  r2ModModulus := ⟨0x896cf21467d7d140, 0x741496c20e7cf878, 0xe697f5e45bcd07c6, 0x9d671cd581c69bc5⟩
  gcdFinalRounds := 45
  gcdInitU := ⟨0xe6053d857d7d4222, 0x42599230f99c6a25, 0x215bb648c78ffa6c, 0xbfde432688ae6725⟩

/-- The fast native-word secp256k1 scalar field carrier, stored as a Montgomery residue. -/
abbrev ScalarField : Type := FastField Secp256k1.SCALAR_FIELD_CARD

/-! ## Conversions -/

/-- Convert from the canonical `Secp256k1.ScalarField` field into fast Montgomery form. -/
@[inline]
def ofField (x : Secp256k1.ScalarField) : ScalarField :=
  Montgomery.Native256.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and the canonical
`Secp256k1.ScalarField`. -/
def ringEquiv : ScalarField ≃+* Secp256k1.ScalarField :=
  Montgomery.Native256.ringEquiv Secp256k1.SCALAR_FIELD_CARD

end Secp256k1.Fr.Fast
