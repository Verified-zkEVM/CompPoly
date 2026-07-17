/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast secp256k1 Base Field

A native 256-bit Montgomery implementation of secp256k1 base-field arithmetic. The shared
algorithms and proofs live in `CompPoly.Fields.Montgomery.Native256Field`; this module
supplies the base-field constants and its concrete API.
-/

namespace Secp256k1.Fq.Fast

open Montgomery.Native256 (Mont256Field FastField)
open Montgomery.Native256.FastField

set_option exponentiation.threshold 1100

/-! ## Parameters and carrier -/

/-- The per-field data realizing the secp256k1 base field as a fast 256-bit Montgomery
field. -/
instance instMont256Field : Mont256Field Secp256k1.BASE_FIELD_CARD where
  prime := Secp256k1.BaseField_is_prime
  modulus256 := ⟨0xfffffffefffffc2f, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff⟩
  montgomeryNegInv := 0xd838091dd2253531
  rModModulus := ⟨0x00000001000003d1, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000⟩
  r2ModModulus := ⟨0x000007a2000e90a1, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000⟩
  gcdFinalRounds := 45
  gcdInitU := ⟨0x795f6a608d461504, 0x00003d10015d8f1b, 0x0000000000000004, 0x0000000000000000⟩

/-- The fast native-word secp256k1 base field carrier, stored as a Montgomery residue. -/
abbrev BaseField : Type := FastField Secp256k1.BASE_FIELD_CARD

/-! ## Conversions -/

/-- Convert from the canonical `Secp256k1.BaseField` field into fast Montgomery form. -/
@[inline]
def ofField (x : Secp256k1.BaseField) : BaseField :=
  Montgomery.Native256.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and the canonical
`Secp256k1.BaseField`. -/
def ringEquiv : BaseField ≃+* Secp256k1.BaseField :=
  Montgomery.Native256.ringEquiv Secp256k1.BASE_FIELD_CARD

end Secp256k1.Fq.Fast
