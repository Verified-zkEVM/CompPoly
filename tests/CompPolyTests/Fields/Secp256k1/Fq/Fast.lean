/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1.Fq.Fast

/-!
# Fast secp256k1 Base Field Tests

Regression checks for the executable 256-bit Montgomery representation: the stored residues,
literal round trips, the field operations, and agreement with the canonical
`Secp256k1.BaseField` model through `toField`.
-/

namespace Secp256k1.Fq.Fast

open Secp256k1 (BASE_FIELD_CARD)
open Montgomery.Native256

set_option maxRecDepth 4000

-- Stored Montgomery residues.
#guard (0 : BaseField).val = 0
#guard (1 : BaseField).val = Mont256Field.rModModulus BASE_FIELD_CARD

-- Numeric literals reduce modulo the prime; `toNat` exits Montgomery form.
#guard (37 : BaseField).toNat = 37
#guard (BASE_FIELD_CARD : BaseField).toNat = 0
#guard (BASE_FIELD_CARD + 37 : BaseField).toNat = 37

-- Addition (with and without wraparound).
#guard ((BASE_FIELD_CARD - 1 : BaseField) + 2).toNat = 1
#guard ((BASE_FIELD_CARD - 1 : BaseField) + (BASE_FIELD_CARD - 1 : BaseField)).toNat
  = BASE_FIELD_CARD - 2

-- Subtraction (with and without borrow).
#guard ((9 : BaseField) - 5).toNat = 4
#guard ((5 : BaseField) - 9).toNat = BASE_FIELD_CARD - 4

-- Negation.
#guard (-(0 : BaseField)).toNat = 0
#guard (-(1 : BaseField)).toNat = BASE_FIELD_CARD - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard ((BASE_FIELD_CARD - 1 : BaseField) * (BASE_FIELD_CARD - 1 : BaseField)).toNat = 1
#guard ((12345 : BaseField) * 12345).toNat = 152399025

-- Exponentiation, including agreement with the canonical field.
#guard ((37 : BaseField) ^ 0).toNat = 1
#guard ((37 : BaseField) ^ 1).toNat = 37
#guard ((123456789 : BaseField) ^ 17).toField = ((123456789 : Secp256k1.BaseField) ^ 17)
#guard ((123456789 : BaseField) ^ 255).toField = ((123456789 : Secp256k1.BaseField) ^ 255)

-- Inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard ((0 : BaseField)⁻¹).toNat = 0
#guard ((37 : BaseField)⁻¹ * 37).toNat = 1

-- The Pornin binary-GCD fast path is exact: the raw candidate equals what `inv` returns,
-- i.e. the runtime check passed and the window fallback was not needed.
#guard gcdInvCandidate (modulus := BASE_FIELD_CARD) (37 : BaseField).val
         = ((37 : BaseField)⁻¹).val
#guard gcdInvCandidate (modulus := BASE_FIELD_CARD) (BASE_FIELD_CARD - 1 : BaseField).val
         = ((BASE_FIELD_CARD - 1 : BaseField)⁻¹).val
#guard gcdInvCandidate (modulus := BASE_FIELD_CARD) (BASE_FIELD_CARD - 2 : BaseField).val
         = ((BASE_FIELD_CARD - 2 : BaseField)⁻¹).val
#guard gcdInvCandidate (modulus := BASE_FIELD_CARD) (2 ^ 200 + 12345 : BaseField).val
         = ((2 ^ 200 + 12345 : BaseField)⁻¹).val
#guard ((37 : BaseField) / 37).toNat = 1
#guard ((37 : BaseField)⁻¹).toField = ((37 : Secp256k1.BaseField)⁻¹)
#guard ((37 : BaseField) ^ (-3 : Int)).toField = ((37 : Secp256k1.BaseField) ^ (-3 : Int))

-- The precomputed-digit window inversion agrees with the canonical inverse on another value.
#guard ((987654321 : BaseField)⁻¹).toField = ((987654321 : Secp256k1.BaseField)⁻¹)

end Secp256k1.Fq.Fast
