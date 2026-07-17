/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1.Fr.Fast

/-!
# Fast secp256k1 Scalar Field Tests

Regression checks for the executable 256-bit Montgomery representation: the stored residues,
literal round trips, the field operations, and agreement with the canonical
`Secp256k1.ScalarField` model through `toField`.
-/

namespace Secp256k1.Fr.Fast

open Secp256k1 (SCALAR_FIELD_CARD)
open Montgomery.Native256

set_option maxRecDepth 4000

-- Stored Montgomery residues.
#guard (0 : ScalarField).val = 0
#guard (1 : ScalarField).val = Mont256Field.rModModulus SCALAR_FIELD_CARD

-- Numeric literals reduce modulo the prime; `toNat` exits Montgomery form.
#guard (37 : ScalarField).toNat = 37
#guard (SCALAR_FIELD_CARD : ScalarField).toNat = 0
#guard (SCALAR_FIELD_CARD + 37 : ScalarField).toNat = 37

-- Addition (with and without wraparound).
#guard ((SCALAR_FIELD_CARD - 1 : ScalarField) + 2).toNat = 1
#guard ((SCALAR_FIELD_CARD - 1 : ScalarField) + (SCALAR_FIELD_CARD - 1 : ScalarField)).toNat
  = SCALAR_FIELD_CARD - 2

-- Subtraction (with and without borrow).
#guard ((9 : ScalarField) - 5).toNat = 4
#guard ((5 : ScalarField) - 9).toNat = SCALAR_FIELD_CARD - 4

-- Negation.
#guard (-(0 : ScalarField)).toNat = 0
#guard (-(1 : ScalarField)).toNat = SCALAR_FIELD_CARD - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard ((SCALAR_FIELD_CARD - 1 : ScalarField) * (SCALAR_FIELD_CARD - 1 : ScalarField)).toNat = 1
#guard ((12345 : ScalarField) * 12345).toNat = 152399025

-- Exponentiation, including agreement with the canonical field.
#guard ((37 : ScalarField) ^ 0).toNat = 1
#guard ((37 : ScalarField) ^ 1).toNat = 37
#guard ((123456789 : ScalarField) ^ 17).toField = ((123456789 : Secp256k1.ScalarField) ^ 17)
#guard ((123456789 : ScalarField) ^ 255).toField = ((123456789 : Secp256k1.ScalarField) ^ 255)

-- Inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard ((0 : ScalarField)⁻¹).toNat = 0
#guard ((37 : ScalarField)⁻¹ * 37).toNat = 1

-- The Pornin binary-GCD fast path is exact: the raw candidate equals what `inv` returns,
-- i.e. the runtime check passed and the window fallback was not needed.
#guard gcdInvCandidate (modulus := SCALAR_FIELD_CARD) (37 : ScalarField).val
         = ((37 : ScalarField)⁻¹).val
#guard gcdInvCandidate (modulus := SCALAR_FIELD_CARD) (SCALAR_FIELD_CARD - 1 : ScalarField).val
         = ((SCALAR_FIELD_CARD - 1 : ScalarField)⁻¹).val
#guard gcdInvCandidate (modulus := SCALAR_FIELD_CARD) (SCALAR_FIELD_CARD - 2 : ScalarField).val
         = ((SCALAR_FIELD_CARD - 2 : ScalarField)⁻¹).val
#guard gcdInvCandidate (modulus := SCALAR_FIELD_CARD) (2 ^ 200 + 12345 : ScalarField).val
         = ((2 ^ 200 + 12345 : ScalarField)⁻¹).val
#guard ((37 : ScalarField) / 37).toNat = 1
#guard ((37 : ScalarField)⁻¹).toField = ((37 : Secp256k1.ScalarField)⁻¹)
#guard ((37 : ScalarField) ^ (-3 : Int)).toField = ((37 : Secp256k1.ScalarField) ^ (-3 : Int))

-- The precomputed-digit window inversion agrees with the canonical inverse on another value.
#guard ((987654321 : ScalarField)⁻¹).toField = ((987654321 : Secp256k1.ScalarField)⁻¹)

end Secp256k1.Fr.Fast
