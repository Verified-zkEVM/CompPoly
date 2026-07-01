/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1.Fr.Fast

/-!
# Fast Secp256k1.Fr Scalar Field Tests

Regression checks for the executable 256-bit Montgomery representation: the stored residues,
the `ofNat`/`toNat` round trip, the field operations, and agreement with the canonical
`Secp256k1.ScalarField := ZMod SCALAR_FIELD_CARD` model through `toField`.
-/

namespace Secp256k1.Fr.Fast

open Secp256k1 (SCALAR_FIELD_CARD)
open Montgomery.Native256

set_option maxRecDepth 4000

-- Stored Montgomery residues.
#guard raw (0 : ScalarField) = 0
#guard raw (1 : ScalarField) = rModModulus

-- `ofNat` reduces modulo the prime; `toNat` exits Montgomery form.
#guard toNat (ofNat 37) = 37
#guard toNat (ofNat SCALAR_FIELD_CARD) = 0
#guard toNat (ofNat (SCALAR_FIELD_CARD + 37)) = 37

-- Addition (with and without wraparound).
#guard toNat ((ofNat (SCALAR_FIELD_CARD - 1)) + (2 : ScalarField)) = 1
#guard toNat ((ofNat (SCALAR_FIELD_CARD - 1)) + (ofNat (SCALAR_FIELD_CARD - 1)))
  = SCALAR_FIELD_CARD - 2

-- Subtraction (with and without borrow).
#guard toNat ((9 : ScalarField) - (5 : ScalarField)) = 4
#guard toNat ((5 : ScalarField) - (9 : ScalarField)) = SCALAR_FIELD_CARD - 4

-- Negation.
#guard toNat (-(0 : ScalarField)) = 0
#guard toNat (-(1 : ScalarField)) = SCALAR_FIELD_CARD - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard toNat ((ofNat (SCALAR_FIELD_CARD - 1)) * (ofNat (SCALAR_FIELD_CARD - 1))) = 1
#guard toNat (square (12345 : ScalarField)) = 152399025

-- Exponentiation, including agreement with the canonical field.
#guard toNat ((37 : ScalarField) ^ 0) = 1
#guard toNat ((37 : ScalarField) ^ 1) = 37
#guard toField ((123456789 : ScalarField) ^ 17) = ((123456789 : Secp256k1.ScalarField) ^ 17)
#guard toField ((123456789 : ScalarField) ^ 255) = ((123456789 : Secp256k1.ScalarField) ^ 255)

-- Inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard toNat ((0 : ScalarField)⁻¹) = 0
#guard toNat ((37 : ScalarField)⁻¹ * (37 : ScalarField)) = 1
#guard toNat ((37 : ScalarField) / (37 : ScalarField)) = 1
#guard toField ((37 : ScalarField)⁻¹) = ((37 : Secp256k1.ScalarField)⁻¹)
#guard toField ((37 : ScalarField) ^ (-3 : Int)) = ((37 : Secp256k1.ScalarField) ^ (-3 : Int))

-- The precomputed-digit window inversion agrees with the canonical inverse on another value.
#guard toField ((987654321 : ScalarField)⁻¹) = ((987654321 : Secp256k1.ScalarField)⁻¹)

end Secp256k1.Fr.Fast
