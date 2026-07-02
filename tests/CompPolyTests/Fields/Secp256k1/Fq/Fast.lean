/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1.Fq.Fast

/-!
# Fast Secp256k1.Fq Base Field Tests

Regression checks for the executable 256-bit Montgomery representation: the stored residues,
the `ofNat`/`toNat` round trip, the field operations, and agreement with the canonical
`Secp256k1.BaseField := ZMod BASE_FIELD_CARD` model through `toField`.
-/

namespace Secp256k1.Fq.Fast

open Secp256k1 (BASE_FIELD_CARD)
open Montgomery.Native256

set_option maxRecDepth 4000

-- Stored Montgomery residues.
#guard raw (0 : BaseField) = 0
#guard raw (1 : BaseField) = rModModulus

-- `ofNat` reduces modulo the prime; `toNat` exits Montgomery form.
#guard toNat (ofNat 37) = 37
#guard toNat (ofNat BASE_FIELD_CARD) = 0
#guard toNat (ofNat (BASE_FIELD_CARD + 37)) = 37

-- Addition (with and without wraparound).
#guard toNat ((ofNat (BASE_FIELD_CARD - 1)) + (2 : BaseField)) = 1
#guard toNat ((ofNat (BASE_FIELD_CARD - 1)) + (ofNat (BASE_FIELD_CARD - 1))) = BASE_FIELD_CARD - 2

-- Subtraction (with and without borrow).
#guard toNat ((9 : BaseField) - (5 : BaseField)) = 4
#guard toNat ((5 : BaseField) - (9 : BaseField)) = BASE_FIELD_CARD - 4

-- Negation.
#guard toNat (-(0 : BaseField)) = 0
#guard toNat (-(1 : BaseField)) = BASE_FIELD_CARD - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard toNat ((ofNat (BASE_FIELD_CARD - 1)) * (ofNat (BASE_FIELD_CARD - 1))) = 1
#guard toNat (square (12345 : BaseField)) = 152399025

-- Exponentiation, including agreement with the canonical field.
#guard toNat ((37 : BaseField) ^ 0) = 1
#guard toNat ((37 : BaseField) ^ 1) = 37
#guard toField ((123456789 : BaseField) ^ 17) = ((123456789 : Secp256k1.BaseField) ^ 17)
#guard toField ((123456789 : BaseField) ^ 255) = ((123456789 : Secp256k1.BaseField) ^ 255)

-- Inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard toNat ((0 : BaseField)⁻¹) = 0
#guard toNat ((37 : BaseField)⁻¹ * (37 : BaseField)) = 1

-- The Pornin binary-GCD fast path is exact: the raw candidate equals what `inv` returns,
-- i.e. the runtime check passed and the window fallback was not needed.
#guard gcdInvCandidate (F := Secp256k1.BaseField) (raw (37 : BaseField)) = raw ((37 : BaseField)⁻¹)
#guard gcdInvCandidate (F := Secp256k1.BaseField) (raw (ofNat (BASE_FIELD_CARD - 1)))
         = raw ((ofNat (BASE_FIELD_CARD - 1) : BaseField)⁻¹)
#guard gcdInvCandidate (F := Secp256k1.BaseField) (raw (ofNat (BASE_FIELD_CARD - 2)))
         = raw ((ofNat (BASE_FIELD_CARD - 2) : BaseField)⁻¹)
#guard gcdInvCandidate (F := Secp256k1.BaseField) (raw (ofNat (2 ^ 200 + 12345)))
         = raw ((ofNat (2 ^ 200 + 12345) : BaseField)⁻¹)
#guard toNat ((37 : BaseField) / (37 : BaseField)) = 1
#guard toField ((37 : BaseField)⁻¹) = ((37 : Secp256k1.BaseField)⁻¹)
#guard toField ((37 : BaseField) ^ (-3 : Int)) = ((37 : Secp256k1.BaseField) ^ (-3 : Int))

-- The precomputed-digit window inversion agrees with the canonical inverse on another value.
#guard toField ((987654321 : BaseField)⁻¹) = ((987654321 : Secp256k1.BaseField)⁻¹)

end Secp256k1.Fq.Fast
