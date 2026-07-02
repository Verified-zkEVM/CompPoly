/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_381.Fast

/-!
# Fast BLS12_381 Scalar Field Tests

Regression checks for the executable 256-bit Montgomery representation: the stored residues,
the `ofNat`/`toNat` round trip, the field operations, and agreement with the canonical
`BLS12_381.ScalarField := ZMod scalarFieldSize` model through `toField`.
-/

namespace BLS12_381.Fast

open BLS12_381 (scalarFieldSize)
open Montgomery.Native256

set_option maxRecDepth 4000

-- Stored Montgomery residues.
#guard raw (0 : ScalarField) = 0
#guard raw (1 : ScalarField) = rModModulus

-- `ofNat` reduces modulo the prime; `toNat` exits Montgomery form.
#guard toNat (ofNat 37) = 37
#guard toNat (ofNat scalarFieldSize) = 0
#guard toNat (ofNat (scalarFieldSize + 37)) = 37

-- Addition (with and without wraparound).
#guard toNat ((ofNat (scalarFieldSize - 1)) + (2 : ScalarField)) = 1
#guard toNat ((ofNat (scalarFieldSize - 1)) + (ofNat (scalarFieldSize - 1))) = scalarFieldSize - 2

-- Subtraction (with and without borrow).
#guard toNat ((9 : ScalarField) - (5 : ScalarField)) = 4
#guard toNat ((5 : ScalarField) - (9 : ScalarField)) = scalarFieldSize - 4

-- Negation.
#guard toNat (-(0 : ScalarField)) = 0
#guard toNat (-(1 : ScalarField)) = scalarFieldSize - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard toNat ((ofNat (scalarFieldSize - 1)) * (ofNat (scalarFieldSize - 1))) = 1
#guard toNat (square (12345 : ScalarField)) = 152399025

-- Exponentiation, including agreement with the canonical field.
#guard toNat ((37 : ScalarField) ^ 0) = 1
#guard toNat ((37 : ScalarField) ^ 1) = 37
#guard toField ((123456789 : ScalarField) ^ 17) = ((123456789 : BLS12_381.ScalarField) ^ 17)
#guard toField ((123456789 : ScalarField) ^ 255) = ((123456789 : BLS12_381.ScalarField) ^ 255)

-- Inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard toNat ((0 : ScalarField)⁻¹) = 0
#guard toNat ((37 : ScalarField)⁻¹ * (37 : ScalarField)) = 1

-- The Pornin binary-GCD fast path is exact: the raw candidate equals what `inv` returns,
-- i.e. the runtime check passed and the window fallback was not needed.
#guard gcdInvCandidate (F := BLS12_381.ScalarField) (raw (37 : ScalarField))
         = raw ((37 : ScalarField)⁻¹)
#guard gcdInvCandidate (F := BLS12_381.ScalarField) (raw (ofNat (scalarFieldSize - 1)))
         = raw ((ofNat (scalarFieldSize - 1) : ScalarField)⁻¹)
#guard gcdInvCandidate (F := BLS12_381.ScalarField) (raw (ofNat (scalarFieldSize - 2)))
         = raw ((ofNat (scalarFieldSize - 2) : ScalarField)⁻¹)
#guard gcdInvCandidate (F := BLS12_381.ScalarField) (raw (ofNat (2 ^ 200 + 12345)))
         = raw ((ofNat (2 ^ 200 + 12345) : ScalarField)⁻¹)
#guard toNat ((37 : ScalarField) / (37 : ScalarField)) = 1
#guard toField ((37 : ScalarField)⁻¹) = ((37 : BLS12_381.ScalarField)⁻¹)
#guard toField ((37 : ScalarField) ^ (-3 : Int)) = ((37 : BLS12_381.ScalarField) ^ (-3 : Int))

-- The precomputed-digit window inversion agrees with the canonical inverse on another value.
#guard toField ((987654321 : ScalarField)⁻¹) = ((987654321 : BLS12_381.ScalarField)⁻¹)

end BLS12_381.Fast
