/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_381.Fast

/-!
# Fast BLS12-381 Scalar Field Tests

Regression checks for the executable eight-limb Montgomery representation: the stored
residues, literal round trips, the field operations, the checked binary-GCD inversion, and
agreement with the canonical `BLS12_381.ScalarField` model through `toField`.
-/

namespace BLS12_381.Fast

open BLS12_381 (scalarFieldSize)
open Montgomery.Native64x8

set_option maxRecDepth 4000

-- Stored Montgomery residues.
#guard (0 : ScalarField).val = Limbs8.zero
#guard (1 : ScalarField).val = Mont64x8Field.rModModulus scalarFieldSize

-- Numeric literals reduce modulo the prime; `toNat` exits Montgomery form.
#guard (37 : ScalarField).toNat = 37
#guard (scalarFieldSize : ScalarField).toNat = 0
#guard (scalarFieldSize + 37 : ScalarField).toNat = 37

-- Addition (with and without wraparound).
#guard ((scalarFieldSize - 1 : ScalarField) + 2).toNat = 1
#guard ((scalarFieldSize - 1 : ScalarField) + (scalarFieldSize - 1 : ScalarField)).toNat
  = scalarFieldSize - 2

-- Subtraction (with and without borrow).
#guard ((9 : ScalarField) - 5).toNat = 4
#guard ((5 : ScalarField) - 9).toNat = scalarFieldSize - 4

-- Negation.
#guard (-(0 : ScalarField)).toNat = 0
#guard (-(1 : ScalarField)).toNat = scalarFieldSize - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard ((scalarFieldSize - 1 : ScalarField) * (scalarFieldSize - 1 : ScalarField)).toNat = 1
#guard ((12345 : ScalarField) * 12345).toNat = 152399025

-- Exponentiation, including agreement with the canonical field.
#guard ((37 : ScalarField) ^ 0).toNat = 1
#guard ((37 : ScalarField) ^ 1).toNat = 37
#guard ((123456789 : ScalarField) ^ 17).toField = ((123456789 : BLS12_381.ScalarField) ^ 17)
#guard ((123456789 : ScalarField) ^ 255).toField = ((123456789 : BLS12_381.ScalarField) ^ 255)

-- Fermat inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard ((0 : ScalarField)⁻¹).toNat = 0
#guard ((37 : ScalarField)⁻¹ * 37).toNat = 1
#guard ((37 : ScalarField) / 37).toNat = 1
#guard ((37 : ScalarField)⁻¹).toField = ((37 : BLS12_381.ScalarField)⁻¹)
#guard ((37 : ScalarField) ^ (-3 : Int)).toField = ((37 : BLS12_381.ScalarField) ^ (-3 : Int))

-- The checked binary-GCD inversion agrees with the Fermat inverse; the raw-candidate guard
-- detects a silent fallback (`invGcd = ⁻¹` alone cannot: a miss just takes the slow path).
#guard ((37 : ScalarField).invGcd * 37).toNat = 1
#guard ((scalarFieldSize - 1 : ScalarField).invGcd).toField
  = ((scalarFieldSize - 1 : BLS12_381.ScalarField)⁻¹)
#guard ((2 ^ 200 + 12345 : ScalarField).invGcd).toField
  = ((2 ^ 200 + 12345 : BLS12_381.ScalarField)⁻¹)
#guard (987654321 : ScalarField).invGcd.toField = ((987654321 : BLS12_381.ScalarField)⁻¹)
#guard (37 : ScalarField).invGcd.val
  = gcdInvCandidate scalarFieldSize (Mont64x8Field.modulusLimbs scalarFieldSize)
      (Mont64x8Field.montgomeryNegInv scalarFieldSize) (37 : ScalarField).val

-- The Fermat fallback, exercised directly (the fast path never takes it).
#guard montPow (Mont64x8Field.modulusLimbs scalarFieldSize)
    (Mont64x8Field.montgomeryNegInv scalarFieldSize) (Mont64x8Field.rModModulus scalarFieldSize)
    (37 : ScalarField).val (scalarFieldSize - 2)
  = ((37 : ScalarField)⁻¹).val

end BLS12_381.Fast
