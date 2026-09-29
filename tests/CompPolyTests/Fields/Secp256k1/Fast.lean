/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public meta import CompPoly.Fields.Secp256k1.Fast

/-!
# Fast secp256k1 Field Tests

Regression checks for the eight-limb Montgomery scalar and base fields, whose moduli have
bit 255 set: residues, literal round trips, field operations including the carry paths,
the checked binary-GCD inversion, and agreement with the canonical `ZMod` models.
-/

public meta section

namespace Secp256k1.Fast

open Secp256k1 (SCALAR_FIELD_CARD BASE_FIELD_CARD)
open Montgomery.Native64x8

set_option maxRecDepth 4000

/-! ## Scalar field -/

-- Stored Montgomery residues.
#guard (0 : ScalarField).val = Limbs8.zero
#guard (1 : ScalarField).val = Mont64x8Field.rModModulus SCALAR_FIELD_CARD

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
#guard ((SCALAR_FIELD_CARD - 1 : ScalarField) * (SCALAR_FIELD_CARD - 1 : ScalarField)).toNat
  = 1
#guard ((12345 : ScalarField) * 12345).toNat = 152399025
#guard ((SCALAR_FIELD_CARD - 2 : ScalarField) * (SCALAR_FIELD_CARD - 3 : ScalarField)).toField
  = ((SCALAR_FIELD_CARD - 2 : Secp256k1.ScalarField) * (SCALAR_FIELD_CARD - 3))
#guard ((2 ^ 255 + 12345 : ScalarField) * (2 ^ 255 + 67890 : ScalarField)).toField
  = ((2 ^ 255 + 12345 : Secp256k1.ScalarField) * (2 ^ 255 + 67890))

-- Exponentiation, including agreement with the canonical field.
#guard ((37 : ScalarField) ^ 0).toNat = 1
#guard ((37 : ScalarField) ^ 1).toNat = 37
#guard ((123456789 : ScalarField) ^ 17).toField = ((123456789 : Secp256k1.ScalarField) ^ 17)
#guard ((123456789 : ScalarField) ^ 255).toField
  = ((123456789 : Secp256k1.ScalarField) ^ 255)

-- Fermat inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard ((0 : ScalarField)⁻¹).toNat = 0
#guard ((37 : ScalarField)⁻¹ * 37).toNat = 1
#guard ((37 : ScalarField) / 37).toNat = 1
#guard ((37 : ScalarField)⁻¹).toField = ((37 : Secp256k1.ScalarField)⁻¹)
#guard ((37 : ScalarField) ^ (-3 : Int)).toField = ((37 : Secp256k1.ScalarField) ^ (-3 : Int))

-- The checked binary-GCD inversion agrees with the Fermat inverse; the raw-candidate guard
-- detects a silent fallback.
#guard ((37 : ScalarField).invGcd * 37).toNat = 1
#guard ((SCALAR_FIELD_CARD - 1 : ScalarField).invGcd).toField
  = ((SCALAR_FIELD_CARD - 1 : Secp256k1.ScalarField)⁻¹)
#guard ((2 ^ 200 + 12345 : ScalarField).invGcd).toField
  = ((2 ^ 200 + 12345 : Secp256k1.ScalarField)⁻¹)
#guard (987654321 : ScalarField).invGcd.toField = ((987654321 : Secp256k1.ScalarField)⁻¹)
#guard (37 : ScalarField).invGcd.val
  = gcdInvCandidate SCALAR_FIELD_CARD (Mont64x8Field.modulusLimbs SCALAR_FIELD_CARD)
      (Mont64x8Field.montgomeryNegInv SCALAR_FIELD_CARD) (37 : ScalarField).val
#guard (2 ^ 255 + 12345 : ScalarField).invGcd.val
  = gcdInvCandidate SCALAR_FIELD_CARD (Mont64x8Field.modulusLimbs SCALAR_FIELD_CARD)
      (Mont64x8Field.montgomeryNegInv SCALAR_FIELD_CARD) (2 ^ 255 + 12345 : ScalarField).val

-- The Fermat fallback, exercised directly (the fast path never takes it).
#guard montPow (Mont64x8Field.modulusLimbs SCALAR_FIELD_CARD)
    (Mont64x8Field.montgomeryNegInv SCALAR_FIELD_CARD)
    (Mont64x8Field.rModModulus SCALAR_FIELD_CARD)
    (37 : ScalarField).val (SCALAR_FIELD_CARD - 2)
  = ((37 : ScalarField)⁻¹).val

/-! ## Base field -/

-- Stored Montgomery residues.
#guard (0 : BaseField).val = Limbs8.zero
#guard (1 : BaseField).val = Mont64x8Field.rModModulus BASE_FIELD_CARD

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
#guard ((BASE_FIELD_CARD - 2 : BaseField) * (BASE_FIELD_CARD - 3 : BaseField)).toField
  = ((BASE_FIELD_CARD - 2 : Secp256k1.BaseField) * (BASE_FIELD_CARD - 3))
#guard ((2 ^ 255 + 12345 : BaseField) * (2 ^ 255 + 67890 : BaseField)).toField
  = ((2 ^ 255 + 12345 : Secp256k1.BaseField) * (2 ^ 255 + 67890))

-- Exponentiation, including agreement with the canonical field.
#guard ((37 : BaseField) ^ 0).toNat = 1
#guard ((37 : BaseField) ^ 1).toNat = 37
#guard ((123456789 : BaseField) ^ 17).toField = ((123456789 : Secp256k1.BaseField) ^ 17)
#guard ((123456789 : BaseField) ^ 255).toField = ((123456789 : Secp256k1.BaseField) ^ 255)

-- Fermat inversion and division (`0⁻¹ = 0`, `x⁻¹ * x = 1`, `x / x = 1`).
#guard ((0 : BaseField)⁻¹).toNat = 0
#guard ((37 : BaseField)⁻¹ * 37).toNat = 1
#guard ((37 : BaseField) / 37).toNat = 1
#guard ((37 : BaseField)⁻¹).toField = ((37 : Secp256k1.BaseField)⁻¹)
#guard ((37 : BaseField) ^ (-3 : Int)).toField = ((37 : Secp256k1.BaseField) ^ (-3 : Int))

-- The checked binary-GCD inversion agrees with the Fermat inverse; the raw-candidate guard
-- detects a silent fallback.
#guard ((37 : BaseField).invGcd * 37).toNat = 1
#guard ((BASE_FIELD_CARD - 1 : BaseField).invGcd).toField
  = ((BASE_FIELD_CARD - 1 : Secp256k1.BaseField)⁻¹)
#guard ((2 ^ 200 + 12345 : BaseField).invGcd).toField
  = ((2 ^ 200 + 12345 : Secp256k1.BaseField)⁻¹)
#guard (987654321 : BaseField).invGcd.toField = ((987654321 : Secp256k1.BaseField)⁻¹)
#guard (37 : BaseField).invGcd.val
  = gcdInvCandidate BASE_FIELD_CARD (Mont64x8Field.modulusLimbs BASE_FIELD_CARD)
      (Mont64x8Field.montgomeryNegInv BASE_FIELD_CARD) (37 : BaseField).val
#guard (2 ^ 255 + 12345 : BaseField).invGcd.val
  = gcdInvCandidate BASE_FIELD_CARD (Mont64x8Field.modulusLimbs BASE_FIELD_CARD)
      (Mont64x8Field.montgomeryNegInv BASE_FIELD_CARD) (2 ^ 255 + 12345 : BaseField).val

-- The Fermat fallback, exercised directly (the fast path never takes it).
#guard montPow (Mont64x8Field.modulusLimbs BASE_FIELD_CARD)
    (Mont64x8Field.montgomeryNegInv BASE_FIELD_CARD)
    (Mont64x8Field.rModModulus BASE_FIELD_CARD)
    (37 : BaseField).val (BASE_FIELD_CARD - 2)
  = ((37 : BaseField)⁻¹).val

end Secp256k1.Fast
