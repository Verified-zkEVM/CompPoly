/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public meta import CompPoly.Fields.Secp256k1.Fast

/-!
# Fast secp256k1 Field Tests

Regression checks for the four-limb Montgomery scalar and base fields, whose moduli have
bit 255 set: residues, literal round trips, field operations including the carry paths,
the checked binary-GCD inversion, and agreement with the canonical `ZMod` models.
-/

public meta section

namespace Secp256k1.Fast

open Secp256k1 (scalarFieldSize baseFieldSize)
open Montgomery.Native64x4

set_option maxRecDepth 4000

/-! ## Scalar field -/

-- Stored Montgomery residues.
#guard (0 : ScalarField).val = Limbs4.zero
#guard (1 : ScalarField).val = Mont64x4Field.rModModulus scalarFieldSize

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
#guard ((scalarFieldSize - 1 : ScalarField) * (scalarFieldSize - 1 : ScalarField)).toNat
  = 1
#guard ((12345 : ScalarField) * 12345).toNat = 152399025
#guard ((scalarFieldSize - 2 : ScalarField) * (scalarFieldSize - 3 : ScalarField)).toField
  = ((scalarFieldSize - 2 : Secp256k1.ScalarField) * (scalarFieldSize - 3))
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
#guard ((scalarFieldSize - 1 : ScalarField).invGcd).toField
  = ((scalarFieldSize - 1 : Secp256k1.ScalarField)⁻¹)
#guard ((2 ^ 200 + 12345 : ScalarField).invGcd).toField
  = ((2 ^ 200 + 12345 : Secp256k1.ScalarField)⁻¹)
#guard (987654321 : ScalarField).invGcd.toField = ((987654321 : Secp256k1.ScalarField)⁻¹)
#guard (37 : ScalarField).invGcd.val
  = gcdInvCandidate scalarFieldSize (Mont64x4Field.modulusLimbs scalarFieldSize)
      (Mont64x4Field.montgomeryNegInv scalarFieldSize) (37 : ScalarField).val
#guard (2 ^ 255 + 12345 : ScalarField).invGcd.val
  = gcdInvCandidate scalarFieldSize (Mont64x4Field.modulusLimbs scalarFieldSize)
      (Mont64x4Field.montgomeryNegInv scalarFieldSize) (2 ^ 255 + 12345 : ScalarField).val

-- The Fermat fallback, exercised directly (the fast path never takes it).
#guard montPow (Mont64x4Field.modulusLimbs scalarFieldSize)
    (Mont64x4Field.montgomeryNegInv scalarFieldSize)
    (Mont64x4Field.rModModulus scalarFieldSize)
    (37 : ScalarField).val (scalarFieldSize - 2)
  = ((37 : ScalarField)⁻¹).val

/-! ## Base field -/

-- Stored Montgomery residues.
#guard (0 : BaseField).val = Limbs4.zero
#guard (1 : BaseField).val = Mont64x4Field.rModModulus baseFieldSize

-- Numeric literals reduce modulo the prime; `toNat` exits Montgomery form.
#guard (37 : BaseField).toNat = 37
#guard (baseFieldSize : BaseField).toNat = 0
#guard (baseFieldSize + 37 : BaseField).toNat = 37

-- Addition (with and without wraparound).
#guard ((baseFieldSize - 1 : BaseField) + 2).toNat = 1
#guard ((baseFieldSize - 1 : BaseField) + (baseFieldSize - 1 : BaseField)).toNat
  = baseFieldSize - 2

-- Subtraction (with and without borrow).
#guard ((9 : BaseField) - 5).toNat = 4
#guard ((5 : BaseField) - 9).toNat = baseFieldSize - 4

-- Negation.
#guard (-(0 : BaseField)).toNat = 0
#guard (-(1 : BaseField)).toNat = baseFieldSize - 1

-- Multiplication and squaring (`(-1) * (-1) = 1`).
#guard ((baseFieldSize - 1 : BaseField) * (baseFieldSize - 1 : BaseField)).toNat = 1
#guard ((12345 : BaseField) * 12345).toNat = 152399025
#guard ((baseFieldSize - 2 : BaseField) * (baseFieldSize - 3 : BaseField)).toField
  = ((baseFieldSize - 2 : Secp256k1.BaseField) * (baseFieldSize - 3))
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
#guard ((baseFieldSize - 1 : BaseField).invGcd).toField
  = ((baseFieldSize - 1 : Secp256k1.BaseField)⁻¹)
#guard ((2 ^ 200 + 12345 : BaseField).invGcd).toField
  = ((2 ^ 200 + 12345 : Secp256k1.BaseField)⁻¹)
#guard (987654321 : BaseField).invGcd.toField = ((987654321 : Secp256k1.BaseField)⁻¹)
#guard (37 : BaseField).invGcd.val
  = gcdInvCandidate baseFieldSize (Mont64x4Field.modulusLimbs baseFieldSize)
      (Mont64x4Field.montgomeryNegInv baseFieldSize) (37 : BaseField).val
#guard (2 ^ 255 + 12345 : BaseField).invGcd.val
  = gcdInvCandidate baseFieldSize (Mont64x4Field.modulusLimbs baseFieldSize)
      (Mont64x4Field.montgomeryNegInv baseFieldSize) (2 ^ 255 + 12345 : BaseField).val

-- The Fermat fallback, exercised directly (the fast path never takes it).
#guard montPow (Mont64x4Field.modulusLimbs baseFieldSize)
    (Mont64x4Field.montgomeryNegInv baseFieldSize)
    (Mont64x4Field.rModModulus baseFieldSize)
    (37 : BaseField).val (baseFieldSize - 2)
  = ((37 : BaseField)⁻¹).val

end Secp256k1.Fast
