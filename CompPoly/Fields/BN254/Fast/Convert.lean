/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Fast.Montgomery

/-!
# Fast BN254 Scalar Field — Conversions

The bridge between the fast Montgomery representation (`ScalarField`, a `UInt256L` storing
`x · 2²⁵⁶ mod p`) and the canonical `BN254.ScalarField := ZMod p` view. `toField` exits
Montgomery form by one `montgomeryMul` against the raw integer `1`; `toField_eq_raw_mul_inv`
identifies it with multiplication by `(2²⁵⁶)⁻¹`.
-/

set_option maxRecDepth 4000

namespace BN254
namespace Fast

open BN254 (scalarFieldSize)

/-- The carrier's defining bound, restated against `scalarFieldSize` (= `modulus.toNat`). -/
theorem property_lt (x : ScalarField) : x.val.toNat < scalarFieldSize :=
  modulus_toNat ▸ x.property

/-- The raw 256-bit word for the integer `1` (NOT the Montgomery one `R`). -/
def oneRaw : UInt256L := ⟨1, 0, 0, 0⟩

@[simp] theorem oneRaw_toNat : oneRaw.toNat = 1 := by decide

/-- Exit Montgomery form: the canonical native-word representative of `x`. -/
@[inline]
def toCanonicalUInt256L (x : ScalarField) : UInt256L := montgomeryMul x.val oneRaw

/-- The canonical natural representative of a fast element. -/
@[inline]
def toNat (x : ScalarField) : Nat := (toCanonicalUInt256L x).toNat

/-- Interpret a fast element in the canonical `ZMod p` field. -/
@[inline]
def toField (x : ScalarField) : BN254.ScalarField := (toNat x : BN254.ScalarField)

theorem toNat_lt_scalarFieldSize (x : ScalarField) : toNat x < scalarFieldSize :=
  (montgomeryMul_spec x.val oneRaw (property_lt x)).1

/-- `toField` is the Montgomery interpretation: the stored word times `(2²⁵⁶)⁻¹`. -/
theorem toField_eq_raw_mul_inv (x : ScalarField) :
    toField x = (x.val.toNat : BN254.ScalarField) * ((2 ^ 256 : Nat) : BN254.ScalarField)⁻¹ := by
  have h := (montgomeryMul_spec x.val oneRaw (property_lt x)).2
  unfold toField toNat toCanonicalUInt256L
  rw [h, oneRaw_toNat]
  simp only [Nat.cast_one, mul_one]

/-- `R = 2²⁵⁶` is a unit in `ZMod p` (since `p` is an odd prime it cannot divide `2²⁵⁶`). -/
theorem r256_ne_zero : ((2 ^ 256 : Nat) : BN254.ScalarField) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have h2 : scalarFieldSize ∣ 2 := BN254.ScalarField_is_prime.dvd_of_dvd_pow hd
  exact absurd (Nat.le_of_dvd (by decide) h2) (by decide)

/-- The stored word equals `toField x · 2²⁵⁶` in `ZMod p`. -/
theorem raw_cast_eq_toField_mul (x : ScalarField) :
    (x.val.toNat : BN254.ScalarField) = toField x * ((2 ^ 256 : Nat) : BN254.ScalarField) := by
  rw [toField_eq_raw_mul_inv, mul_assoc, inv_mul_cancel₀ r256_ne_zero, mul_one]

/-- Two naturals below `p` with equal `ZMod p` casts are equal. -/
theorem nat_eq_of_field_eq {a b : Nat} (ha : a < scalarFieldSize) (hb : b < scalarFieldSize)
    (h : (a : BN254.ScalarField) = (b : BN254.ScalarField)) : a = b :=
  Montgomery.natCast_inj ha hb h

end Fast
end BN254
