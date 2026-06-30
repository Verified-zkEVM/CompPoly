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

/-! ## Entering Montgomery form (`ofField`) and the round trips -/

/-- Build a fast element from a canonical natural representative `n < p`: materialise `n` as a
256-bit word and `montgomeryMul` it by `R²`, landing on the Montgomery residue `n · R`. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < scalarFieldSize) : ScalarField :=
  ⟨montgomeryMul (UInt256L.ofNat n) r2ModModulus, by
    have hlt : (UInt256L.ofNat n).toNat < scalarFieldSize := by
      rw [UInt256L.toNat_ofNat n (by have := two_mul_scalarFieldSize_lt_two256; omega)]
      exact h
    have hb := (montgomeryMul_spec (UInt256L.ofNat n) r2ModModulus hlt).1
    rwa [modulus_toNat]⟩

/-- The stored word of `ofCanonicalNat n` is the Montgomery residue `n · 2²⁵⁶` in `ZMod p`:
`montgomeryMul` contributes `R⁻¹`, `r2ModModulus` contributes `R²`, leaving one factor of `R`. -/
theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < scalarFieldSize) :
    ((ofCanonicalNat n h).val.toNat : BN254.ScalarField)
      = (n : BN254.ScalarField) * ((2 ^ 256 : Nat) : BN254.ScalarField) := by
  have hn : n < 2 ^ 256 := by have := two_mul_scalarFieldSize_lt_two256; omega
  have hlt : (UInt256L.ofNat n).toNat < scalarFieldSize := by
    rw [UInt256L.toNat_ofNat n hn]; exact h
  have hspec := (montgomeryMul_spec (UInt256L.ofNat n) r2ModModulus hlt).2
  change ((montgomeryMul (UInt256L.ofNat n) r2ModModulus).toNat : BN254.ScalarField) = _
  rw [hspec, UInt256L.toNat_ofNat n hn, r2ModModulus_cast, mul_assoc, pow_two,
    mul_assoc ((2 ^ 256 : Nat) : BN254.ScalarField), mul_inv_cancel₀ r256_ne_zero, mul_one]

/-- `toField` recovers the canonical representative fed to `ofCanonicalNat`. -/
@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < scalarFieldSize) :
    toField (ofCanonicalNat n h) = (n : BN254.ScalarField) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast, mul_assoc,
    mul_inv_cancel₀ r256_ne_zero, mul_one]

/-- Convert from the canonical `ZMod p` field into fast Montgomery form. -/
@[inline]
def ofField (x : BN254.ScalarField) : ScalarField := ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert a natural number into fast Montgomery form (reducing modulo `p` first). -/
@[inline]
def ofNat (n : Nat) : ScalarField :=
  ofCanonicalNat (n % scalarFieldSize) (Nat.mod_lt _ BN254.ScalarField_is_prime.pos)

/-- Convert an integer into fast Montgomery form. -/
@[inline]
def ofInt (n : Int) : ScalarField := ofField (n : BN254.ScalarField)

/-- Canonical field → fast form → canonical field is the identity. -/
@[simp]
theorem toField_ofField (x : BN254.ScalarField) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Fast form → canonical field → fast form is the identity. -/
@[simp]
theorem ofField_toField (x : ScalarField) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt256L.toNat_inj.mp
  apply nat_eq_of_field_eq (property_lt (ofField (toField x))) (property_lt x)
  rw [raw_cast_eq_toField_mul, toField_ofField, raw_cast_eq_toField_mul]

/-- `toField` is injective: distinct fast elements denote distinct elements of the canonical
field. Derived from the `ofField`/`toField` round trip; this is the gateway lemma for
transporting the `ZMod p` `Field` structure onto the fast representation via
`Function.Injective.field` (operation-preservation lemmas supply the rest). -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

end Fast
end BN254
