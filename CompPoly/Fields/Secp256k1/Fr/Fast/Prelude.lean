/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Secp256k1
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast secp256k1 Scalar Field (`Fr`) — `Mont256Field` instance

The per-field data realizing `Secp256k1.ScalarField` (the secp256k1 group order
`SCALAR_FIELD_CARD`) as a fast 256-bit Montgomery field: the four word constants (matching
arkworks `ark-secp256k1`) plus the `decide`-checked numeric/`ZMod` facts that the generic
`Montgomery.Native256` stack consumes. The fast carrier `ScalarField`, its operations, and the
`Field` structure all come from the generic stack — this module supplies only the instance.

Note: this modulus has its top bit set (`2·p > 2²⁵⁶`), so it relies on the full-width reduction
path of `Montgomery.Native256` rather than the `2·p < 2²⁵⁶` shortcut used by BN254/BLS.
-/

namespace Secp256k1.Fr
namespace Fast

open Montgomery.Native256

/-- The secp256k1 scalar-field modulus as a 256-bit word. -/
def modulus : UInt256L :=
  { l0 := 0xbfd25e8cd0364141,
    l1 := 0xbaaedce6af48a03b,
    l2 := 0xfffffffffffffffe,
    l3 := 0xffffffffffffffff }

/-- `-modulus⁻¹ mod 2^64`, the per-limb multiplier for interleaved Montgomery reduction. -/
def montgomeryNegInv : UInt64 := 0x4b0dff665588b13f

/-- `2^256 mod modulus`, the Montgomery representation of one. -/
def rModModulus : UInt256L :=
  { l0 := 0x402da1732fc9bebf,
    l1 := 0x4551231950b75fc4,
    l2 := 0x0000000000000001,
    l3 := 0x0000000000000000 }

/-- `(2^256)^2 mod modulus`, used to enter Montgomery form. -/
def r2ModModulus : UInt256L :=
  { l0 := 0x896cf21467d7d140,
    l1 := 0x741496c20e7cf878,
    l2 := 0xe697f5e45bcd07c6,
    l3 := 0x9d671cd581c69bc5 }

theorem modulus_toNat : modulus.toNat = Secp256k1.SCALAR_FIELD_CARD := by decide

theorem rModModulus_lt_scalarFieldCard :
    rModModulus.toNat < Secp256k1.SCALAR_FIELD_CARD := by decide

theorem rModModulus_cast :
    (rModModulus.toNat : ZMod Secp256k1.SCALAR_FIELD_CARD)
      = ((2 ^ 256 : Nat) : ZMod Secp256k1.SCALAR_FIELD_CARD) := by
  have h : rModModulus.toNat ≡ 2 ^ 256 [MOD Secp256k1.SCALAR_FIELD_CARD] := by decide
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

theorem r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod Secp256k1.SCALAR_FIELD_CARD)
      = ((2 ^ 256 : Nat) : ZMod Secp256k1.SCALAR_FIELD_CARD) ^ 2 := by
  have h : r2ModModulus.toNat ≡ (2 ^ 256) ^ 2 [MOD Secp256k1.SCALAR_FIELD_CARD] := by decide
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h, Nat.cast_pow]

theorem negInv_congr :
    montgomeryNegInv.toNat * Secp256k1.SCALAR_FIELD_CARD ≡ 2 ^ 64 - 1 [MOD 2 ^ 64] := by decide

theorem two_ne_zero_in_field : ((2 : Nat) : ZMod Secp256k1.SCALAR_FIELD_CARD) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd (by decide) hd) (by decide)

theorem p2HexDigits_reconstruct :
    ((List.range 64).map
        (fun i => ((Secp256k1.SCALAR_FIELD_CARD - 2) >>> ((63 - i) * 4)) &&& 0xF)).tail.foldl
        (fun n d => n * 16 + d)
        (((List.range 64).map
          (fun i => ((Secp256k1.SCALAR_FIELD_CARD - 2) >>> ((63 - i) * 4)) &&& 0xF)).headD 0)
      = Secp256k1.SCALAR_FIELD_CARD - 2 := by decide

/-- The per-field data realizing secp256k1's scalar field as a fast 256-bit Montgomery field.
The four word constants are the only runtime data; everything else is a `decide`-checked fact. -/
instance instMont256Field : Mont256Field Secp256k1.ScalarField where
  fieldSize := Secp256k1.SCALAR_FIELD_CARD
  prime := inferInstance
  modulus := modulus
  montgomeryNegInv := montgomeryNegInv
  rModModulus := rModModulus
  r2ModModulus := r2ModModulus
  modulus_toNat := modulus_toNat
  rModModulus_lt_fieldSize := rModModulus_lt_scalarFieldCard
  rModModulus_cast := rModModulus_cast
  r2ModModulus_cast := r2ModModulus_cast
  negInv_congr := negInv_congr
  two_ne_zero_in_field := two_ne_zero_in_field
  p2HexDigits_reconstruct := p2HexDigits_reconstruct

/-- The fast native-word secp256k1 scalar field, stored as a Montgomery residue below the
prime. -/
abbrev ScalarField : Type := FastField Secp256k1.ScalarField

/-- The raw Montgomery word backing a fast secp256k1 scalar-field element. -/
@[inline]
def raw (x : ScalarField) : UInt256L := x.val

end Fast
end Secp256k1.Fr
