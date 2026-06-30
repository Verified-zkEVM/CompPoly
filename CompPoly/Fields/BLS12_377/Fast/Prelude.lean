/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_377.Basic
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast BLS12-377 Scalar Field — `Mont256Field` instance

The per-field data realizing `BLS12_377.ScalarField` as a fast 256-bit Montgomery field: the
four word constants (verified byte-for-byte against arkworks `ark-bls12-377`) plus the
`decide`-checked numeric/`ZMod` facts the generic `Montgomery.Native256` stack consumes. The
fast carrier `ScalarField`, its operations, and the `Field` structure all come from the generic
stack — this module supplies only the instance.
-/

namespace BLS12_377
namespace Fast

open Montgomery.Native256

/-- The BLS12-377 scalar-field modulus as a 256-bit word. -/
def modulus : UInt256L :=
  { l0 := 0x0a11800000000001,
    l1 := 0x59aa76fed0000001,
    l2 := 0x60b44d1e5c37b001,
    l3 := 0x12ab655e9a2ca556 }

/-- `-modulus⁻¹ mod 2^64`, the per-limb multiplier for interleaved Montgomery reduction. -/
def montgomeryNegInv : UInt64 := 0x0a117fffffffffff

/-- `2^256 mod modulus`, the Montgomery representation of one. -/
def rModModulus : UInt256L :=
  { l0 := 0x7d1c7ffffffffff3,
    l1 := 0x7257f50f6ffffff2,
    l2 := 0x16d81575512c0fee,
    l3 := 0x0d4bda322bbb9a9d }

/-- `(2^256)^2 mod modulus`, used to enter Montgomery form. -/
def r2ModModulus : UInt256L :=
  { l0 := 0x25d577bab861857b,
    l1 := 0xcc2c27b58860591f,
    l2 := 0xa7cc008fe5dc8593,
    l3 := 0x011fdae7eff1c939 }

theorem modulus_toNat : modulus.toNat = BLS12_377.scalarFieldSize := by decide

theorem two_mul_scalarFieldSize_lt_two256 : 2 * BLS12_377.scalarFieldSize < 2 ^ 256 := by decide

theorem rModModulus_lt_scalarFieldSize : rModModulus.toNat < BLS12_377.scalarFieldSize := by decide

theorem rModModulus_cast :
    (rModModulus.toNat : ZMod BLS12_377.scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod BLS12_377.scalarFieldSize) := by
  have h : rModModulus.toNat ≡ 2 ^ 256 [MOD BLS12_377.scalarFieldSize] := by decide
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

theorem r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod BLS12_377.scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod BLS12_377.scalarFieldSize) ^ 2 := by
  have h : r2ModModulus.toNat ≡ (2 ^ 256) ^ 2 [MOD BLS12_377.scalarFieldSize] := by decide
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h, Nat.cast_pow]

theorem negInv_congr :
    montgomeryNegInv.toNat * BLS12_377.scalarFieldSize ≡ 2 ^ 64 - 1 [MOD 2 ^ 64] := by decide

theorem two_ne_zero_in_field : ((2 : Nat) : ZMod BLS12_377.scalarFieldSize) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd (by decide) hd) (by decide)

theorem p2HexDigits_reconstruct :
    ((List.range 64).map
        (fun i => ((BLS12_377.scalarFieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).tail.foldl
        (fun n d => n * 16 + d)
        (((List.range 64).map
          (fun i => ((BLS12_377.scalarFieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).headD 0)
      = BLS12_377.scalarFieldSize - 2 := by decide

/-- The per-field data realizing BLS12-377's scalar field as a fast 256-bit Montgomery field.
The four word constants are the only runtime data; everything else is a `decide`-checked fact. -/
instance instMont256Field : Mont256Field BLS12_377.ScalarField where
  fieldSize := BLS12_377.scalarFieldSize
  prime := inferInstance
  modulus := modulus
  montgomeryNegInv := montgomeryNegInv
  rModModulus := rModModulus
  r2ModModulus := r2ModModulus
  modulus_toNat := modulus_toNat
  two_mul_fieldSize_lt_two256 := two_mul_scalarFieldSize_lt_two256
  rModModulus_lt_fieldSize := rModModulus_lt_scalarFieldSize
  rModModulus_cast := rModModulus_cast
  r2ModModulus_cast := r2ModModulus_cast
  negInv_congr := negInv_congr
  two_ne_zero_in_field := two_ne_zero_in_field
  p2HexDigits_reconstruct := p2HexDigits_reconstruct

/-- The fast native-word BLS12-377 scalar field, stored as a Montgomery residue below the
prime. -/
abbrev ScalarField : Type := FastField BLS12_377.ScalarField

/-- The raw Montgomery word backing a fast BLS12-377 scalar-field element. -/
@[inline]
def raw (x : ScalarField) : UInt256L := x.val

end Fast
end BLS12_377
