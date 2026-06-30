/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Basic
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast BN254 Scalar Field — `Mont256Field` instance

The per-field data realizing `BN254.ScalarField` as a fast 256-bit Montgomery field: the four
word constants plus the `decide`-checked numeric/`ZMod` facts that the generic
`Montgomery.Native256` stack consumes. The fast carrier `ScalarField`, its operations, and the
`Field` structure all come from the generic stack — this module supplies only the instance.
-/

namespace BN254
namespace Fast

open Montgomery.Native256

/-- The BN254 scalar-field modulus as a 256-bit word. -/
def modulus : UInt256L :=
  { l0 := 0x43e1f593f0000001,
    l1 := 0x2833e84879b97091,
    l2 := 0xb85045b68181585d,
    l3 := 0x30644e72e131a029 }

/-- `-modulus⁻¹ mod 2^64`, the per-limb multiplier for interleaved Montgomery reduction. -/
def montgomeryNegInv : UInt64 := 0xc2e1f593efffffff

/-- `2^256 mod modulus`, the Montgomery representation of one. -/
def rModModulus : UInt256L :=
  { l0 := 0xac96341c4ffffffb,
    l1 := 0x36fc76959f60cd29,
    l2 := 0x666ea36f7879462e,
    l3 := 0x0e0a77c19a07df2f }

/-- `(2^256)^2 mod modulus`, used to enter Montgomery form. -/
def r2ModModulus : UInt256L :=
  { l0 := 0x1bb8e645ae216da7,
    l1 := 0x53fe3ab1e35c59e3,
    l2 := 0x8c49833d53bb8085,
    l3 := 0x0216d0b17f4e44a5 }

theorem modulus_toNat : modulus.toNat = BN254.scalarFieldSize := by decide

theorem two_mul_scalarFieldSize_lt_two256 : 2 * BN254.scalarFieldSize < 2 ^ 256 := by decide

theorem rModModulus_lt_scalarFieldSize : rModModulus.toNat < BN254.scalarFieldSize := by decide

theorem rModModulus_cast :
    (rModModulus.toNat : ZMod BN254.scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod BN254.scalarFieldSize) := by
  have h : rModModulus.toNat ≡ 2 ^ 256 [MOD BN254.scalarFieldSize] := by decide
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

theorem r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod BN254.scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod BN254.scalarFieldSize) ^ 2 := by
  have h : r2ModModulus.toNat ≡ (2 ^ 256) ^ 2 [MOD BN254.scalarFieldSize] := by decide
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h, Nat.cast_pow]

theorem negInv_congr :
    montgomeryNegInv.toNat * BN254.scalarFieldSize ≡ 2 ^ 64 - 1 [MOD 2 ^ 64] := by decide

theorem two_ne_zero_in_field : ((2 : Nat) : ZMod BN254.scalarFieldSize) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd (by decide) hd) (by decide)

theorem p2HexDigits_reconstruct :
    ((List.range 64).map
        (fun i => ((BN254.scalarFieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).tail.foldl
        (fun n d => n * 16 + d)
        (((List.range 64).map
          (fun i => ((BN254.scalarFieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).headD 0)
      = BN254.scalarFieldSize - 2 := by decide

/-- The per-field data realizing BN254's scalar field as a fast 256-bit Montgomery field. The
four word constants are the only runtime data; everything else is a `decide`-checked fact. -/
instance instMont256Field : Mont256Field BN254.ScalarField where
  fieldSize := BN254.scalarFieldSize
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

/-- The fast native-word BN254 scalar field, stored as a Montgomery residue below the prime. -/
abbrev ScalarField : Type := FastField BN254.ScalarField

/-- The raw Montgomery word backing a fast BN254 scalar-field element. -/
@[inline]
def raw (x : ScalarField) : UInt256L := x.val

end Fast
end BN254
