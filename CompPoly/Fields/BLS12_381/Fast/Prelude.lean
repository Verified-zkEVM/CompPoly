/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BLS12_381.Basic
import CompPoly.Fields.Montgomery.Native256Field

/-!
# Fast BLS12-381 Scalar Field — `Mont256Field` instance

The per-field data realizing `BLS12_381.ScalarField` as a fast 256-bit Montgomery field: the
four word constants (verified byte-for-byte against arkworks `ark-bls12-381`) plus the
`decide`-checked numeric/`ZMod` facts the generic `Montgomery.Native256` stack consumes. The
fast carrier `ScalarField`, its operations, and the `Field` structure all come from the generic
stack — this module supplies only the instance.
-/

namespace BLS12_381
namespace Fast

open Montgomery.Native256

/-- The BLS12-381 scalar-field modulus as a 256-bit word. -/
def modulus : UInt256L :=
  { l0 := 0xffffffff00000001,
    l1 := 0x53bda402fffe5bfe,
    l2 := 0x3339d80809a1d805,
    l3 := 0x73eda753299d7d48 }

/-- `-modulus⁻¹ mod 2^64`, the per-limb multiplier for interleaved Montgomery reduction. -/
def montgomeryNegInv : UInt64 := 0xfffffffeffffffff

/-- `2^256 mod modulus`, the Montgomery representation of one. -/
def rModModulus : UInt256L :=
  { l0 := 0x00000001fffffffe,
    l1 := 0x5884b7fa00034802,
    l2 := 0x998c4fefecbc4ff5,
    l3 := 0x1824b159acc5056f }

/-- `(2^256)^2 mod modulus`, used to enter Montgomery form. -/
def r2ModModulus : UInt256L :=
  { l0 := 0xc999e990f3f29c6d,
    l1 := 0x2b6cedcb87925c23,
    l2 := 0x05d314967254398f,
    l3 := 0x0748d9d99f59ff11 }

theorem modulus_toNat : modulus.toNat = BLS12_381.scalarFieldSize := by decide

theorem rModModulus_lt_scalarFieldSize : rModModulus.toNat < BLS12_381.scalarFieldSize := by decide

theorem rModModulus_cast :
    (rModModulus.toNat : ZMod BLS12_381.scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod BLS12_381.scalarFieldSize) := by
  have h : rModModulus.toNat ≡ 2 ^ 256 [MOD BLS12_381.scalarFieldSize] := by decide
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

theorem r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod BLS12_381.scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod BLS12_381.scalarFieldSize) ^ 2 := by
  have h : r2ModModulus.toNat ≡ (2 ^ 256) ^ 2 [MOD BLS12_381.scalarFieldSize] := by decide
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h, Nat.cast_pow]

theorem negInv_congr :
    montgomeryNegInv.toNat * BLS12_381.scalarFieldSize ≡ 2 ^ 64 - 1 [MOD 2 ^ 64] := by decide

theorem two_ne_zero_in_field : ((2 : Nat) : ZMod BLS12_381.scalarFieldSize) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd (by decide) hd) (by decide)

theorem p2HexDigits_reconstruct :
    ((List.range 64).map
        (fun i => ((BLS12_381.scalarFieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).tail.foldl
        (fun n d => n * 16 + d)
        (((List.range 64).map
          (fun i => ((BLS12_381.scalarFieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).headD 0)
      = BLS12_381.scalarFieldSize - 2 := by decide

/-- The per-field data realizing BLS12-381's scalar field as a fast 256-bit Montgomery field.
The four word constants are the only runtime data; everything else is a `decide`-checked fact. -/
instance instMont256Field : Mont256Field BLS12_381.ScalarField where
  fieldSize := BLS12_381.scalarFieldSize
  prime := inferInstance
  modulus := modulus
  montgomeryNegInv := montgomeryNegInv
  rModModulus := rModModulus
  r2ModModulus := r2ModModulus
  modulus_toNat := modulus_toNat
  rModModulus_lt_fieldSize := rModModulus_lt_scalarFieldSize
  rModModulus_cast := rModModulus_cast
  r2ModModulus_cast := r2ModModulus_cast
  negInv_congr := negInv_congr
  two_ne_zero_in_field := two_ne_zero_in_field
  p2HexDigits_reconstruct := p2HexDigits_reconstruct

/-- The fast native-word BLS12-381 scalar field, stored as a Montgomery residue below the
prime. -/
abbrev ScalarField : Type := FastField BLS12_381.ScalarField

/-- The raw Montgomery word backing a fast BLS12-381 scalar-field element. -/
@[inline]
def raw (x : ScalarField) : UInt256L := x.val

end Fast
end BLS12_381
