/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import Mathlib.Algebra.Field.TransferInstance
import CompPoly.Fields.BN254.Fast.Convert



namespace BN254
namespace Fast

@[inline]
def add (x y : ScalarField) : ScalarField :=
  reduceUInt256Lt2Modulus (x.val + y.val) (by
    rw [UInt256L.toNat_add]
    have hx := x.property
    have hy := y.property
    have hm := modulus_toNat
    omega)

/-- Fast zero in Montgomery form (the zero residue). -/
def zero : ScalarField := ⟨0, by decide⟩

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : ScalarField) : ScalarField :=
  if hx : x.val = 0 then
    zero
  else
    ⟨modulus - x.val, by
      have hle : x.val.toNat ≤ modulus.toNat := Nat.le_of_lt x.property
      rw [UInt256L.toNat_sub_of_le hle]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt256L.toNat_inj.mp
        simpa using hzero
      omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : ScalarField) : ScalarField :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt256L.le_iff_toNat_le] at hyx
      rw [UInt256L.toNat_sub_of_le hyx]
      have hx := x.property
      omega⟩
  else
    ⟨x.val + modulus - y.val, by
      have hb := x.property
      have hyb := y.property
      have hm := modulus_toNat
      have h2 := two_mul_scalarFieldSize_lt_two256
      rw [UInt256L.le_iff_toNat_le] at hyx
      have hbound : x.val.toNat + modulus.toNat < 2 ^ 256 := by omega
      have hsum_eq : (x.val + modulus).toNat = x.val.toNat + modulus.toNat := by
        rw [UInt256L.toNat_add, Nat.mod_eq_of_lt hbound]
      have hyle : y.val.toNat ≤ (x.val + modulus).toNat := by rw [hsum_eq]; omega
      rw [UInt256L.toNat_sub_of_le hyle, hsum_eq]
      omega⟩





end Fast
end BN254
