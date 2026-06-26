/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Fast.Prelude


namespace BN254
namespace Fast

@[inline]
def reduceUInt256Lt2ModulusRaw (x : UInt256L) : UInt256L :=
  if x < modulus then x else x - modulus

theorem reduceUInt256Lt2ModulusRaw_lt (x : UInt256L)
  (h : x.toNat < 2 * BN254.scalarFieldSize) :
  (reduceUInt256Lt2ModulusRaw x).toNat < BN254.scalarFieldSize := by
  unfold reduceUInt256Lt2ModulusRaw
  by_cases hx : x < modulus
  . rw [if_pos hx]
    rw [UInt256L.lt_iff_toNat_lt, modulus_toNat] at hx
    exact hx
  . rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt] at hx
    have hle : modulus.toNat ≤ x.toNat := by omega
    rw [UInt256L.toNat_sub_of_le hle, modulus_toNat]
    rw [modulus_toNat] at hx
    omega


/-- Reduce a native word known to be below twice the BabyBear prime. -/
@[inline]
def reduceUInt256Lt2Modulus (x : UInt256L) (h : x.toNat < 2 * BN254.scalarFieldSize) :
    ScalarField :=
  ⟨reduceUInt256Lt2ModulusRaw x, reduceUInt256Lt2ModulusRaw_lt x h⟩



end Fast
end BN254
