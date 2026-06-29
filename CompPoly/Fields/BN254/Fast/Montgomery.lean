/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Fast.Prelude


namespace BN254
namespace Fast

/-- `2^256 mod modulus`. This is the Montgomery representation of one (`R mod p`). -/
def rModModulus : UInt256L :=
  { l0 := 0xac96341c4ffffffb,
    l1 := 0x36fc76959f60cd29,
    l2 := 0x666ea36f7879462e,
    l3 := 0x0e0a77c19a07df2f }

/-- `(2^256)^2 mod modulus` (`R^2 mod p`), used to enter Montgomery representation. -/
def r2ModModulus : UInt256L :=
  { l0 := 0x1bb8e645ae216da7,
    l1 := 0x53fe3ab1e35c59e3,
    l2 := 0x8c49833d53bb8085,
    l3 := 0x0216d0b17f4e44a5 }

/-- `-modulus⁻¹ mod 2^64`, the per-limb multiplier for **additive** interleaved
Montgomery reduction. -/
def montgomeryNegInv : UInt64 := 0xc2e1f593efffffff

/-- Reduce a word known to be `< 2·modulus` to canonical range by one conditional subtract. -/
@[inline]
def reduceUInt256Lt2ModulusRaw (x : UInt256L) : UInt256L :=
  if x < modulus then x else x - modulus

/-- The conditional subtract lands in `[0, modulus)` when the input is `< 2·modulus`. -/
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


/-- `reduceUInt256Lt2ModulusRaw` packaged as a `ScalarField` (input `< 2·modulus`). -/
@[inline]
def reduceUInt256Lt2Modulus (x : UInt256L) (h : x.toNat < 2 * BN254.scalarFieldSize) :
    ScalarField :=
  ⟨reduceUInt256Lt2ModulusRaw x, reduceUInt256Lt2ModulusRaw_lt x h⟩


/-- One additive CIOS step: given the low limb `acc0` and high four limbs `acc` of a 5-limb
accumulator, returns `(acc0 + acc·2⁶⁴)·2⁻⁶⁴ mod p`. Assumes the accumulator is `< p·2⁶⁴`, so
a single conditional subtract reduces. -/
@[inline] def interleavedMontyReduction (acc0: UInt64) (acc : UInt256L) : UInt256L :=
  let t := montgomeryNegInv * acc0
  let prod := mulSmall modulus t
  let cin := (addc acc0 prod.1 0).2
  let s := UInt256L.addCarry acc prod.2 cin
  reduceUInt256Lt2ModulusRaw s


/-- Montgomery multiplication: `montyMul a b = a · b · R⁻¹ mod p` (CIOS, 4 rounds).
Requires `lhs < modulus` (the fully-scanned operand); `rhs` is unrestricted. -/
@[inline] def montyMul (lhs rhs : UInt256L) : UInt256L :=
  let (a0, a) := mulSmall lhs rhs.l0
  let r0 := interleavedMontyReduction a0 a
  let (b0, b) := mulSmallAndAcc lhs rhs.l1 r0
  let r1 := interleavedMontyReduction b0 b
  let (c0, c) := mulSmallAndAcc lhs rhs.l2 r1
  let r2 := interleavedMontyReduction c0 c
  let (d0, d) := mulSmallAndAcc lhs rhs.l3 r2
  interleavedMontyReduction d0 d



end Fast
end BN254
