/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Fast.Prelude
import CompPoly.Fields.Montgomery.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Fast BN254 Scalar Field — Montgomery Reduction and Multiplication

The native-word CIOS Montgomery reducer (`interleavedMontgomeryReduction`) and Montgomery
multiplication (`montgomeryMul`) for the BN254 scalar field, together with their `ZMod p`
correctness specs: one reduction step divides by `2⁶⁴`, and four interleaved rounds realise
`a · b · (2²⁵⁶)⁻¹ mod p`.
-/

-- The CIOS correctness proofs build deep `addc`/`mulSmall` carry chains.
set_option maxRecDepth 4000

namespace BN254
namespace Fast

open BN254 (scalarFieldSize)

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

/-- `r2ModModulus` is `R² = (2²⁵⁶)²` in `ZMod p`. Verified as a `Nat` congruence (kernel
`decide`), then cast — the value half of "multiply by `R²` enters Montgomery form". -/
theorem r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod scalarFieldSize)
      = ((2 ^ 256 : Nat) : ZMod scalarFieldSize) ^ 2 := by
  have h : r2ModModulus.toNat ≡ (2 ^ 256) ^ 2 [MOD scalarFieldSize] := by decide
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h, Nat.cast_pow]

/-- `rModModulus` is `R = 2²⁵⁶` in `ZMod p` (the Montgomery image of one). Verified as a `Nat`
congruence (kernel `decide`), then cast. -/
theorem rModModulus_cast :
    (rModModulus.toNat : ZMod scalarFieldSize) = ((2 ^ 256 : Nat) : ZMod scalarFieldSize) := by
  have h : rModModulus.toNat ≡ 2 ^ 256 [MOD scalarFieldSize] := by decide
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

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
  · rw [if_pos hx]
    rw [UInt256L.lt_iff_toNat_lt, modulus_toNat] at hx
    exact hx
  · rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt] at hx
    have hle : modulus.toNat ≤ x.toNat := by omega
    rw [UInt256L.toNat_sub_of_le hle, modulus_toNat]
    rw [modulus_toNat] at hx
    omega

/-- The conditional subtract preserves the value modulo the prime. -/
theorem reduceUInt256Lt2ModulusRaw_cast (x : UInt256L) :
    ((reduceUInt256Lt2ModulusRaw x).toNat : ZMod scalarFieldSize)
      = (x.toNat : ZMod scalarFieldSize) := by
  unfold reduceUInt256Lt2ModulusRaw
  by_cases hx : x < modulus
  · rw [if_pos hx]
  · rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt, modulus_toNat] at hx
    have hle : modulus.toNat ≤ x.toNat := by rw [modulus_toNat]; omega
    rw [UInt256L.toNat_sub_of_le hle, modulus_toNat,
        Nat.cast_sub (by rw [modulus_toNat] at hle; exact hle)]
    simp only [ZMod.natCast_self, sub_zero]


/-- `reduceUInt256Lt2ModulusRaw` packaged as a `ScalarField` (input `< 2·modulus`). -/
@[inline]
def reduceUInt256Lt2Modulus (x : UInt256L) (h : x.toNat < 2 * BN254.scalarFieldSize) :
    ScalarField :=
  ⟨reduceUInt256Lt2ModulusRaw x, reduceUInt256Lt2ModulusRaw_lt x h⟩


/-- One additive CIOS step: given the low limb `acc0` and high four limbs `acc` of a 5-limb
accumulator, returns `(acc0 + acc·2⁶⁴)·2⁻⁶⁴ mod p`. Assumes the accumulator is `< p·2⁶⁴`, so
a single conditional subtract reduces. -/
@[inline]
def interleavedMontgomeryReduction (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := montgomeryNegInv * acc0
  let prod := mulSmall modulus t
  let cin := (addc acc0 prod.1 0).2
  let s := UInt256L.addCarry acc prod.2 cin
  reduceUInt256Lt2ModulusRaw s

/-- One CIOS step is correct: given the 5-limb accumulator `(acc0, acc)` bounded by `p·2⁶⁴`,
`interleavedMontgomeryReduction` returns a canonical residue equal to
`(acc0 + acc·2⁶⁴)·(2⁶⁴)⁻¹ mod p`. -/
theorem interleavedMontgomeryReduction_spec (acc0 : UInt64) (acc : UInt256L)
    (hV : acc0.toNat + acc.toNat * 2 ^ 64 < scalarFieldSize * 2 ^ 64) :
    (interleavedMontgomeryReduction acc0 acc).toNat < scalarFieldSize ∧
    ((interleavedMontgomeryReduction acc0 acc).toNat : ZMod scalarFieldSize)
      = ((acc0.toNat + acc.toNat * 2 ^ 64 : Nat) : ZMod scalarFieldSize)
        * ((2 ^ 64 : Nat) : ZMod scalarFieldSize)⁻¹ := by
  have hcong : montgomeryNegInv.toNat * scalarFieldSize ≡ 2 ^ 64 - 1 [MOD 2 ^ 64] := by decide
  have hRne : ((2 ^ 64 : Nat) : ZMod scalarFieldSize) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by decide)
  have h2p : 2 * scalarFieldSize < 2 ^ 256 := two_mul_scalarFieldSize_lt_two256
  unfold interleavedMontgomeryReduction
  set t := montgomeryNegInv * acc0 with htdef
  set prod := mulSmall modulus t with hproddef
  set cin := (addc acc0 prod.1 0).2 with hcindef
  set s := UInt256L.addCarry acc prod.2 cin with hsdef
  have ht_lt : t.toNat < 2 ^ 64 := t.toNat_lt
  have ha0 : acc0.toNat < 2 ^ 64 := acc0.toNat_lt
  have hp1 : prod.1.toNat < 2 ^ 64 := prod.1.toNat_lt
  have hprodval : prod.1.toNat + prod.2.toNat * 2 ^ 64 = scalarFieldSize * t.toNat := by
    rw [hproddef, mulSmall_toNat, modulus_toNat]
  obtain ⟨haddc, hcin1, hD⟩ := addc_spec acc0 prod.1 0 (by decide)
  rw [← hcindef] at haddc hcin1
  rw [show (0 : UInt64).toNat = 0 from rfl] at haddc
  have hVmod : (acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 = acc0.toNat := by omega
  have htm : (acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 * montgomeryNegInv.toNat % 2 ^ 64
      = t.toNat := by
    rw [hVmod, htdef, UInt64.toNat_mul, Nat.mul_comm]
  have hdvd : 2 ^ 64 ∣ (acc0.toNat + acc.toNat * 2 ^ 64)
      + (prod.1.toNat + prod.2.toNat * 2 ^ 64) := by
    have h := Montgomery.sum_dvd (2 ^ 64) scalarFieldSize montgomeryNegInv.toNat (by decide) hcong
      (acc0.toNat + acc.toNat * 2 ^ 64)
    rw [htm] at h
    rwa [show t.toNat * scalarFieldSize = scalarFieldSize * t.toNat from by ring, ← hprodval] at h
  have hD0 : (addc acc0 prod.1 0).1.toNat = 0 := by omega
  have hu : acc.toNat + prod.2.toNat + cin.toNat
      = ((acc0.toNat + acc.toNat * 2 ^ 64) + (prod.1.toNat + prod.2.toNat * 2 ^ 64)) / 2 ^ 64 := by
    omega
  have hpb : prod.1.toNat + prod.2.toNat * 2 ^ 64 < scalarFieldSize * 2 ^ 64 := by
    rw [hprodval]; nlinarith [ht_lt, (by decide : (0 : Nat) < scalarFieldSize)]
  have hSlt : acc.toNat + prod.2.toNat + cin.toNat < 2 * scalarFieldSize := by
    rw [hu]; omega
  have hsval : s.toNat = acc.toNat + prod.2.toNat + cin.toNat := by
    rw [hsdef, UInt256L.toNat_addCarry acc prod.2 cin hcin1, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · exact reduceUInt256Lt2ModulusRaw_lt s (by rw [hsval]; exact hSlt)
  · rw [reduceUInt256Lt2ModulusRaw_cast, hsval, hu]
    rw [show (acc0.toNat + acc.toNat * 2 ^ 64) + (prod.1.toNat + prod.2.toNat * 2 ^ 64)
          = (acc0.toNat + acc.toNat * 2 ^ 64)
            + ((acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 * montgomeryNegInv.toNat % 2 ^ 64)
              * scalarFieldSize from by rw [htm, hprodval]; ring]
    exact Montgomery.quotient_cast (2 ^ 64) scalarFieldSize montgomeryNegInv.toNat (by decide)
      hcong hRne (acc0.toNat + acc.toNat * 2 ^ 64)


/-- Montgomery multiplication: `montgomeryMul a b = a · b · R⁻¹ mod p` (CIOS, 4 rounds).
Requires `lhs < modulus` (the fully-scanned operand); `rhs` is unrestricted. -/
@[inline]
def montgomeryMul (lhs rhs : UInt256L) : UInt256L :=
  let (a0, a) := mulSmall lhs rhs.l0
  let r0 := interleavedMontgomeryReduction a0 a
  let (b0, b) := mulSmallAndAcc lhs rhs.l1 r0
  let r1 := interleavedMontgomeryReduction b0 b
  let (c0, c) := mulSmallAndAcc lhs rhs.l2 r1
  let r2 := interleavedMontgomeryReduction c0 c
  let (d0, d) := mulSmallAndAcc lhs rhs.l3 r2
  interleavedMontgomeryReduction d0 d

private theorem montNegInv_dvd : ((2 ^ 64 : Nat) : ZMod scalarFieldSize) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt (by decide) (by decide)

/-- Round 0 of CIOS: `mulSmall` then one reduction step. -/
theorem montgomeryInit_spec (lhs : UInt256L) (d : UInt64) (hlhs : lhs.toNat < scalarFieldSize) :
    (interleavedMontgomeryReduction (mulSmall lhs d).1 (mulSmall lhs d).2).toNat < scalarFieldSize ∧
    ((interleavedMontgomeryReduction (mulSmall lhs d).1 (mulSmall lhs d).2).toNat :
        ZMod scalarFieldSize)
      = (lhs.toNat : ZMod scalarFieldSize) * (d.toNat : ZMod scalarFieldSize)
        * ((2 ^ 64 : Nat) : ZMod scalarFieldSize)⁻¹ := by
  have hv : (mulSmall lhs d).1.toNat + (mulSmall lhs d).2.toNat * 2 ^ 64 = lhs.toNat * d.toNat :=
    mulSmall_toNat lhs d
  have hrng : (mulSmall lhs d).1.toNat + (mulSmall lhs d).2.toNat * 2 ^ 64
      < scalarFieldSize * 2 ^ 64 := by
    rw [hv]; nlinarith [hlhs, d.toNat_lt]
  obtain ⟨hb, hc⟩ := interleavedMontgomeryReduction_spec (mulSmall lhs d).1 (mulSmall lhs d).2 hrng
  refine ⟨hb, ?_⟩
  rw [hc, hv]; push_cast; ring

/-- Rounds 1–3 of CIOS: `mulSmallAndAcc` then one reduction step. -/
theorem montgomeryStep_spec (lhs : UInt256L) (d : UInt64) (acc : UInt256L)
    (hlhs : lhs.toNat < scalarFieldSize) (hacc : acc.toNat < scalarFieldSize) :
    (interleavedMontgomeryReduction (mulSmallAndAcc lhs d acc).1
        (mulSmallAndAcc lhs d acc).2).toNat < scalarFieldSize ∧
    ((interleavedMontgomeryReduction (mulSmallAndAcc lhs d acc).1
        (mulSmallAndAcc lhs d acc).2).toNat :
        ZMod scalarFieldSize)
      = ((lhs.toNat : ZMod scalarFieldSize) * (d.toNat : ZMod scalarFieldSize)
          + (acc.toNat : ZMod scalarFieldSize)) * ((2 ^ 64 : Nat) : ZMod scalarFieldSize)⁻¹ := by
  have hv : (mulSmallAndAcc lhs d acc).1.toNat + (mulSmallAndAcc lhs d acc).2.toNat * 2 ^ 64
      = lhs.toNat * d.toNat + acc.toNat := mulSmallAndAcc_toNat lhs d acc
  have hrng : (mulSmallAndAcc lhs d acc).1.toNat + (mulSmallAndAcc lhs d acc).2.toNat * 2 ^ 64
      < scalarFieldSize * 2 ^ 64 := by
    rw [hv]; nlinarith [hlhs, hacc, d.toNat_lt]
  obtain ⟨hb, hc⟩ := interleavedMontgomeryReduction_spec (mulSmallAndAcc lhs d acc).1
    (mulSmallAndAcc lhs d acc).2 hrng
  refine ⟨hb, ?_⟩
  rw [hc, hv]; push_cast; ring

/-- The field-level reassembly of the four reduction rounds into `L · rhs · (R⁴)⁻¹`. -/
private theorem montgomeryMul_assemble (R L b0 b1 b2 b3 c0 c1 c2 res : ZMod scalarFieldSize)
    (hRne : R ≠ 0)
    (h0 : c0 = L * b0 * R⁻¹) (h1 : c1 = (L * b1 + c0) * R⁻¹)
    (h2 : c2 = (L * b2 + c1) * R⁻¹) (h3 : res = (L * b3 + c2) * R⁻¹) :
    res = L * (b0 + b1 * R + b2 * R ^ 2 + b3 * R ^ 3) * (R ^ 4)⁻¹ := by
  have e0 : c0 * R = L * b0 := by rw [h0, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have e1 : c1 * R = L * b1 + c0 := by rw [h1, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have e2 : c2 * R = L * b2 + c1 := by rw [h2, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have e3 : res * R = L * b3 + c2 := by rw [h3, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have hkey : res * R ^ 4 = L * (b0 + b1 * R + b2 * R ^ 2 + b3 * R ^ 3) := by
    linear_combination e0 + R * e1 + R ^ 2 * e2 + R ^ 3 * e3
  rw [← hkey, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 4 hRne), mul_one]

/-- Montgomery multiplication is correct: for `lhs < modulus` and arbitrary `rhs`, the result
is a canonical residue equal to `lhs · rhs · (2²⁵⁶)⁻¹ mod p`. -/
theorem montgomeryMul_spec (lhs rhs : UInt256L) (hlhs : lhs.toNat < scalarFieldSize) :
    (montgomeryMul lhs rhs).toNat < scalarFieldSize ∧
    ((montgomeryMul lhs rhs).toNat : ZMod scalarFieldSize)
      = (lhs.toNat : ZMod scalarFieldSize) * (rhs.toNat : ZMod scalarFieldSize)
        * ((2 ^ 256 : Nat) : ZMod scalarFieldSize)⁻¹ := by
  unfold montgomeryMul
  set r0 := interleavedMontgomeryReduction (mulSmall lhs rhs.l0).1 (mulSmall lhs rhs.l0).2 with hr0
  set r1 := interleavedMontgomeryReduction (mulSmallAndAcc lhs rhs.l1 r0).1
    (mulSmallAndAcc lhs rhs.l1 r0).2 with hr1
  set r2 := interleavedMontgomeryReduction (mulSmallAndAcc lhs rhs.l2 r1).1
    (mulSmallAndAcc lhs rhs.l2 r1).2 with hr2
  obtain ⟨hb0, hc0⟩ := montgomeryInit_spec lhs rhs.l0 hlhs
  rw [← hr0] at hb0 hc0
  obtain ⟨hb1, hc1⟩ := montgomeryStep_spec lhs rhs.l1 r0 hlhs hb0
  rw [← hr1] at hb1 hc1
  obtain ⟨hb2, hc2⟩ := montgomeryStep_spec lhs rhs.l2 r1 hlhs hb1
  rw [← hr2] at hb2 hc2
  obtain ⟨hb3, hc3⟩ := montgomeryStep_spec lhs rhs.l3 r2 hlhs hb2
  set rr := interleavedMontgomeryReduction (mulSmallAndAcc lhs rhs.l3 r2).1
    (mulSmallAndAcc lhs rhs.l3 r2).2 with hrr
  refine ⟨hb3, ?_⟩
  set R := ((2 ^ 64 : Nat) : ZMod scalarFieldSize) with hRdef
  have hrhs : (rhs.toNat : ZMod scalarFieldSize)
      = (rhs.l0.toNat : ZMod scalarFieldSize) + (rhs.l1.toNat : ZMod scalarFieldSize) * R
        + (rhs.l2.toNat : ZMod scalarFieldSize) * R ^ 2
        + (rhs.l3.toNat : ZMod scalarFieldSize) * R ^ 3 := by
    simp only [UInt256L.toNat, Nat.shiftLeft_eq]; push_cast [hRdef]; ring
  have h256 : ((2 ^ 256 : Nat) : ZMod scalarFieldSize) = R ^ 4 := by
    rw [hRdef]; push_cast; ring
  rw [h256, hrhs]
  exact montgomeryMul_assemble R (lhs.toNat : ZMod scalarFieldSize)
    (rhs.l0.toNat : ZMod scalarFieldSize)
    (rhs.l1.toNat : ZMod scalarFieldSize) (rhs.l2.toNat : ZMod scalarFieldSize)
    (rhs.l3.toNat : ZMod scalarFieldSize) (r0.toNat : ZMod scalarFieldSize)
    (r1.toNat : ZMod scalarFieldSize) (r2.toNat : ZMod scalarFieldSize)
    (rr.toNat : ZMod scalarFieldSize) montNegInv_dvd hc0 hc1 hc2 hc3

end Fast
end BN254
