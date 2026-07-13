/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Basic

/-!
# Native 32-bit Montgomery Reduction

Native `UInt32` Montgomery reduction with radix `2 ^ 32`, connected to the generic
natural-number specification in `Montgomery.Basic`.
-/

namespace Montgomery
namespace Native32

/-- The native pre-subtraction quotient in 32-bit Montgomery reduction. -/
@[inline]
def reduceQuotient (negInv : UInt32) (p x : UInt64) : UInt32 :=
  ((x + (x.toUInt32 * negInv).toUInt64 * p) >>> 32).toUInt32

/-- The native quotient agrees with the `Nat`-level Montgomery quotient. -/
theorem reduceQuotient_toNat (negInv : UInt32) (p : UInt64)
    (hp_pos : 0 < p.toNat) (hbound : p.toNat < 2 ^ 31)
    (x : UInt64) (h : x.toNat < p.toNat * 2 ^ 32) :
    (reduceQuotient negInv p x).toNat =
      reduceNatQuotient (2 ^ 32) p.toNat negInv.toNat x.toNat := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt64.toNat_ofNat,
    reduceQuotient, reduceNatQuotient, Nat.shiftRight_eq_div_pow]
  let mNat := x.toNat * negInv.toNat % 2 ^ 32
  have hm_lt : mNat < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hsum_lt : x.toNat + mNat * p.toNat < 2 ^ 64 := by
    have hprod_lt : mNat * p.toNat < p.toNat * 2 ^ 32 := by
      have := Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
      simpa [Nat.mul_comm] using this
    calc
      x.toNat + mNat * p.toNat <
          p.toNat * 2 ^ 32 + p.toNat * 2 ^ 32 := Nat.add_lt_add h hprod_lt
      _ = 2 * p.toNat * 2 ^ 32 := by ring
      _ < 2 ^ 64 := by omega
  norm_num [UInt32.size]
  change ((x.toNat + mNat * p.toNat) % 2 ^ 64 / 2 ^ 32) % 2 ^ 32 =
      (x.toNat + mNat * p.toNat) / 2 ^ 32
  rw [Nat.mod_eq_of_lt hsum_lt, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul]
  · exact hsum_lt
  · decide

/-- The native Montgomery quotient stays below twice the modulus, so one conditional
subtraction canonicalizes it. -/
theorem reduceQuotient_toNat_lt_two_mul (negInv : UInt32) (p : UInt64)
    (hp_pos : 0 < p.toNat) (hbound : p.toNat < 2 ^ 31)
    (x : UInt64) (h : x.toNat < p.toNat * 2 ^ 32) :
    (reduceQuotient negInv p x).toNat < 2 * p.toNat := by
  rw [reduceQuotient_toNat negInv p hp_pos hbound x h]
  apply reduceNatQuotient_lt_two_mul <;> simp_all

end Native32
end Montgomery
