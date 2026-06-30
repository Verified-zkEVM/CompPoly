/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Basic

/-!
# Montgomery Reduction — native `UInt32 × UInt64`, radix `R = 2^32`

The word-level bridge specialising `Montgomery.Basic` to 32-bit-word prime fields: the
Montgomery product fits in a `UInt64`, the radix is `R = UInt32.size = 2^32`, and the
high word is extracted with `>>> 32`. These lemmas relate the native-word computation to
the `Nat` formula proved generically in `Montgomery.Basic`, parameterized by the prime
`p`, the `UInt32` negated inverse `negInv`, and the `UInt64` modulus `modN`.

A future 64-bit family would add a parallel `Native64` bridge (`>>> 64`,
`UInt64 × UInt128`) over the same `Montgomery.Basic` core.
-/

namespace Montgomery
namespace Native32

/-- The native high-word extraction agrees with the `Nat`-level Montgomery quotient. -/
theorem u_eq_nat (negInv : UInt32) (modN : UInt64) (p : Nat)
    (hmod : modN.toNat = p) (hp_pos : 0 < p)
    (hbound : 2 * p * UInt32.size < 2 ^ 64)
    (x : UInt64) (h : x.toNat < p * UInt32.size) :
    ((((x + (x.toUInt32 * negInv).toUInt64 * modN) >>> 32).toUInt32).toNat) =
      (x.toNat + ((x.toNat % UInt32.size * negInv.toNat) % UInt32.size) * p) / UInt32.size := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt64.toNat_ofNat,
    hmod, Nat.shiftRight_eq_div_pow]
  norm_num [UInt32.size] at h hbound ⊢
  let mNat := x.toNat * negInv.toNat % 4294967296
  have hm_lt : mNat < 4294967296 := Nat.mod_lt _ (by decide)
  have hsum_lt : x.toNat + mNat * p < 18446744073709551616 := by
    have hprod_lt : mNat * p < p * 4294967296 := by
      have := Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
      simpa [Nat.mul_comm] using this
    calc x.toNat + mNat * p < p * 4294967296 + p * 4294967296 := Nat.add_lt_add h hprod_lt
      _ = 2 * p * 4294967296 := by ring
      _ < 18446744073709551616 := hbound
  change ((x.toNat + mNat * p) % 18446744073709551616 / 4294967296) % 4294967296 =
      (x.toNat + mNat * p) / 4294967296
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul]
  · exact hsum_lt
  · decide

/-- The native Montgomery quotient stays below `2 * p`, so a single conditional subtract
canonicalises it. -/
theorem u_lt_two_mul (negInv : UInt32) (modN : UInt64) (p : Nat)
    (hmod : modN.toNat = p) (hp_pos : 0 < p)
    (hbound : 2 * p * UInt32.size < 2 ^ 64)
    (x : UInt64) (h : x.toNat < p * UInt32.size) :
    ((((x + (x.toUInt32 * negInv).toUInt64 * modN) >>> 32).toUInt32).toNat) < 2 * p := by
  rw [u_eq_nat negInv modN p hmod hp_pos hbound x h]
  let mNat := x.toNat % UInt32.size * negInv.toNat % UInt32.size
  have hm_lt : mNat < UInt32.size := Nat.mod_lt _ (by decide)
  rw [Nat.div_lt_iff_lt_mul]
  · have hprod_lt : mNat * p < UInt32.size * p := Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
    have hprod_lt' : mNat * p < p * UInt32.size := by
      simpa [Nat.mul_comm] using hprod_lt
    change x.toNat + mNat * p < 2 * p * UInt32.size
    calc x.toNat + mNat * p < p * UInt32.size + p * UInt32.size :=
          Nat.add_lt_add h hprod_lt'
      _ = 2 * p * UInt32.size := by ring
  · decide

end Native32
end Montgomery
