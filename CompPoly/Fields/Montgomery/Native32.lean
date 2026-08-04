/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Basic

/-!
# Native 32-bit Montgomery Reduction

Raw word operations for Montgomery reduction with radix `2 ^ 32`.
-/

@[expose] public section

namespace Montgomery
namespace Native32

/-- Montgomery reduction. -/
@[inline]
def reduceRaw (p32 : UInt32) (p64 : UInt64) (negInv : UInt32) (x : UInt64) : UInt32 :=
  let m := (x.toUInt32 * negInv).toUInt64
  let u := ((x + m * p64) >>> 32).toUInt32
  if u < p32 then u else u - p32

/-- The native pre-subtraction quotient in 32-bit Montgomery reduction. -/
def reduceQuotient (negInv : UInt32) (p x : UInt64) : UInt32 :=
  ((x + (x.toUInt32 * negInv).toUInt64 * p) >>> 32).toUInt32

/-- Conditional subtraction of the modulus in 32-bit Montgomery reduction. -/
def conditionalSubtract (p32 : UInt32) (u : UInt32) : UInt32 :=
  if u < p32 then u else u - p32

variable {modulus : ℕ} {p32 negInv u : UInt32} {p64 x : UInt64}

theorem reduceRaw_eq_conditionalSubtract :
    reduceRaw p32 p64 negInv x =
      conditionalSubtract p32 (reduceQuotient negInv p64 x) := rfl

/-- The native quotient agrees with the `Nat`-level Montgomery quotient. -/
theorem reduceQuotient_toNat (hp_pos : 0 < p64.toNat) (hbound : p64.toNat < 2 ^ 31)
    (h : x.toNat < p64.toNat * 2 ^ 32) :
    (reduceQuotient negInv p64 x).toNat =
      reduceNatQuotient (2 ^ 32) p64.toNat negInv.toNat x.toNat := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt64.toNat_ofNat,
    reduceQuotient, reduceNatQuotient, Nat.shiftRight_eq_div_pow]
  let mNat := x.toNat * negInv.toNat % 2 ^ 32
  have hm_lt : mNat < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hsum_lt : x.toNat + mNat * p64.toNat < 2 ^ 64 := by
    have hprod_lt : mNat * p64.toNat < p64.toNat * 2 ^ 32 := by
      have := Nat.mul_lt_mul_of_pos_right hm_lt hp_pos
      simpa [Nat.mul_comm] using this
    calc
      x.toNat + mNat * p64.toNat <
          p64.toNat * 2 ^ 32 + p64.toNat * 2 ^ 32 := Nat.add_lt_add h hprod_lt
      _ = 2 * p64.toNat * 2 ^ 32 := by ring
      _ < 2 ^ 64 := by omega
  norm_num [UInt32.size]
  change ((x.toNat + mNat * p64.toNat) % 2 ^ 64 / 2 ^ 32) % 2 ^ 32 =
      (x.toNat + mNat * p64.toNat) / 2 ^ 32
  rw [Nat.mod_eq_of_lt hsum_lt, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul]
  · exact hsum_lt
  · decide

theorem conditionalSubtract_toNat :
    (conditionalSubtract p32 u).toNat =
      if u.toNat < p32.toNat then u.toNat else u.toNat - p32.toNat := by
  simp only [conditionalSubtract, UInt32.lt_iff_toNat_lt]
  by_cases hx : u.toNat < p32.toNat
  · simp only [if_pos hx]
  · have hp_le_x : p32 ≤ u := by
      rw [UInt32.le_iff_toNat_le]
      omega
    simp only [if_neg hx, UInt32.toNat_sub_of_le _ _ hp_le_x]

/-- Native Montgomery reduction agrees with the natural-number specification. -/
theorem reduceRaw_toNat (hp32 : p32.toNat = modulus) (hp64 : p64.toNat = modulus)
    (hp_pos : 0 < modulus) (hp_bound : modulus < 2 ^ 31)
    (h : x.toNat < modulus * 2 ^ 32) :
    (reduceRaw p32 p64 negInv x).toNat =
      reduceNat (2 ^ 32) modulus negInv.toNat x.toNat := by
  rw [reduceRaw_eq_conditionalSubtract, conditionalSubtract_toNat]
  rw [reduceQuotient_toNat
    (by simpa only [hp64] using hp_pos)
    (by simpa only [hp64] using hp_bound)
    (by simpa only [hp64] using h)]
  rw [hp32, hp64]
  rfl

theorem conditionalSubtract_lt (h : u.toNat < 2 * p32.toNat) :
    (conditionalSubtract p32 u).toNat < p32.toNat := by
  simp only [conditionalSubtract, UInt32.lt_iff_toNat_lt]
  by_cases hx : u.toNat < p32.toNat
  · rw [if_pos hx]
    exact hx
  · have hp_le_x : p32 ≤ u := by
      rw [UInt32.le_iff_toNat_le]
      omega
    rw [if_neg hx, UInt32.toNat_sub_of_le _ _ hp_le_x]
    omega

theorem conditionalSubtract_cast :
    ((conditionalSubtract p32 u).toNat : ZMod p32.toNat) =
      (u.toNat : ZMod p32.toNat) := by
  simp only [conditionalSubtract]
  by_cases hx : u < p32
  · rw [if_pos hx]
  · have hp_le_x : p32 ≤ u := by
      rw [UInt32.le_iff_toNat_le]
      rw [UInt32.lt_iff_toNat_lt] at hx
      exact Nat.le_of_not_gt hx
    rw [if_neg hx, UInt32.toNat_sub_of_le _ _ hp_le_x]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hp_le_x
      exact hp_le_x)]
    simp

theorem reduceRaw_lt (hp : p32.toNat = p64.toNat) (hp_pos : 0 < p64.toNat)
    (hp_bound : p64.toNat < 2 ^ 31)
    (h : x.toNat < p64.toNat * 2 ^ 32) :
    (reduceRaw p32 p64 negInv x).toNat < p32.toNat := by
  rw [reduceRaw_toNat hp rfl hp_pos hp_bound h, hp]
  exact reduceNat_lt (2 ^ 32) p64.toNat negInv.toNat x.toNat
    (by decide) hp_pos h

theorem reduceRaw_cast [Fact (Nat.Prime modulus)]
    (hp32 : p32.toNat = modulus) (hp64 : p64.toNat = modulus)
    (hp_pos : 0 < modulus) (hp_bound : modulus < 2 ^ 31)
    (hnegInv : negInv.toNat * modulus % 2 ^ 32 = 2 ^ 32 - 1)
    (hRne : ((2 ^ 32 : ℕ) : ZMod modulus) ≠ 0)
    (h : x.toNat < modulus * 2 ^ 32) :
    ((reduceRaw p32 p64 negInv x).toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  rw [reduceRaw_toNat hp32 hp64 hp_pos hp_bound h]
  exact reduceNat_cast (2 ^ 32) modulus negInv.toNat
    (by decide) hnegInv hRne x.toNat

end Native32
end Montgomery
