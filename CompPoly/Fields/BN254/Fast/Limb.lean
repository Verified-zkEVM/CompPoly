/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

/-!
# Single-limb add-with-carry (`addc`)

The 64-bit add-with-carry primitive and its `Nat` contract, the building block for the
ripple-carry arithmetic of the BN254 fast scalar field.
-/

namespace BN254.Fast

/-- One limb of add-with-carry: `(dᵢ, carry')`, with `carry' ∈ {0,1}` when `c ∈ {0,1}`. -/
@[inline] def addc (a b c : UInt64) : UInt64 × UInt64 :=
  let s1 := a + b
  let c1 := if s1 < a then 1 else 0
  let s2 := s1 + c
  let c2 := if s2 < s1 then 1 else 0
  (s2, c1 + c2)

/-- One limb of add-with-carry is correct: the low word plus the carry-out times the base
recovers the sum of the inputs and the carry-in; the carry-out is a single bit (given a
single-bit carry-in) and the result fits in a word. -/
theorem addc_spec (a b c : UInt64) (hc : c.toNat ≤ 1) :
    (addc a b c).1.toNat + (addc a b c).2.toNat * 2 ^ 64 = a.toNat + b.toNat + c.toNat
    ∧ (addc a b c).2.toNat ≤ 1
    ∧ (addc a b c).1.toNat < 2 ^ 64 := by
  have ha := UInt64.toNat_lt a
  have hb := UInt64.toNat_lt b
  have l11 : ((1 : UInt64) + 1).toNat = 2 := by decide
  have l10 : ((1 : UInt64) + 0).toNat = 1 := by decide
  have l01 : ((0 : UInt64) + 1).toNat = 1 := by decide
  have l00 : ((0 : UInt64) + 0).toNat = 0 := by decide
  unfold addc
  dsimp only
  by_cases h1 : a + b < a
  · by_cases h2 : a + b + c < a + b
    · simp only [if_pos h1, if_pos h2, l11]
      rw [UInt64.lt_iff_toNat_lt] at h1 h2
      simp only [UInt64.toNat_add] at h1 h2 ⊢; omega
    · simp only [if_pos h1, if_neg h2, l10]
      rw [UInt64.lt_iff_toNat_lt] at h1 h2
      simp only [UInt64.toNat_add] at h1 h2 ⊢; omega
  · by_cases h2 : a + b + c < a + b
    · simp only [if_neg h1, if_pos h2, l01]
      rw [UInt64.lt_iff_toNat_lt] at h1 h2
      simp only [UInt64.toNat_add] at h1 h2 ⊢; omega
    · simp only [if_neg h1, if_neg h2, l00]
      rw [UInt64.lt_iff_toNat_lt] at h1 h2
      simp only [UInt64.toNat_add] at h1 h2 ⊢; omega




end BN254.Fast
