/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.BitReverse
import Mathlib.Tactic.Ring

/-! # Bit-reversal identities used by the tiled output scatter -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Reversing concatenated low and high bit groups reverses each group and swaps their positions. -/
theorem bitRevNat_concat (high low x y : Nat) (hy : y < 2 ^ low) :
    NTT.Transform.bitRevNat (high + low) (2 ^ low * x + y) =
      2 ^ high * NTT.Transform.bitRevNat low y + NTT.Transform.bitRevNat high x := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Native.bitRevNat_testBit,
    Nat.testBit_two_pow_mul_add _ (NTT.Transform.bitRevNat_lt high x)]
  by_cases hk : k < high
  · have hsum : k < high + low := by omega
    have hindex : ¬high + low - 1 - k < low := by omega
    have he : high + low - 1 - k - low = high - 1 - k := by omega
    rw [ite_eq_left hsum, ite_eq_left hk,
      Nat.testBit_two_pow_mul_add x hy, ite_eq_right hindex,
      Native.bitRevNat_testBit, ite_eq_left hk, he]
  · by_cases hsum : k < high + low
    · have hindex : high + low - 1 - k < low := by omega
      have hbit : k - high < low := by omega
      have he : high + low - 1 - k = low - 1 - (k - high) := by omega
      rw [ite_eq_left hsum, ite_eq_right hk, Nat.testBit_two_pow_mul_add x hy,
        ite_eq_left hindex, Native.bitRevNat_testBit, ite_eq_left hbit, he]
    · have hbit : ¬k - high < low := by omega
      rw [ite_eq_right hsum, ite_eq_right hk, Native.bitRevNat_testBit, ite_eq_right hbit]

/-- A tiled decoder lane is precisely the full transform's reversed input index. -/
theorem bitRevNat_tile (logN m d lane : Nat) (hlog : 6 ≤ logN)
    (hm : m < 2 ^ (logN - 6)) (hd : d < 16) :
    NTT.Transform.bitRevNat logN (m * 16 + d + lane * 2 ^ (logN - 2)) =
      NTT.Transform.bitRevNat 4 d * 2 ^ (logN - 4) +
        NTT.Transform.bitRevNat (logN - 6) m * 4 + NTT.Transform.bitRevNat 2 lane := by
  have hsplit : logN = (2 + (logN - 6)) + 4 := by omega
  have hinput : m * 16 + d + lane * 2 ^ (logN - 2) =
      2 ^ 4 * (2 ^ (logN - 6) * lane + m) + d := by
    have he : logN - 2 = (logN - 6) + 4 := by omega
    rw [he, Nat.pow_add]
    norm_num
    ring
  conv_lhs =>
    rw [hinput]
    arg 1
    rw [hsplit]
  rw [bitRevNat_concat _ 4 _ d hd, bitRevNat_concat 2 _ lane m hm]
  have hexp : 2 + (logN - 6) = logN - 4 := by omega
  rw [hexp]
  simp only [Nat.reducePow]
  ring

end CompPoly.CPolynomial.NTTFast.Packed
