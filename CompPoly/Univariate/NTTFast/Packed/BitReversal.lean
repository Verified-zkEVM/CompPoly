/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Reverse32
import Mathlib.Tactic.Ring

/-! # Bit-reversal identities for interleaving reversed blocks -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Reversing concatenated low and high bit groups reverses each group and swaps their positions. -/
theorem bitRevNat_concat (high low x y : Nat) (hy : y < 2 ^ low) :
    NTT.Transform.bitRevNat (high + low) (2 ^ low * x + y) =
      2 ^ high * NTT.Transform.bitRevNat low y + NTT.Transform.bitRevNat high x := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [bitRevNat_testBit,
    Nat.testBit_two_pow_mul_add _ (NTT.Transform.bitRevNat_lt high x)]
  by_cases hk : k < high
  · have hsum : k < high + low := by omega
    have hindex : ¬high + low - 1 - k < low := by omega
    have he : high + low - 1 - k - low = high - 1 - k := by omega
    rw [ite_eq_left hsum, ite_eq_left hk,
      Nat.testBit_two_pow_mul_add x hy, ite_eq_right hindex,
      bitRevNat_testBit, ite_eq_left hk, he]
  · by_cases hsum : k < high + low
    · have hindex : high + low - 1 - k < low := by omega
      have hbit : k - high < low := by omega
      have he : high + low - 1 - k = low - 1 - (k - high) := by omega
      rw [ite_eq_left hsum, ite_eq_right hk, Nat.testBit_two_pow_mul_add x hy,
        ite_eq_left hindex, bitRevNat_testBit, ite_eq_left hbit, he]
    · have hbit : ¬k - high < low := by omega
      rw [ite_eq_right hsum, ite_eq_right hk, bitRevNat_testBit, ite_eq_right hbit]

end CompPoly.CPolynomial.NTTFast.Packed
