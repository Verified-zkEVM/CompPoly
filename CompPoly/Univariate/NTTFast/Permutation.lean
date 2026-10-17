/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTT.Transform
public import CompPoly.Data.Array.Involution

/-! # Bit reversal as an array index involution -/

@[expose] public section
namespace CompPoly.CPolynomial.NTT.Transform
private theorem testBit_one (i : Nat) : (1 : Nat).testBit i = decide (i = 0) := by
  simpa only [Nat.pow_zero, eq_comm] using (Nat.testBit_two_pow (n := 0) (m := i))

/-- Reversal reads bit positions in the opposite order within the selected width. -/
theorem bitRevNat_testBit (bits i j : Nat) :
    (bitRevNat bits i).testBit j = (decide (j < bits) && i.testBit (bits - 1 - j)) := by
  induction bits generalizing i j with
  | zero => simp only [bitRevNat, Nat.zero_testBit, Nat.not_lt_zero, decide_false, Bool.false_and]
  | succ bits ih =>
    simp only [bitRevNat, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
      testBit_one, ih, Nat.testBit_shiftRight]
    by_cases hj : j < bits
    · have hn : ¬ j ≥ bits := by omega
      have hj' : j < bits + 1 := by omega
      simp only [hj, hn, hj', decide_true, decide_false, Bool.false_and, Bool.true_and,
        Bool.false_or]
      congr 1
      omega
    · by_cases he : j = bits
      · subst j
        simp only [Nat.le_refl, decide_true, Nat.sub_self, Bool.and_true,
          Nat.lt_irrefl, decide_false, Bool.false_and, Bool.or_false,
          Nat.lt_succ_self, Bool.true_and, Nat.add_sub_cancel]
      · have hn : j ≥ bits := by omega
        have hj' : ¬ j < bits + 1 := by omega
        have hsub : j - bits ≠ 0 := by omega
        simp only [hj, hn, hj', hsub, decide_false, decide_true,
          Bool.and_false, Bool.false_and, Bool.or_false]

/-- Reversing twice restores every index within the selected width. -/
theorem bitRevNat_involutive (bits i : Nat) (hi : i < 2 ^ bits) :
    bitRevNat bits (bitRevNat bits i) = i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitRevNat_testBit]
  by_cases hj : j < bits
  · have hh : bits - 1 - j < bits := by omega
    rw [bitRevNat_testBit]
    simp only [hj, hh, decide_true, Bool.true_and]
    congr 1
    omega
  · have hpow : 2 ^ bits ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [hj, decide_false, Bool.false_and,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hi hpow)]
end CompPoly.CPolynomial.NTT.Transform
