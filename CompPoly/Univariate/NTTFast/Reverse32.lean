/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTT.Transform
import Mathlib.Tactic.IntervalCases

/-! # Thirty-two-bit word reversal for bit-reversed indexing -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast

/-- Reverse the thirty-two bits of a word. -/
@[inline] def reverse32 (x : UInt32) : UInt32 :=
  let x : UInt32 := ((x >>> (1 : UInt32)) &&& (0x55555555 : UInt32)) ||| ((x &&& (0x55555555 :
    UInt32)) <<< (1 : UInt32))
  let x : UInt32 := ((x >>> (2 : UInt32)) &&& (0x33333333 : UInt32)) ||| ((x &&& (0x33333333 :
    UInt32)) <<< (2 : UInt32))
  let x : UInt32 := ((x >>> (4 : UInt32)) &&& (0x0f0f0f0f : UInt32)) ||| ((x &&& (0x0f0f0f0f :
    UInt32)) <<< (4 : UInt32))
  let x : UInt32 := ((x >>> (8 : UInt32)) &&& (0x00ff00ff : UInt32)) ||| ((x &&& (0x00ff00ff :
    UInt32)) <<< (8 : UInt32))
  (x >>> (16 : UInt32)) ||| (x <<< (16 : UInt32))

/-- The mask-and-shift word permutation reverses exactly thirty-two bits. -/
theorem reverse32_toBitVec (x : UInt32) : (reverse32 x).toBitVec = x.toBitVec.reverse := by
  have h32 : (32 : BitVec 32).toNat = 32 := by decide
  unfold reverse32
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_and, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_ofNat]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;>
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft',
      BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_ofNat, BitVec.toNat_umod, h32,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceLT, Nat.testBit_eq_decide_div_mod_eq, Nat.reduceDiv, Nat.reduceEqDiff,
      decide_true, decide_false, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true,
      Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false]


/-- The low `bits` input bits appear in reversed order and all higher output bits vanish. -/
theorem bitRevNat_testBit (bits i k : Nat) :
    (NTT.Transform.bitRevNat bits i).testBit k =
      if k < bits then i.testBit (bits - 1 - k) else false := by
  have hone (t : Nat) : Nat.testBit 1 t = decide (t = 0) := by
    simpa only [Nat.pow_zero, eq_comm] using (Nat.testBit_two_pow (n := 0) (m := t))
  induction bits generalizing i k with
  | zero => simp only [NTT.Transform.bitRevNat, Nat.zero_testBit, Nat.not_lt_zero, ite_false]
  | succ bits ih =>
    rw [NTT.Transform.bitRevNat, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_and, hone, ih]
    by_cases hk : k < bits
    · have hkle : ¬k ≥ bits := by omega
      have hk1 : k < bits + 1 := by omega
      have he : 1 + (bits - 1 - k) = bits + 1 - 1 - k := by omega
      simp only [hk, hk1, hkle, decide_false, Bool.false_and, Bool.false_or,
        ite_true, Nat.testBit_shiftRight, he]
    · by_cases hke : k = bits
      · subst k
        simp only [Nat.le_refl, decide_true, Nat.sub_self, Bool.true_and,
          Nat.lt_irrefl, ite_false, Bool.or_false, Nat.lt_succ_self, ite_true,
          Nat.add_sub_cancel, Nat.testBit_shiftRight, Bool.and_true]
      · have hkl : k ≥ bits := by omega
        have hkn : ¬k < bits + 1 := by omega
        have hks : ¬k - bits = 0 := by omega
        simp only [hk, hkl, hkn, hks, decide_true, decide_false, Bool.and_false,
          Bool.or_false, ite_false]

/-- A shifted thirty-two-bit reversal computes the transform's bounded index permutation. -/
theorem reverse32_shift_eq_bitRevNat (bits i : Nat) (hb : 0 < bits) (h32 : bits ≤ 32) :
    (reverse32 i.toUInt32 >>> (32 - bits).toUInt32).toNat =
      NTT.Transform.bitRevNat bits i := by
  have hs : 32 - bits < 32 := by omega
  have hword : (32 - bits).toUInt32.toBitVec.toNat = 32 - bits := by
    simp only [Nat.toUInt32_eq, UInt32.toBitVec_ofNat', BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : ((32 - bits).toUInt32.toBitVec % (32 : BitVec 32)).toNat = 32 - bits := by
    rw [BitVec.toNat_umod, hword]
    change (32 - bits) % 32 = 32 - bits
    exact Nat.mod_eq_of_lt hs
  apply Nat.eq_of_testBit_eq
  intro k
  rw [← UInt32.toNat_toBitVec, BitVec.testBit_toNat, UInt32.toBitVec_shiftRight,
    reverse32_toBitVec, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hmod,
    BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, bitRevNat_testBit]
  by_cases hk : k < bits
  · have ht : 32 - bits + k < 32 := by omega
    have he : 32 - 1 - (32 - bits + k) = bits - 1 - k := by omega
    have hi : bits - 1 - k < 32 := by omega
    simp only [ht, hk, he, decide_true, Bool.true_and, ite_true,
      Nat.toUInt32_eq, UInt32.toBitVec_ofNat', BitVec.getLsbD_ofNat]
    simp only [hi, decide_true, Bool.true_and]
  · have ht : ¬32 - bits + k < 32 := by omega
    simp only [ht, hk, decide_false, Bool.false_and, ite_false]

end CompPoly.CPolynomial.NTTFast
