/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Expressions
public import CompPoly.Univariate.NTTFast.Packed.QuadCells
import Mathlib.Tactic.IntervalCases

/-! # Mathematical refinement of sixteen-lane butterfly batches -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Expressions

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
/-- The batched field kernel executes sixteen independent radix-four cells. -/
theorem getD_step16Field [Field R] (th tl : Array R) (q : Nat)
    (j j1 i0 i1 i2 i3 : USize) (a : Array R)
    (hj1 : j1.toNat = j.toNat + q) (hs : i3.toNat + 16 ≤ a.size)
    (h01 : i0.toNat + 16 ≤ i1.toNat) (h12 : i1.toNat + 16 ≤ i2.toNat)
    (h23 : i2.toNat + 16 ≤ i3.toNat) (k : Nat) :
    (step16Field th tl j j1 i0 i1 i2 i3 a).getD k 0 =
      quadValue th tl q j.toNat i0.toNat i1.toNat i2.toNat i3.toNat 16 a k := by
  have hi0 : i0.toNat + 16 ≤ a.size := by omega
  have hi1 : i1.toNat + 16 ≤ a.size := by omega
  have hi2 : i2.toNat + 16 ≤ a.size := by omega
  unfold step16Field readField fieldAdd fieldSub fieldMul quadValue quadAt quadOutputs
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide), hj1]
  simp (config := { maxDischargeDepth := 8, maxSteps := 1000000 }) (disch := (first
    | (simp -failIfUnchanged only
      [splice, Array.size_append, Array.size_extract, size_literal16] <;> omega)
    | fail)) only
    [getD_splice, size_literal16]
  by_cases hk0 : i0.toNat ≤ k ∧ k < i0.toNat + 16
  · obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 16 ∧ k = i0.toNat + offset := by
      exact ⟨k - i0.toNat, by omega, by omega⟩
    subst k
    interval_cases offset <;>
      simp (disch := omega) only [Nat.add_assoc, Nat.sub_self,
      Nat.add_sub_cancel_left, Nat.add_zero, ite_eq_left, ite_eq_right,
      getD_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  · by_cases hk1 : i1.toNat ≤ k ∧ k < i1.toNat + 16
    · obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 16 ∧ k = i1.toNat + offset := by
        exact ⟨k - i1.toNat, by omega, by omega⟩
      subst k
      interval_cases offset <;>
        simp (disch := omega) only [Nat.add_assoc, Nat.sub_self,
      Nat.add_sub_cancel_left, Nat.add_zero, ite_eq_left, ite_eq_right,
      getD_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · by_cases hk2 : i2.toNat ≤ k ∧ k < i2.toNat + 16
      · obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 16 ∧ k = i2.toNat + offset := by
          exact ⟨k - i2.toNat, by omega, by omega⟩
        subst k
        interval_cases offset <;>
          simp (disch := omega) only [Nat.add_assoc, Nat.sub_self,
      Nat.add_sub_cancel_left, Nat.add_zero, ite_eq_left, ite_eq_right,
      getD_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;> simp
        only [Nat.add_comm]
      · by_cases hk3 : i3.toNat ≤ k ∧ k < i3.toNat + 16
        · obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 16 ∧ k = i3.toNat + offset := by
            exact ⟨k - i3.toNat, by omega, by omega⟩
          subst k
          interval_cases offset <;>
            simp (disch := omega) only [Nat.add_assoc, Nat.sub_self,
      Nat.add_sub_cancel_left, Nat.add_zero, ite_eq_left, ite_eq_right,
      getD_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;> simp
        only [Nat.add_comm]
        · simp (disch := omega) only [ite_eq_left, ite_eq_right, ite_self]

/-- The batched expression graph equals the explicit-length scalar batch. -/
theorem step16Field_eq_quadCells [Field R] (th tl : Array R) (q : Nat)
    (j j1 i0 i1 i2 i3 : USize) (a : Array R)
    (hj1 : j1.toNat = j.toNat + q) (hs : i3.toNat + 16 ≤ a.size)
    (h01 : i0.toNat + 16 ≤ i1.toNat) (h12 : i1.toNat + 16 ≤ i2.toNat)
    (h23 : i2.toNat + 16 ≤ i3.toNat) :
    step16Field th tl j j1 i0 i1 i2 i3 a =
      quadCells th tl q j.toNat i0.toNat i1.toNat i2.toNat i3.toNat a 16 := by
  apply array_eq_of_getD _ _ (0 : R)
  · have hi0 : i0.toNat + 16 ≤ a.size := by omega
    have hi1 : i1.toNat + 16 ≤ a.size := by omega
    have hi2 : i2.toNat + 16 ≤ a.size := by omega
    unfold step16Field
    simp (config := { maxDischargeDepth := 8, maxSteps := 1000000 }) (disch := (first
      | (simp -failIfUnchanged only
        [splice, Array.size_append, Array.size_extract, size_literal16] <;> omega)
      | fail)) only
      [size_splice16, size_quadCells]
  · intro k
    rw [getD_step16Field th tl q j j1 i0 i1 i2 i3 a hj1 hs h01 h12 h23,
      getD_quadCells th tl q j.toNat i0.toNat i1.toNat i2.toNat i3.toNat a 16 hs h01 h12 h23]

end CompPoly.CPolynomial.NTTFast.Packed.Expressions
