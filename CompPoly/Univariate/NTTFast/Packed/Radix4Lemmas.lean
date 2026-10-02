/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
public import CompPoly.Univariate.NTTFast.Packed.ButterflyLemmas

/-! # Coordinate semantics of independent radix-four DIF cells -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The four scalar outputs of two adjacent DIF layers. -/
def quadOutputs [Add R] [Sub R] [Mul R] (w0 w1 w : R) (x0 x1 x2 x3 : R) : R × R × R × R :=
  let a0 := x0 + x2
  let a1 := x1 + x3
  let a2 := w0 * (x0 - x2)
  let a3 := w1 * (x1 - x3)
  (a0 + a1, w * (a0 - a1), a2 + a3, w * (a2 - a3))

/-- One independent cell reads four input coordinates at the same lane offset. -/
def quadAt [Zero R] [Add R] [Sub R] [Mul R] (th tl : Array R) (q j i0 i1 i2 i3 : Nat)
    (a : Array R) (offset : Nat) : R × R × R × R :=
  quadOutputs (th.getD (j + offset) 0) (th.getD (j + offset + q) 0) (tl.getD (j + offset) 0)
    (a.getD (i0 + offset) 0) (a.getD (i1 + offset) 0)
    (a.getD (i2 + offset) 0) (a.getD (i3 + offset) 0)

/-- Pointwise result of a complete range of independent radix-four cells. -/
def quadValue [Zero R] [Add R] [Sub R] [Mul R] (th tl : Array R) (q j i0 i1 i2 i3 count : Nat)
    (a : Array R) (k : Nat) : R :=
  if i0 ≤ k ∧ k < i0 + count then (quadAt th tl q j i0 i1 i2 i3 a (k - i0)).1 else
  if i1 ≤ k ∧ k < i1 + count then (quadAt th tl q j i0 i1 i2 i3 a (k - i1)).2.1 else
  if i2 ≤ k ∧ k < i2 + count then (quadAt th tl q j i0 i1 i2 i3 a (k - i2)).2.2.1 else
  if i3 ≤ k ∧ k < i3 + count then (quadAt th tl q j i0 i1 i2 i3 a (k - i3)).2.2.2 else
  a.getD k 0

set_option maxHeartbeats 1200000 in
private theorem quadValue_step [Field R] (th tl : Array R) (q j i0 i1 i2 i3 count : Nat)
    (a : Array R) (hs : i3 + (count + 1) ≤ a.size)
    (h01 : i0 + (count + 1) ≤ i1) (h12 : i1 + (count + 1) ≤ i2)
    (h23 : i2 + (count + 1) ≤ i3) (k : Nat) :
    let outputs := quadAt th tl q j i0 i1 i2 i3 a 0
    let b := (((a.setIfInBounds i0 outputs.1).setIfInBounds i1 outputs.2.1).setIfInBounds i2
      outputs.2.2.1).setIfInBounds i3 outputs.2.2.2
    quadValue th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) count b k =
      quadValue th tl q j i0 i1 i2 i3 (count + 1) a k := by
  dsimp only
  unfold quadValue quadAt quadOutputs
  simp (config := { maxSteps := 1000000 }) (disch := (simp -failIfUnchanged only
    [Array.size_setIfInBounds] <;> omega)) only
    [getD_setIfInBounds]
  by_cases hk0 : k = i0
  · subst k
    simp (disch := omega) only [Nat.sub_self, Nat.add_zero, ite_eq_left, ite_eq_right, ↓reduceIte]
  · by_cases hk1 : k = i1
    · subst k
      simp (disch := omega) only [Nat.sub_self, Nat.add_zero, ite_eq_left, ite_eq_right, ↓reduceIte]
    · by_cases hk2 : k = i2
      · subst k
        simp (disch := omega) only [Nat.sub_self, Nat.add_zero, ite_eq_left, ite_eq_right,
          ↓reduceIte]
      · by_cases hk3 : k = i3
        · subst k
          simp (disch := omega) only [Nat.sub_self, Nat.add_zero, ite_eq_left, ite_eq_right,
            ↓reduceIte]
        · by_cases hr0 : i0 ≤ k ∧ k < i0 + (count + 1)
          · have he0 : i0 + 1 + (k - (i0 + 1)) = i0 + (k - i0) := by omega
            have he1 : i1 + 1 + (k - (i0 + 1)) = i1 + (k - i0) := by omega
            have he2 : i2 + 1 + (k - (i0 + 1)) = i2 + (k - i0) := by omega
            have he3 : i3 + 1 + (k - (i0 + 1)) = i3 + (k - i0) := by omega
            have hew : j + 1 + (k - (i0 + 1)) = j + (k - i0) := by omega
            simp (disch := omega) only [he0, he1, he2, he3, ite_eq_left, ite_eq_right]
          · by_cases hr1 : i1 ≤ k ∧ k < i1 + (count + 1)
            · have he0 : i0 + 1 + (k - (i1 + 1)) = i0 + (k - i1) := by omega
              have he1 : i1 + 1 + (k - (i1 + 1)) = i1 + (k - i1) := by omega
              have he2 : i2 + 1 + (k - (i1 + 1)) = i2 + (k - i1) := by omega
              have he3 : i3 + 1 + (k - (i1 + 1)) = i3 + (k - i1) := by omega
              have hew : j + 1 + (k - (i1 + 1)) = j + (k - i1) := by omega
              simp (disch := omega) only [he0, he1, he2, he3, hew, ite_eq_left, ite_eq_right]
            · by_cases hr2 : i2 ≤ k ∧ k < i2 + (count + 1)
              · have he0 : i0 + 1 + (k - (i2 + 1)) = i0 + (k - i2) := by omega
                have he1 : i1 + 1 + (k - (i2 + 1)) = i1 + (k - i2) := by omega
                have he2 : i2 + 1 + (k - (i2 + 1)) = i2 + (k - i2) := by omega
                have he3 : i3 + 1 + (k - (i2 + 1)) = i3 + (k - i2) := by omega
                have hew : j + 1 + (k - (i2 + 1)) = j + (k - i2) := by omega
                simp (disch := omega) only [he0, he1, he2, he3, hew, ite_eq_left, ite_eq_right]
              · by_cases hr3 : i3 ≤ k ∧ k < i3 + (count + 1)
                · have he0 : i0 + 1 + (k - (i3 + 1)) = i0 + (k - i3) := by omega
                  have he1 : i1 + 1 + (k - (i3 + 1)) = i1 + (k - i3) := by omega
                  have he2 : i2 + 1 + (k - (i3 + 1)) = i2 + (k - i3) := by omega
                  have he3 : i3 + 1 + (k - (i3 + 1)) = i3 + (k - i3) := by omega
                  have hew : j + 1 + (k - (i3 + 1)) = j + (k - i3) := by omega
                  simp (disch := omega) only [he0, he1, he2, he3, hew, ite_eq_left, ite_eq_right]
                · simp (disch := omega) only [ite_eq_left, ite_eq_right]

/-- The ordinary radix-four inner loop has the independent-cell coordinate formula. -/
theorem getD_butterflyDIFRadix4Inner [Field R] (th tl : Array R) (q j i0 i1 i2 i3 : Nat)
    (a : Array R) (hs : i3 + (q - j) ≤ a.size)
    (h01 : i0 + (q - j) ≤ i1) (h12 : i1 + (q - j) ≤ i2)
    (h23 : i2 + (q - j) ≤ i3) (k : Nat) :
    (Plan.butterflyDIFRadix4Inner th tl q j i0 i1 i2 i3 a).getD k 0 =
      quadValue th tl q j i0 i1 i2 i3 (q - j) a k := by
  rw [Plan.butterflyDIFRadix4Inner]
  split
  · rename_i hj
    have he : q - j = (q - (j + 1)) + 1 := by omega
    rw [getD_butterflyDIFRadix4Inner th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) _
      (by simp only [Array.size_set!]; omega) (by omega) (by omega) (by omega), he]
    exact quadValue_step th tl q j i0 i1 i2 i3 (q - (j + 1)) a
      (by omega) (by omega) (by omega) (by omega) k
  · have he : q - j = 0 := by omega
    simp (disch := omega) only [he, quadValue, Nat.add_zero, ite_eq_right]
termination_by q - j
decreasing_by omega

end CompPoly.CPolynomial.NTTFast.Packed
