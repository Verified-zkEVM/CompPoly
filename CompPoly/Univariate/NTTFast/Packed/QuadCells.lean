/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Packed.Radix4Lemmas
public import CompPoly.Univariate.NTTFast.Packed.Radix4Lemmas

/-! # Explicit-length batches of independent radix-four cells -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Execute an explicit number of cells while keeping the twiddle stride fixed. -/
def quadCells [Zero R] [Add R] [Sub R] [Mul R]
    (th tl : Array R) (q j i0 i1 i2 i3 : Nat) (a : Array R) : Nat → Array R
  | 0 => a
  | count + 1 =>
    let outputs := quadAt th tl q j i0 i1 i2 i3 a 0
    let b := (((a.setIfInBounds i0 outputs.1).setIfInBounds i1 outputs.2.1).setIfInBounds i2
      outputs.2.2.1).setIfInBounds i3 outputs.2.2.2
    quadCells th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) b count

/-- Executing a batch preserves the working array's size. -/
@[simp] theorem size_quadCells [Zero R] [Add R] [Sub R] [Mul R]
    (th tl : Array R) (q j i0 i1 i2 i3 : Nat) (a : Array R) (count : Nat) :
    (quadCells th tl q j i0 i1 i2 i3 a count).size = a.size := by
  induction count generalizing j i0 i1 i2 i3 a with
  | zero => rfl
  | succ count ih => simp only [quadCells, ih, Array.size_setIfInBounds]

/-- A disjoint batch has the independent-cell coordinate formula. -/
theorem getD_quadCells [Field R] (th tl : Array R) (q j i0 i1 i2 i3 : Nat)
    (a : Array R) (count : Nat) (hs : i3 + count ≤ a.size)
    (h01 : i0 + count ≤ i1) (h12 : i1 + count ≤ i2)
    (h23 : i2 + count ≤ i3) (k : Nat) :
    (quadCells th tl q j i0 i1 i2 i3 a count).getD k 0 =
      quadValue th tl q j i0 i1 i2 i3 count a k := by
  induction count generalizing j i0 i1 i2 i3 a with
  | zero => simp (disch := omega) only [quadCells, quadValue, Nat.add_zero, ite_eq_right]
  | succ count ih =>
    rw [quadCells, ih _ _ _ _ _ _ (by simp only [Array.size_setIfInBounds]; omega)
      (by omega) (by omega) (by omega)]
    exact quadValue_step th tl q j i0 i1 i2 i3 count a hs h01 h12 h23 k

/-- The ordinary inner loop executes exactly its remaining number of cells. -/
theorem butterflyDIFRadix4Inner_eq_quadCells [Field R] (th tl : Array R)
    (q j i0 i1 i2 i3 : Nat) (a : Array R) :
    Plan.butterflyDIFRadix4Inner th tl q j i0 i1 i2 i3 a =
      quadCells th tl q j i0 i1 i2 i3 a (q - j) := by
  rw [Plan.butterflyDIFRadix4Inner]
  split
  · rename_i hj
    have he : q - j = (q - (j + 1)) + 1 := by omega
    rw [he, quadCells]
    simpa only [quadAt, quadOutputs, Nat.add_zero, Array.set!] using
      butterflyDIFRadix4Inner_eq_quadCells th tl q (j + 1)
        (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) _
  · have he : q - j = 0 := by omega
    rw [he, quadCells]
termination_by q - j
decreasing_by omega

/-- Splitting a batch after a fixed number of cells changes only the loop counters. -/
theorem quadCells_add [Zero R] [Add R] [Sub R] [Mul R] (th tl : Array R)
    (q j i0 i1 i2 i3 : Nat) (a : Array R) (left right : Nat) :
    quadCells th tl q j i0 i1 i2 i3 a (left + right) =
      quadCells th tl q (j + left) (i0 + left) (i1 + left) (i2 + left) (i3 + left)
        (quadCells th tl q j i0 i1 i2 i3 a left) right := by
  induction left generalizing j i0 i1 i2 i3 a with
  | zero => simp only [Nat.zero_add, Nat.add_zero, quadCells]
  | succ left ih =>
    rw [Nat.succ_add, quadCells, quadCells, ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 left]

end CompPoly.CPolynomial.NTTFast.Packed
