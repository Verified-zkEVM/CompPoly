/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
public import CompPoly.Univariate.NTTFast.Packed.ButterflyLemmas
public import CompPoly.Univariate.NTTFast.Packed.Arithmetic
import Mathlib.Tactic.IntervalCases

/-! # Coordinate semantics of the four final DIF layers -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- A single radix-two layer inside a sixteen-coordinate block. -/
def layer16Value [Field R] (tw : Array R) (half : Nat)
    (a : Array R) (base offset : Nat) : R :=
  let first := base + offset / (2 * half) * (2 * half) + offset % half
  if offset % (2 * half) < half then
    a.getD first 0 + a.getD (first + half) 0
  else tw.getD (offset % half) 0 * (a.getD first 0 - a.getD (first + half) 0)

/-- The layer with butterfly half-width 8 on one sixteen-coordinate block. -/
def layer16_8 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) : Array R :=
  let a := Plan.butterflyDIFInner tw 8 0 (base + 0) (base + 8) a
  a

/-- One complete local layer preserves the array size. -/
@[simp] theorem size_layer16_8 [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    (layer16_8 tw a base).size = a.size := by
  unfold layer16_8
  simp only [Plan.size_butterflyDIFInner]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
/-- The local layer has the ordinary pairwise butterfly formula. -/
theorem getD_layer16_8 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (offset : Nat) (ho : offset < 16) :
    (layer16_8 tw a base).getD (base + offset) 0 = layer16Value tw 8 a base offset := by
  unfold layer16_8 layer16Value
  interval_cases offset <;>
    simp (disch := (first
      | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
      | fail)) only
      [getD_butterflyDIFInner_left, getD_butterflyDIFInner_right,
        Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceLT, Nat.reduceSub, Nat.add_sub_cancel_left, Nat.add_sub_add_left,
        Nat.sub_self, Nat.add_zero, Nat.zero_add, ↓reduceIte]

/-- The first coordinate uses offset zero, even when simplification has removed `+ 0`. -/
theorem getD_layer16_8_zero [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) :
    (layer16_8 tw a base).getD base 0 = layer16Value tw 8 a base 0 := by
  simpa only [Nat.add_zero] using getD_layer16_8 tw a base hs 0 (by decide)

/-- Coordinates outside the block are unchanged by the local layer. -/
theorem getD_layer16_8_outside [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (k : Nat)
    (hk : ¬(base ≤ k ∧ k < base + 16)) :
    (layer16_8 tw a base).getD k 0 = a.getD k 0 := by
  unfold layer16_8
  simp (disch := (first
    | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
    | fail)) only
    [getD_butterflyDIFInner_outside]

/-- The layer with butterfly half-width 4 on one sixteen-coordinate block. -/
def layer16_4 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) : Array R :=
  let a := Plan.butterflyDIFInner tw 4 0 (base + 0) (base + 4) a
  let a := Plan.butterflyDIFInner tw 4 0 (base + 8) (base + 12) a
  a

/-- One complete local layer preserves the array size. -/
@[simp] theorem size_layer16_4 [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    (layer16_4 tw a base).size = a.size := by
  unfold layer16_4
  simp only [Plan.size_butterflyDIFInner]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
/-- The local layer has the ordinary pairwise butterfly formula. -/
theorem getD_layer16_4 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (offset : Nat) (ho : offset < 16) :
    (layer16_4 tw a base).getD (base + offset) 0 = layer16Value tw 4 a base offset := by
  unfold layer16_4 layer16Value
  interval_cases offset <;>
    simp (disch := (first
      | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
      | fail)) only
      [getD_butterflyDIFInner_left, getD_butterflyDIFInner_right, getD_butterflyDIFInner_outside,
        Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceLT, Nat.reduceSub, Nat.add_sub_cancel_left, Nat.add_sub_add_left,
        Nat.sub_self, Nat.add_zero, Nat.zero_add, ↓reduceIte]

/-- The first coordinate uses offset zero, even when simplification has removed `+ 0`. -/
theorem getD_layer16_4_zero [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) :
    (layer16_4 tw a base).getD base 0 = layer16Value tw 4 a base 0 := by
  simpa only [Nat.add_zero] using getD_layer16_4 tw a base hs 0 (by decide)

/-- Coordinates outside the block are unchanged by the local layer. -/
theorem getD_layer16_4_outside [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (k : Nat)
    (hk : ¬(base ≤ k ∧ k < base + 16)) :
    (layer16_4 tw a base).getD k 0 = a.getD k 0 := by
  unfold layer16_4
  simp (disch := (first
    | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
    | fail)) only
    [getD_butterflyDIFInner_outside]

/-- The layer with butterfly half-width 2 on one sixteen-coordinate block. -/
def layer16_2 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) : Array R :=
  let a := Plan.butterflyDIFInner tw 2 0 (base + 0) (base + 2) a
  let a := Plan.butterflyDIFInner tw 2 0 (base + 4) (base + 6) a
  let a := Plan.butterflyDIFInner tw 2 0 (base + 8) (base + 10) a
  let a := Plan.butterflyDIFInner tw 2 0 (base + 12) (base + 14) a
  a

/-- One complete local layer preserves the array size. -/
@[simp] theorem size_layer16_2 [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    (layer16_2 tw a base).size = a.size := by
  unfold layer16_2
  simp only [Plan.size_butterflyDIFInner]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
/-- The local layer has the ordinary pairwise butterfly formula. -/
theorem getD_layer16_2 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (offset : Nat) (ho : offset < 16) :
    (layer16_2 tw a base).getD (base + offset) 0 = layer16Value tw 2 a base offset := by
  unfold layer16_2 layer16Value
  interval_cases offset <;>
    simp (disch := (first
      | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
      | fail)) only
      [getD_butterflyDIFInner_left, getD_butterflyDIFInner_right, getD_butterflyDIFInner_outside,
        Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceLT, Nat.reduceSub, Nat.add_sub_cancel_left, Nat.add_sub_add_left,
        Nat.sub_self, Nat.add_zero, Nat.zero_add, ↓reduceIte]

/-- The first coordinate uses offset zero, even when simplification has removed `+ 0`. -/
theorem getD_layer16_2_zero [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) :
    (layer16_2 tw a base).getD base 0 = layer16Value tw 2 a base 0 := by
  simpa only [Nat.add_zero] using getD_layer16_2 tw a base hs 0 (by decide)

/-- Coordinates outside the block are unchanged by the local layer. -/
theorem getD_layer16_2_outside [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (k : Nat)
    (hk : ¬(base ≤ k ∧ k < base + 16)) :
    (layer16_2 tw a base).getD k 0 = a.getD k 0 := by
  unfold layer16_2
  simp (disch := (first
    | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
    | fail)) only
    [getD_butterflyDIFInner_outside]

/-- The layer with butterfly half-width 1 on one sixteen-coordinate block. -/
def layer16_1 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) : Array R :=
  let a := Plan.butterflyDIFInner tw 1 0 (base + 0) (base + 1) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 2) (base + 3) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 4) (base + 5) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 6) (base + 7) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 8) (base + 9) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 10) (base + 11) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 12) (base + 13) a
  let a := Plan.butterflyDIFInner tw 1 0 (base + 14) (base + 15) a
  a

/-- One complete local layer preserves the array size. -/
@[simp] theorem size_layer16_1 [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    (layer16_1 tw a base).size = a.size := by
  unfold layer16_1
  simp only [Plan.size_butterflyDIFInner]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
/-- The local layer has the ordinary pairwise butterfly formula. -/
theorem getD_layer16_1 [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (offset : Nat) (ho : offset < 16) :
    (layer16_1 tw a base).getD (base + offset) 0 = layer16Value tw 1 a base offset := by
  unfold layer16_1 layer16Value
  interval_cases offset <;>
    simp (disch := (first
      | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
      | fail)) only
      [getD_butterflyDIFInner_left, getD_butterflyDIFInner_right, getD_butterflyDIFInner_outside,
        Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceLT,
        Nat.sub_self, Nat.add_zero, ↓reduceIte]

/-- The first coordinate uses offset zero, even when simplification has removed `+ 0`. -/
theorem getD_layer16_1_zero [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) :
    (layer16_1 tw a base).getD base 0 = layer16Value tw 1 a base 0 := by
  simpa only [Nat.add_zero] using getD_layer16_1 tw a base hs 0 (by decide)

/-- Coordinates outside the block are unchanged by the local layer. -/
theorem getD_layer16_1_outside [Field R] (tw : Array R) (a : Array R)
    (base : Nat) (hs : base + 16 ≤ a.size) (k : Nat)
    (hk : ¬(base ≤ k ∧ k < base + 16)) :
    (layer16_1 tw a base).getD k 0 = a.getD k 0 := by
  unfold layer16_1
  simp (disch := (first
    | (simp -failIfUnchanged only [Plan.size_butterflyDIFInner] <;> omega)
    | fail)) only
    [getD_butterflyDIFInner_outside]

end CompPoly.CPolynomial.NTTFast.Packed
