/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Expressions
public import CompPoly.Univariate.NTTFast.Packed.LeafLayers
public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import CompPoly.Univariate.NTTFast.Packed.Unrolled
import Mathlib.Tactic.IntervalCases

/-! # The final DIF layers one at a time

The stage kernels run each of the four final DIF layers over all sixteen-word blocks of a leaf
before the next, each block stored as two halves of eight words. Each stage's field model, a
block's two halves spliced in by `splice8`, is the layer (`leafStage8Field_eq` and its siblings).
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Entries `i, …, i + 7` replaced by `v0, …, v7` where they exist: an eight-entry splice that keeps
the size. -/
def splice8 (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α) : Array α :=
  ((((((((a.setIfInBounds i v0).setIfInBounds (i + 1) v1).setIfInBounds (i + 2) v2).setIfInBounds
    (i + 3) v3).setIfInBounds (i + 4) v4).setIfInBounds (i + 5) v5).setIfInBounds (i + 6)
    v6).setIfInBounds (i + 7) v7)

@[simp] theorem size_splice8 (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α) :
    (splice8 a i v0 v1 v2 v3 v4 v5 v6 v7).size = a.size := by
  simp only [splice8, Array.size_setIfInBounds]

/-- Inside its range, an in-bounds `splice8` reads its values. -/
theorem getD_splice8_in (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α)
    (h : i + 8 ≤ a.size) (k : Nat) (d : α) (hk : i ≤ k ∧ k < i + 8) :
    (splice8 a i v0 v1 v2 v3 v4 v5 v6 v7).getD k d =
      #[v0, v1, v2, v3, v4, v5, v6, v7].getD (k - i) d := by
  obtain ⟨o, ho, rfl⟩ : ∃ o, o < 8 ∧ k = i + o := ⟨k - i, by omega, by omega⟩
  unfold splice8
  interval_cases o <;>
    simp (disch := (first | omega | (simp only [Array.size_setIfInBounds]; omega))) only
      [getD_setIfInBounds, Nat.add_sub_cancel_left, Nat.add_zero, Nat.add_left_cancel_iff,
        Nat.reduceEqDiff, Nat.left_eq_add, Nat.succ_ne_zero, Nat.sub_self, ↓reduceIte,
        getD_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]

/-- Outside its range, `splice8` keeps the entries. -/
theorem getD_splice8_out (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α) (k : Nat) (d : α)
    (hk : k < i ∨ i + 8 ≤ k) :
    (splice8 a i v0 v1 v2 v3 v4 v5 v6 v7).getD k d = a.getD k d := by
  simp only [splice8, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  repeat rw [ite_eq_right (by omega)]

/-- An eight-entry literal has eight entries. -/
@[simp] theorem size_literal8 (v0 v1 v2 v3 v4 v5 v6 v7 : α) :
    (#[v0, v1, v2, v3, v4, v5, v6, v7]).size = 8 := rfl

/-- In bounds, `splice8` is the splice of its eight values. -/
theorem splice8_eq_splice (a : Array α) (i : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : α)
    (h : i + 8 ≤ a.size) :
    splice8 a i v0 v1 v2 v3 v4 v5 v6 v7 = splice a i #[v0, v1, v2, v3, v4, v5, v6, v7] := by
  apply array_eq_of_getD _ _ v0 (by rw [size_splice8, size_splice _ _ _ h])
  intro k
  rw [getD_splice _ _ _ h, size_literal8]
  by_cases hk : i ≤ k ∧ k < i + 8
  · rw [getD_splice8_in _ _ _ _ _ _ _ _ _ _ h _ _ hk, ite_eq_right (by omega),
      ite_eq_left hk.2]
  · rw [getD_splice8_out _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    split_ifs <;> first | rfl | omega

namespace Expressions

/-- The first of the four final DIF layers on the sixteen-coordinate block at `base`, as the stage
kernel computes it. -/
def leafStage8Field [Zero R] [Add R] [Sub R] [Mul R] (t : Array R) (base : Nat) (b : Array R) :
    Array R :=
  leafStage8_fields%

/-- The second of the four final DIF layers on the block at `base`. -/
def leafStage4Field [Zero R] [Add R] [Sub R] [Mul R] (t : Array R) (base : Nat) (b : Array R) :
    Array R :=
  leafStage4_fields%

/-- The third of the four final DIF layers on the block at `base`. -/
def leafStage2Field [Zero R] [Add R] [Sub R] [Mul R] (t : Array R) (base : Nat) (b : Array R) :
    Array R :=
  leafStage2_fields%

/-- The last DIF layer on the block at `base`. -/
def leafStage1Field [Zero R] [Add R] [Sub R] (base : Nat) (b : Array R) : Array R :=
  leafStage1_fields%

@[simp] theorem size_leafStage8Field [Zero R] [Add R] [Sub R] [Mul R] (t b : Array R)
    (base : Nat) : (leafStage8Field t base b).size = b.size := by
  simp only [leafStage8Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The first stage's model is the first of the four final layers. -/
theorem leafStage8Field_eq [Field R] (t b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage8Field t base b = layer16_8 t b base := by
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage8Field, size_layer16_8])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_layer16_8 t b base hs o ho]
    unfold leafStage8Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only [getD_splice8_in,
        getD_splice8_out, fieldAdd, fieldSub, fieldMul, getD_toArray, Nat.add_assoc,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT,
        Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.reduceSub, Nat.sub_self, Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_layer16_8_outside t b base hs k hk]
    unfold leafStage8Field
    simp (disch := omega) only [getD_splice8_out]

@[simp] theorem size_leafStage4Field [Zero R] [Add R] [Sub R] [Mul R] (t b : Array R)
    (base : Nat) : (leafStage4Field t base b).size = b.size := by
  simp only [leafStage4Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The second stage's model is the second of the four final layers. -/
theorem leafStage4Field_eq [Field R] (t b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage4Field t base b = layer16_4 t b base := by
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage4Field, size_layer16_4])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_layer16_4 t b base hs o ho]
    unfold leafStage4Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only [getD_splice8_in,
        getD_splice8_out, fieldAdd, fieldSub, fieldMul, getD_toArray, Nat.add_assoc,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT,
        Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.reduceSub, Nat.sub_self, Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_layer16_4_outside t b base hs k hk]
    unfold leafStage4Field
    simp (disch := omega) only [getD_splice8_out]

@[simp] theorem size_leafStage2Field [Zero R] [Add R] [Sub R] [Mul R] (t b : Array R)
    (base : Nat) : (leafStage2Field t base b).size = b.size := by
  simp only [leafStage2Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The third stage's model is the third of the four final layers. -/
theorem leafStage2Field_eq [Field R] (t b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage2Field t base b = layer16_2 t b base := by
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage2Field, size_layer16_2])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_layer16_2 t b base hs o ho]
    unfold leafStage2Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only [getD_splice8_in,
        getD_splice8_out, fieldAdd, fieldSub, fieldMul, getD_toArray, Nat.add_assoc,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT,
        Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.reduceSub, Nat.sub_self, Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_layer16_2_outside t b base hs k hk]
    unfold leafStage2Field
    simp (disch := omega) only [getD_splice8_out]

@[simp] theorem size_leafStage1Field [Zero R] [Add R] [Sub R] (b : Array R)
    (base : Nat) : (leafStage1Field base b).size = b.size := by
  simp only [leafStage1Field, size_splice8]

set_option maxHeartbeats 1000000 in
/-- The last stage's model is the last of the four final layers. -/
theorem leafStage1Field_eq [Field R] (b : Array R) (base : Nat) (hs : base + 16 ≤ b.size) :
    leafStage1Field base b = layer16_1 #[1] b base := by
  apply array_eq_of_getD _ _ (0 : R) (by rw [size_leafStage1Field, size_layer16_1])
  intro k
  by_cases hk : base ≤ k ∧ k < base + 16
  · obtain ⟨o, ho, rfl⟩ : ∃ o, o < 16 ∧ k = base + o := ⟨k - base, by omega, by omega⟩
    rw [getD_layer16_1 #[1] b base hs o ho]
    unfold leafStage1Field layer16Value
    interval_cases o <;>
      simp (disch := (first | omega | (simp only [size_splice8]; omega))) only [getD_splice8_in,
        getD_splice8_out, fieldAdd, fieldSub, getD_toArray, one_mul, Nat.add_assoc,
        Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT,
        Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.reduceSub, Nat.sub_self, Nat.add_zero,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ↓reduceIte]
  · rw [getD_layer16_1_outside #[1] b base hs k hk]
    unfold leafStage1Field
    simp (disch := omega) only [getD_splice8_out]

end Expressions

end CompPoly.CPolynomial.NTTFast.Packed
