/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Data.ByteArray.Packed
public import Mathlib.Tactic.IntervalCases

/-! # Sixteen-word rows

The packed loops append sixteen words at a time. Their results are stated as `rows`, a
concatenation of sixteen-entry literals with a single indexing lemma.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- Sixteen values of a function as an array literal. -/
def lit16 (g : Nat → α) : Array α :=
  #[g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10, g 11, g 12, g 13, g 14, g 15]

@[simp] theorem size_lit16 (g : Nat → α) : (lit16 g).size = 16 := rfl

theorem getD_lit16 (g : Nat → α) (c : Nat) (hc : c < 16) (d : α) :
    (lit16 g).getD c d = g c := by
  interval_cases c <;> rfl

/-- Concatenated sixteen-entry rows; row `j` holds `g j 0, …, g j 15`. -/
def rows (g : Nat → Nat → α) : Nat → Array α
  | 0 => #[]
  | k + 1 => rows g k ++ lit16 (g k)

@[simp] theorem size_rows (g : Nat → Nat → α) (k : Nat) : (rows g k).size = 16 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rows, Array.size_append, ih, size_lit16]
    omega

theorem getD_append_eq (a b : Array α) (i : Nat) (d : α) :
    (a ++ b).getD i d = if i < a.size then a.getD i d else b.getD (i - a.size) d := by
  simp only [Array.getD_eq_getD_getElem?]
  split
  · rw [Array.getElem?_append_left ‹_›]
  · rw [Array.getElem?_append_right (by omega)]

theorem getD_rows (g : Nat → Nat → α) (k i : Nat) (hi : i < 16 * k) (d : α) :
    (rows g k).getD i d = g (i / 16) (i % 16) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [rows]
    rw [getD_append_eq, size_rows]
    split
    · exact ih ‹_›
    · rw [getD_lit16 _ _ (by omega)]
      have h1 : i / 16 = k := by omega
      have h2 : i % 16 = i - 16 * k := by omega
      rw [h1, h2]

theorem rows_add (g : Nat → Nat → α) (a b : Nat) :
    rows g (a + b) = rows g a ++ rows (fun j ↦ g (a + j)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, rows, Array.append_empty]
  | succ b ih =>
    rw [← Nat.add_assoc, rows, ih, rows, Array.append_assoc]

theorem rows_congr (g g' : Nat → Nat → α) (k : Nat) (h : ∀ j c, c < 16 → g j c = g' j c) :
    rows g k = rows g' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rows, ih, lit16]
    rw [h k 0 (by decide), h k 1 (by decide), h k 2 (by decide), h k 3 (by decide),
      h k 4 (by decide), h k 5 (by decide), h k 6 (by decide), h k 7 (by decide),
      h k 8 (by decide), h k 9 (by decide), h k 10 (by decide), h k 11 (by decide),
      h k 12 (by decide), h k 13 (by decide), h k 14 (by decide), h k 15 (by decide)]

theorem getD_map_range (F : Nat → α) (n k : Nat) (hk : k < n) (d : α) :
    ((Array.range n).map F).getD k d = F k := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hk,
    ↓reduceIte, Option.map_some, Option.getD_some]

/-- Pack an empty array, whatever capacity was reserved. -/
theorem Native.emptyWithCapacity_eq_encodeWords (k : Nat) :
    ByteArray.emptyWithCapacity k = encode (#[] : Array UInt32) := rfl

end CompPoly.CPolynomial.NTTFast.Packed
