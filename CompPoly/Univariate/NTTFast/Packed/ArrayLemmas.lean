/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Arrays

/-! # Pointwise equations for packed-kernel array models -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Reading an in-bounds tabulated coordinate returns its defining value. -/
theorem getD_ofFn_bounded (f : Fin n → α) (i : Nat) (hi : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi,
    ↓reduceDIte, Option.getD_some]

/-- A bounded update changes one coordinate, including when the queried coordinate is absent. -/
theorem getD_setIfInBounds (a : Array α) (i k : Nat) (x d : α) (hi : i < a.size) :
    (a.setIfInBounds i x).getD k d = if k = i then x else a.getD k d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : k = i
  · subst k
    simp only [hi, ↓reduceIte, Option.getD_some]
  · have hn : i ≠ k := Ne.symm h
    simp only [h, hn, ↓reduceIte]

/-- Reading within an extracted segment reads the corresponding original coordinate. -/
theorem getD_extract (a : Array α) (first count k : Nat) (d : α)
    (hs : first + count ≤ a.size) (hk : k < count) :
    (a.extract first (first + count)).getD k d = a.getD (first + k) d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract,
    Nat.min_eq_left hs, Nat.add_sub_cancel_left, hk, ↓reduceIte]

/-- Sequential stores for one complete array segment. -/
def storeList (a : Array α) (index : Nat) : List α → Array α
  | [] => a
  | x :: xs => storeList (a.setIfInBounds index x) (index + 1) xs

/-- Sequential segment stores preserve array length. -/
@[simp] theorem size_storeList (a : Array α) (i : Nat) (xs : List α) :
    (storeList a i xs).size = a.size := by
  induction xs generalizing a i with
  | nil => rfl
  | cons x xs ih => simp only [storeList, ih, Array.size_setIfInBounds]

/-- Sequential segment stores have exactly the same coordinate semantics as a splice. -/
theorem getD_storeList (a : Array α) (i : Nat) (xs : List α) (d : α)
    (hs : i + xs.length ≤ a.size) (k : Nat) :
    (storeList a i xs).getD k d =
      if k < i then a.getD k d else
      if k < i + xs.length then xs[k - i]?.getD d else a.getD k d := by
  induction xs generalizing a i with
  | nil => simp only [storeList, List.length_nil, Nat.add_zero, List.getElem?_nil,
      Option.getD_none]; split <;> rfl
  | cons x xs ih =>
    have hi : i < a.size := by simp only [List.length_cons] at hs; omega
    have ht : i + 1 + xs.length ≤ (a.setIfInBounds i x).size := by
      simp only [Array.size_setIfInBounds, List.length_cons] at *; omega
    rw [storeList, ih _ _ ht]
    simp only [getD_setIfInBounds a i k x d hi, List.length_cons]
    by_cases hki : k < i
    · have hk : k < i + 1 := by omega
      have hn : k ≠ i := by omega
      simp only [hki, hk, hn, ↓reduceIte]
    · by_cases hke : k = i
      · subst k
        simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte, Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
        rw [ite_eq_left (by omega)]
      · have hk : ¬k < i + 1 := by omega
        have he : k - i = (k - (i + 1)) + 1 := by omega
        have hb : k < i + 1 + xs.length ↔ k < i + (xs.length + 1) := by omega
        simp only [hki, hk, hke, hb, he, List.getElem?_cons_succ, ↓reduceIte]

/-- A complete batch splice equals ordinary coordinate stores in index order. -/
theorem splice_eq_storeList (a : Array α) (i : Nat) (values : Array α)
    (hs : i + values.size ≤ a.size) :
    splice a i values = storeList a i values.toList := by
  apply Array.ext
  · simp only [size_splice a i values hs, size_storeList]
  · intro k hk hj
    have hsize : k < a.size := by simpa only [size_splice a i values hs] using hk
    have hd := getD_splice a i values hs k a[k]
    have hs' : i + values.toList.length ≤ a.size := by simpa only [Array.length_toList] using hs
    have hl := getD_storeList a i values.toList a[k] hs' k
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
      Array.getElem?_eq_getElem hj, Option.getD_some, Array.length_toList,
      ← Array.getElem?_toList] at hd hl
    exact hd.trans hl.symm

/-- Equal-length arrays are equal when all coordinates with the same default agree. -/
theorem array_eq_of_getD (a b : Array α) (d : α) (hs : a.size = b.size)
    (h : ∀ k, a.getD k d = b.getD k d) : a = b := by
  apply Array.ext hs
  intro k hk hj
  have he := h k
  simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
    Array.getElem?_eq_getElem hj, Option.getD_some] using he

/-- Reading a literal list-backed array uses ordinary list indexing. -/
theorem getD_toArray (xs : List α) (k : Nat) (d : α) :
    xs.toArray.getD k d = xs[k]?.getD d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]

/-- A sixteen-entry literal has sixteen coordinates, independently of its values. -/
@[simp] theorem size_literal16 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    (#[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]).size = 16 := rfl

end CompPoly.CPolynomial.NTTFast.Packed
