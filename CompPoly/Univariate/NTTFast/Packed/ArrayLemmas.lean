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
