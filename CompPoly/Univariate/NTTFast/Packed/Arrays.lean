/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Natural

/-! # Array slices used in packed-kernel refinements -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Replace consecutive entries by a complete array segment. -/
def splice (a : Array α) (index : Nat) (values : Array α) : Array α :=
  a.extract 0 index ++ values ++ a.extract (index + values.size) a.size

/-- An in-bounds splice preserves the array size. -/
@[simp] theorem size_splice (a : Array α) (i : Nat) (values : Array α)
    (h : i + values.size ≤ a.size) : (splice a i values).size = a.size := by
  have hi : i ≤ a.size := by omega
  simp only [splice, Array.size_append, Array.size_extract, Nat.min_self,
    Nat.min_eq_left hi, Nat.sub_zero]
  omega

/-- Every in-bounds sixteen-entry batch preserves the working array's size. -/
@[simp] theorem size_splice16 (a : Array α) (i : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) (hi : i + 16 ≤ a.size) :
    (splice a i #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]).size =
      a.size := by
  apply size_splice
  change i + 16 ≤ a.size
  exact hi

/-- Dropping a prefix of a tail drops the combined prefix. -/
theorem extract_extract_tail (Z : Array α) (a b : Nat) :
    (Z.extract a Z.size).extract b (Z.extract a Z.size).size = Z.extract (a + b) Z.size := by
  rw [Array.extract_extract, Array.size_extract]
  congr 1
  omega

/-- Splicing a batch at the end of a written prefix moves it into the prefix. -/
theorem splice_cursor (l Z V : Array α) (hZ : V.size ≤ Z.size) :
    splice (l ++ Z) l.size V = l ++ V ++ Z.extract V.size Z.size := by
  simp only [splice, Array.size_append]
  rw [Array.extract_append, Array.extract_append]
  simp only [Nat.sub_self, Array.extract_size, Array.extract_zero, Array.append_empty]
  rw [Array.extract_eq_empty_of_le (by omega), Array.empty_append,
    show l.size + V.size - l.size = V.size by omega,
    show l.size + Z.size - l.size = Z.size by omega]

private theorem getD_append (a b : Array α) (i : Nat) (d : α) :
    (a ++ b).getD i d = if i < a.size then a.getD i d else b.getD (i - a.size) d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

private theorem getD_extract (a : Array α) (first last i : Nat) (d : α) :
    (a.extract first last).getD i d =
      if i < min last a.size - first then a.getD (first + i) d else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split <;> rfl

/-- A splice changes exactly the entries in its range. -/
theorem getD_splice (a : Array α) (i : Nat) (values : Array α)
    (h : i + values.size ≤ a.size) (k : Nat) (d : α) :
    (splice a i values).getD k d =
      if k < i then a.getD k d else
      if k < i + values.size then values.getD (k - i) d else a.getD k d := by
  have hi : i ≤ a.size := by omega
  have hp : (a.extract 0 i).size = i := by
    simp only [Array.size_extract, Nat.min_eq_left hi, Nat.sub_zero]
  simp only [splice, getD_append, Array.size_append, hp, getD_extract,
    Nat.min_eq_left hi, Nat.min_self, Nat.sub_zero, Nat.zero_add]
  by_cases hki : k < i
  · have hkiv : k < i + values.size := by omega
    simp only [hki, hkiv, ↓reduceIte]
  · by_cases hkv : k < i + values.size
    · simp only [hki, hkv, ↓reduceIte]
    · have hsum : i + values.size + (k - (i + values.size)) = k := by omega
      by_cases hka : k < a.size
      · have ht : k - (i + values.size) < a.size - (i + values.size) := by omega
        simp only [hki, hkv, ht, hsum, ↓reduceIte]
      · have ht : ¬k - (i + values.size) < a.size - (i + values.size) := by omega
        simp only [hki, hkv, ht, ↓reduceIte, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (Nat.le_of_not_lt hka), Option.getD_none]

/-- A single-entry splice is the usual bounded array update. -/
theorem splice_singleton (a : Array α) (i : Nat) (x : α) (hi : i < a.size) :
    splice a i #[x] = a.setIfInBounds i x := by
  have h : i + (#[x]).size ≤ a.size := by change i + 1 ≤ a.size; omega
  apply Array.ext
  · simp only [size_splice a i #[x] h, Array.size_setIfInBounds]
  · intro k hk hj
    have hs : k < a.size := by simpa only [size_splice a i #[x] h] using hk
    have he := getD_splice a i #[x] h k x
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some] at he
    rw [he]
    simp only [Array.getElem_setIfInBounds hs,
      Array.getElem?_eq_getElem hs, Option.getD_some]
    by_cases hki : k < i
    · have hne : i ≠ k := by omega
      simp only [hki, hne, ↓reduceIte]
    · by_cases hke : k = i
      · subst k
        simp only [Nat.lt_irrefl, Array.size_singleton, Nat.lt_succ_self, ↓reduceIte, Nat.sub_self]
        rfl
      · have hk1 : ¬k < i + (#[x]).size := by change ¬k < i + 1; omega
        have hne : i ≠ k := Ne.symm hke
        simp only [hki, hk1, hne, ↓reduceIte]

end CompPoly.CPolynomial.NTTFast.Packed
