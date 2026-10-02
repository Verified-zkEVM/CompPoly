/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import Mathlib.Init
public import Init.Data.Range.Lemmas

/-! # Array permutations from index involutions

Swap each nontrivial pair once instead of allocating a second array for a gather.
-/

@[expose] public section
namespace Array
variable {α : Type*}

@[inline] private def involutionStep (f : Nat → Nat) (a : Array α) (i : Nat) : Array α :=
  if i < f i then a.swapIfInBounds i (f i) else a

@[simp] private theorem size_involutionStep (f : Nat → Nat) (a : Array α) (i : Nat) :
    (involutionStep f a i).size = a.size := by
  simp only [involutionStep]; split <;> simp only [Array.size_swapIfInBounds]

private theorem size_fold (f : Nat → Nat) (is : List Nat) (a : Array α) :
    (is.foldl (involutionStep f) a).size = a.size := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih =>
    simpa only [List.foldl_cons, size_involutionStep] using ih (involutionStep f a i)

private theorem getD_swap (a : Array α) (i j k : Nat) (d : α)
    (hi : i < a.size) (hj : j < a.size) (hk : k < a.size) :
    (a.swapIfInBounds i j).getD k d =
      if k = i then a.getD j d else if k = j then a.getD i d else a.getD k d := by
  simp only [Array.swapIfInBounds, hi, hj, ↓reduceDIte, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (show k < (a.swap i j hi hj).size by simpa using hk),
    Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj,
    Array.getElem?_eq_getElem hk, Option.getD_some, Array.getElem_swap]

private theorem prefix_invariant (f : Nat → Nat) (a : Array α) (d : α)
    (hb : ∀ i < a.size, f i < a.size)
    (hf : ∀ i < a.size, f (f i) = i) (k : Nat) (hk : k ≤ a.size) :
    ∀ j < a.size, ((List.range k).foldl (involutionStep f) a).getD j d =
      if min j (f j) < k then a.getD (f j) d else a.getD j d := by
  induction k with
  | zero => intro j hj; simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ↓reduceIte]
  | succ k ih =>
    have hk' : k < a.size := by omega
    have ih := ih (by omega)
    intro j hj
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hswap : k < f k
    · simp only [involutionStep, hswap, ↓reduceIte]
      rw [getD_swap _ _ _ _ _ (by simpa only [size_fold] using hk')
        (by simpa only [size_fold] using hb k hk') (by simpa only [size_fold] using hj)]
      by_cases hji : j = k
      · subst j
        rw [ite_eq_left rfl, ih (f k) (hb k hk'), hf k hk']
        have hmin1 : ¬ min (f k) k < k := by omega
        have hmin2 : min k (f k) < k + 1 := by omega
        simp only [hmin1, hmin2, ↓reduceIte]
      · rw [ite_eq_right hji]
        by_cases hjf : j = f k
        · subst j
          rw [ite_eq_left rfl, ih k hk', hf k hk']
          have hmin1 : ¬ min k (f k) < k := by omega
          have hmin2 : min (f k) k < k + 1 := by omega
          simp only [hmin1, hmin2, ↓reduceIte]
        · rw [ite_eq_right hjf, ih j hj]
          have hfj : f j ≠ k := by
            intro he
            have hh := hf j hj
            simp only [he] at hh
            exact hjf hh.symm
          have he : (min j (f j) < k) = (min j (f j) < k + 1) := by
            apply propext; omega
          simp only [he]
    · simp only [involutionStep, hswap, ↓reduceIte]
      rw [ih j hj]
      by_cases hfix : f j = j
      · simp only [hfix, ite_self]
      · have hmin : min j (f j) ≠ k := by
          by_cases hji : j = k
          · subst j; omega
          · by_cases hfj : f j = k
            · have hh := hf j hj
              rw [hfj] at hh
              omega
            · omega
        have he : (min j (f j) < k) = (min j (f j) < k + 1) := by
          apply propext; omega
        simp only [he]

/-- Apply an index involution by swapping each pair once, reusing a uniquely owned array. -/
@[inline] def permuteInvolution (order : Array Nat) (a : Array α) : Array α := Id.run do
  let mut out := a
  for i in [:order.size] do
    let j := order[i]!
    if i < j then out := out.swapIfInBounds i j
  return out

private theorem permuteInvolution_eq_fold (order : Array Nat) (a : Array α) :
    permuteInvolution order a =
      (List.range order.size).foldl (involutionStep (fun i ↦ order[i]!)) a := by
  simp [permuteInvolution, ← apply_ite, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, List.range_eq_range']
  rfl

/-- Swapping entries preserves the array length, including for invalid index tables. -/
@[simp] theorem size_permuteInvolution (order : Array Nat) (a : Array α) :
    (permuteInvolution order a).size = a.size := by
  rw [permuteInvolution_eq_fold, size_fold]

/-- A bounded involutive index table gives the same result as gathering a fresh array. -/
theorem permuteInvolution_eq_map (order : Array Nat) (a : Array α) (d : α)
    (hs : order.size = a.size)
    (hb : ∀ i < order.size, order[i]! < order.size)
    (hf : ∀ i < order.size, order[order[i]!]! = i) :
    permuteInvolution order a = order.map (fun i ↦ a.getD i d) := by
  apply Array.ext
  · rw [size_permuteInvolution, Array.size_map, hs]
  · intro j hj hk
    have hja : j < a.size := by simpa only [size_permuteInvolution] using hj
    have hjo : j < order.size := by omega
    have hfb : ∀ i < a.size, order[i]! < a.size := by simpa only [hs] using hb
    have hff : ∀ i < a.size, order[order[i]!]! = i := by simpa only [hs] using hf
    have hm := prefix_invariant (fun i ↦ order[i]!) a d hfb hff a.size (Nat.le_refl _) j hja
    have hmin : min j order[j]! < a.size := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hja
    simp only [hmin, ↓reduceIte] at hm
    have he : (permuteInvolution order a).getD j d = a.getD order[j]! d := by
      rw [permuteInvolution_eq_fold, hs]
      exact hm
    simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj,
      Option.getD_some, getElem!_pos order j hjo, Array.getElem_map] using he

end Array
