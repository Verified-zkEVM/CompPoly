/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas

/-! # Coordinate semantics of disjoint DIF butterflies -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Coordinate formula for a consecutive range of independent DIF butterflies. -/
def difValue [Field R] (tw : Array R) (j i0 i1 count : Nat) (a : Array R) (k : Nat) : R :=
  if i0 ≤ k ∧ k < i0 + count then a.getD k 0 + a.getD (i1 + (k - i0)) 0 else
  if i1 ≤ k ∧ k < i1 + count then
    tw.getD (j + (k - i1)) 0 * (a.getD (i0 + (k - i1)) 0 - a.getD k 0)
  else a.getD k 0

private theorem difValue_step [Field R] (tw : Array R) (j i0 i1 count : Nat)
    (a : Array R) (hs : i1 + (count + 1) ≤ a.size)
    (hsep : i0 + (count + 1) ≤ i1) (k : Nat) :
    difValue tw (j + 1) (i0 + 1) (i1 + 1) count
      ((a.setIfInBounds i0 (a.getD i0 0 + a.getD i1 0)).setIfInBounds i1
        (tw.getD j 0 * (a.getD i0 0 - a.getD i1 0))) k =
      difValue tw j i0 i1 (count + 1) a k := by
  have hi0 : i0 < a.size := by omega
  have hi1 : i1 < a.size := by omega
  have hsz : i1 < (a.setIfInBounds i0 (a.getD i0 0 + a.getD i1 0)).size := by
    simpa only [Array.size_setIfInBounds] using hi1
  unfold difValue
  simp only [getD_setIfInBounds _ i1 _ _ _ hsz, getD_setIfInBounds a i0 _ _ _ hi0]
  by_cases hk0 : k = i0
  · subst k
    simp (disch := (simp only [Array.size_setIfInBounds] at *; omega)) only
      [Nat.sub_self, Nat.add_zero, ite_eq_left, ite_eq_right, ↓reduceIte]
  · by_cases hk1 : k = i1
    · subst k
      simp (disch := (simp only [Array.size_setIfInBounds] at *; omega)) only
        [Nat.sub_self, Nat.add_zero, ite_eq_left, ite_eq_right, ↓reduceIte]
    · by_cases hl : i0 ≤ k ∧ k < i0 + (count + 1)
      · have hks : i1 + 1 + (k - (i0 + 1)) = i1 + (k - i0) := by omega
        simp (disch := omega) only [hks, ite_eq_left, ite_eq_right]
      · by_cases hr : i1 ≤ k ∧ k < i1 + (count + 1)
        · have hks : i0 + 1 + (k - (i1 + 1)) = i0 + (k - i1) := by omega
          have hws : j + 1 + (k - (i1 + 1)) = j + (k - i1) := by omega
          simp (disch := omega) only [hks, hws, ite_eq_left, ite_eq_right]
        · simp (disch := omega) only [ite_eq_left, ite_eq_right]

/-- An ordinary DIF inner loop has the pointwise formula for disjoint butterfly pairs. -/
theorem getD_butterflyDIFInner [Field R] (tw : Array R) (limit j i0 i1 : Nat) (a : Array R)
    (hs : i1 + (limit - j) ≤ a.size) (hsep : i0 + (limit - j) ≤ i1) (k : Nat) :
    (Plan.butterflyDIFInner tw limit j i0 i1 a).getD k 0 =
      difValue tw j i0 i1 (limit - j) a k := by
  rw [Plan.butterflyDIFInner]
  split
  · rename_i hj
    have he : limit - j = (limit - (j + 1)) + 1 := by omega
    rw [getD_butterflyDIFInner tw limit (j + 1) (i0 + 1) (i1 + 1) _
      (by simp only [Array.size_set!]; omega) (by omega), he]
    exact difValue_step tw j i0 i1 (limit - (j + 1)) a (by omega) (by omega) k
  · have he : limit - j = 0 := by omega
    simp (disch := omega) only [he, difValue, Nat.add_zero, ite_eq_right]
termination_by limit - j
decreasing_by omega

/-- A completed lower-half butterfly coordinate is the sum of its original pair. -/
theorem getD_butterflyDIFInner_left [Field R] (tw : Array R) (limit j i0 i1 : Nat)
    (a : Array R) (hs : i1 + (limit - j) ≤ a.size)
    (hsep : i0 + (limit - j) ≤ i1) (k : Nat)
    (hk : i0 ≤ k ∧ k < i0 + (limit - j)) :
    (Plan.butterflyDIFInner tw limit j i0 i1 a).getD k 0 =
      a.getD k 0 + a.getD (i1 + (k - i0)) 0 := by
  rw [getD_butterflyDIFInner tw limit j i0 i1 a hs hsep]
  simp only [difValue, hk, and_self, ↓reduceIte]

/-- A completed upper-half coordinate is the twiddle-scaled difference of its pair. -/
theorem getD_butterflyDIFInner_right [Field R] (tw : Array R) (limit j i0 i1 : Nat)
    (a : Array R) (hs : i1 + (limit - j) ≤ a.size)
    (hsep : i0 + (limit - j) ≤ i1) (k : Nat)
    (hk : i1 ≤ k ∧ k < i1 + (limit - j)) :
    (Plan.butterflyDIFInner tw limit j i0 i1 a).getD k 0 =
      tw.getD (j + (k - i1)) 0 * (a.getD (i0 + (k - i1)) 0 - a.getD k 0) := by
  have hl : ¬(i0 ≤ k ∧ k < i0 + (limit - j)) := by omega
  rw [getD_butterflyDIFInner tw limit j i0 i1 a hs hsep]
  simp only [difValue, hk, hl, and_self, ↓reduceIte]

/-- All coordinates outside the completed pair ranges are unchanged. -/
theorem getD_butterflyDIFInner_outside [Field R] (tw : Array R) (limit j i0 i1 : Nat)
    (a : Array R) (hs : i1 + (limit - j) ≤ a.size)
    (hsep : i0 + (limit - j) ≤ i1) (k : Nat)
    (hk0 : ¬(i0 ≤ k ∧ k < i0 + (limit - j)))
    (hk1 : ¬(i1 ≤ k ∧ k < i1 + (limit - j))) :
    (Plan.butterflyDIFInner tw limit j i0 i1 a).getD k 0 = a.getD k 0 := by
  rw [getD_butterflyDIFInner tw limit j i0 i1 a hs hsep]
  simp only [difValue, hk0, hk1, ↓reduceIte]

end CompPoly.CPolynomial.NTTFast.Packed
