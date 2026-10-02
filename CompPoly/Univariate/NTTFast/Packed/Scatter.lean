/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
public import CompPoly.Univariate.NTTFast.Packed.Folds
public import CompPoly.Univariate.NTTFast.Permutation
import Mathlib.Tactic.IntervalCases

/-! # Complete four-coordinate scatter into a natural-order output array -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Copy one four-coordinate group from its final target values into the working output. -/
def scatterTile [Zero α] (target : Array α) (group : Nat) (out : Array α) : Array α :=
  storeList out (4 * group) [target.getD (4 * group) 0, target.getD (4 * group + 1) 0,
    target.getD (4 * group + 2) 0, target.getD (4 * group + 3) 0]

/-- A tile scatter preserves the working output's size. -/
@[simp] theorem size_scatterTile [Zero α] (target : Array α) (group : Nat) (out : Array α) :
    (scatterTile target group out).size = out.size := size_storeList ..

/-- A tile scatter writes exactly the target's coordinates in that four-coordinate group. -/
theorem getD_scatterTile [Zero α] (target : Array α) (group : Nat) (out : Array α)
    (hs : 4 * group + 4 ≤ out.size) (k : Nat) :
    (scatterTile target group out).getD k 0 =
      if k / 4 = group then target.getD k 0 else out.getD k 0 := by
  unfold scatterTile
  rw [getD_storeList _ _ _ _ (by exact hs)]
  by_cases hk : k / 4 = group
  · have hlo : ¬k < 4 * group := by omega
    have hhi : k < 4 * group + 4 := by omega
    simp only [hk, ite_true, hlo, ite_false, show
      [target.getD (4 * group) 0, target.getD (4 * group + 1) 0,
        target.getD (4 * group + 2) 0, target.getD (4 * group + 3) 0].length = 4 by rfl]
    rw [ite_eq_left hhi]
    obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 4 ∧ k = 4 * group + offset :=
      ⟨k - 4 * group, by omega, by omega⟩
    subst k
    interval_cases offset <;>
      simp only [Nat.add_sub_cancel_left, Nat.add_zero, Nat.sub_self, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some]
  · have hl : k < 4 * group ∨ 4 * group + 4 ≤ k := by omega
    simp only [hk, ite_false]
    rcases hl with hl | hl
    · rw [ite_eq_left hl]
    · rw [ite_eq_right (by omega), ite_eq_right (by change ¬k < 4 * group + 4; omega)]

/-- A scatter traversal gives the target values exactly in the groups it has visited. -/
theorem getD_fold_scatterTile [Zero α] (target out : Array α) (groups : List Nat)
    (hs : ∀ group ∈ groups, 4 * group + 4 ≤ out.size) (k : Nat) :
    (groups.foldl (fun out group ↦ scatterTile target group out) out).getD k 0 =
      if k / 4 ∈ groups then target.getD k 0 else out.getD k 0 := by
  induction groups generalizing out with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, ite_false]
  | cons group groups ih =>
    rw [List.foldl_cons, ih _ (by
      intro i hi
      simpa only [size_scatterTile] using hs i (List.mem_cons_of_mem group hi)),
      getD_scatterTile _ _ _ (hs group (List.mem_cons_self ..))]
    by_cases ht : k / 4 ∈ groups
    · simp only [List.mem_cons, ht, or_true, ite_true]
    · by_cases he : k / 4 = group
      · simp only [List.mem_cons, he, true_or, ite_true, ite_self]
      · simp only [List.mem_cons, ht, he, or_false, ite_false]

/-- Bit reversal visits every four-coordinate output group, so the complete scatter is the
  target. -/
theorem fold_scatterTile_bitRev [Zero α] (target out : Array α) (bits : Nat)
    (ht : target.size = 4 * 2 ^ bits) (ho : out.size = target.size) :
    (List.range (2 ^ bits)).foldl (fun out tile ↦
      scatterTile target (NTT.Transform.bitRevNat bits tile) out) out = target := by
  rw [← List.foldl_map (f := NTT.Transform.bitRevNat bits)
    (g := fun out group ↦ scatterTile target group out)]
  apply Array.ext
  · exact (foldl_invariant ((List.range (2 ^ bits)).map (NTT.Transform.bitRevNat bits))
      (fun a : Array α ↦ a.size = target.size) _
      (fun i hi a ha ↦ by simpa only [size_scatterTile] using ha) out ho)
  · intro k hk hj
    have hkt : k < 4 * 2 ^ bits := by simpa only [ht] using hj
    have hkg : k / 4 < 2 ^ bits := by omega
    have hm : k / 4 ∈ (List.range (2 ^ bits)).map (NTT.Transform.bitRevNat bits) := by
      apply List.mem_map.mpr
      exact ⟨NTT.Transform.bitRevNat bits (k / 4),
        List.mem_range.mpr (NTT.Transform.bitRevNat_lt _ _),
        NTT.Transform.bitRevNat_involutive bits (k / 4) hkg⟩
    have hg : ∀ group ∈ (List.range (2 ^ bits)).map (NTT.Transform.bitRevNat bits),
        4 * group + 4 ≤ out.size := by
      intro group hgroup
      obtain ⟨tile, htile, he⟩ := List.mem_map.mp hgroup
      have hb := NTT.Transform.bitRevNat_lt bits tile
      rw [← he, ho, ht]
      omega
    have h := getD_fold_scatterTile target out _ hg k
    rw [ite_eq_left hm] at h
    simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
      Array.getElem?_eq_getElem hj, Option.getD_some] using h

end CompPoly.CPolynomial.NTTFast.Packed
