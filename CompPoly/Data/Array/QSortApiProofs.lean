/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Batteries.Data.Array.Merge
import Batteries.Data.Array.Pairwise
import Init.Data.Array.Perm
import Init.Data.Array.QSort.Basic
import Init.Data.Vector.Perm

/-!
# `qsort` / Array-merge API proof probe

This module records the small public-theorem slice around Lean's `Array.qsort` and Batteries'
array-merge helpers that is straightforward to prove against Lean `v4.28.0`.

It also records the current blockers for a richer upstream API, based on a local proof probe and
Lean's historical `qsort_grind` verification draft:

- `Array.qpartition.eq_def` and `Array.qsort.eq_def` are public, but the recursive helpers are not
  source-accessible in this release in the ergonomic form used by the draft proof.
- The draft verification proves `qpartition_loop_perm`, `qpartition_perm`, `qsort_sort_perm`, and
  `qsort_perm` via induction over those recursive helpers.
- The same draft also uses small permutation-support lemmas such as
  `List.Perm.take_of_getElem`, `List.Perm.drop_of_getElem`, `Array.Perm.extract'`, and
  `Vector.Perm.extract'`.

So the likely clean upstream path is:
1. expose or otherwise support induction over the recursive `qpartition` / `qsort` helpers
2. upstream the small `Perm.extract`-style API used by the verification draft
3. then port the draft proof file into a library-facing theorem module

Reference draft:
`https://raw.githubusercontent.com/leanprover/lean4/qsort_grind/tests/lean/run/grind_qsort.lean`
-/

namespace Array

@[simp] theorem qsort_nil (lt : α → α → Bool := by exact (· < ·)) :
    qsort (#[] : Array α) lt = #[] := by
  simp [qsort]

@[simp] theorem qsortOrd_nil [Ord α] : qsortOrd (#[] : Array α) = #[] := by
  simpa [qsortOrd] using qsort_nil (α := α) (lt := fun x y => compare x y |>.isLT)

theorem size_qsort (as : Array α) (lt : α → α → Bool := by exact (· < ·)) :
    (qsort as lt).size = as.size := by
  by_cases h : as.size = 0
  · simp [qsort, h]
  · simp [qsort, h]

theorem size_qsortOrd [Ord α] (as : Array α) :
    (qsortOrd as).size = as.size := by
  simpa [qsortOrd] using size_qsort (as := as) (lt := fun x y => compare x y |>.isLT)

@[simp] theorem mergeAdjacentDups_empty [BEq α] (f : α → α → α) :
    mergeAdjacentDups f (#[] : Array α) = #[] := by
  simp [mergeAdjacentDups]

@[simp] theorem dedupSorted_empty [BEq α] :
    dedupSorted (#[] : Array α) = #[] := by
  simp [dedupSorted]

end Array
