/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.BatchEval.SubproductTree
import CompPoly.Univariate.ToPoly.Impl

/-!
# Batch Evaluation Correctness

Correctness theorems for univariate batch-evaluation implementations.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

private theorem eval_linearFactor [Field R] [BEq R] [LawfulBEq R] (x : R) :
    (linearFactor x).eval x = 0 := by
  rw [eval_toPoly]
  simp [linearFactor, toPoly_sub, X_toPoly, C_toPoly]

private theorem eval_modContext_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (D : ModContext R) (p q : CPolynomial R)
    {x : R} (hq : q.eval x = 0) :
    (D.modByMonic p q).eval x = p.eval x := by
  rw [D.modByMonic_eq_modByMonic]
  exact eval_modByMonic_eq_self_of_eval_eq_zero p q hq

namespace SubproductTree

private def points [Zero R] : SubproductTree R → List R
  | leaf x _ => [x]
  | node _ left right => points left ++ points right

private def pointsList [Zero R] : List (SubproductTree R) → List R
  | [] => []
  | tree :: trees => points tree ++ pointsList trees

private def Valid [Semiring R] : SubproductTree R → Prop
  | leaf x poly => ∀ y, y ∈ [x] → poly.eval y = 0
  | node poly left right =>
      (∀ x, x ∈ points left ++ points right → poly.eval x = 0) ∧ Valid left ∧ Valid right

private theorem valid_root [Semiring R] {tree : SubproductTree R} (h : Valid tree)
    {x : R} (hx : x ∈ points tree) :
    tree.poly.eval x = 0 := by
  cases tree with
  | leaf y poly =>
      exact h x (by simpa [points] using hx)
  | node poly left right =>
      exact h.1 x (by simpa [points] using hx)

private theorem valid_leafFor [Field R] [BEq R] [LawfulBEq R] (x : R) :
    Valid (leafFor x) := by
  intro y hy
  simp at hy
  subst y
  exact eval_linearFactor x

private theorem valid_combine [Field R] [BEq R] [LawfulBEq R] (M : MulContext R)
    (level : Nat)
    {left right : SubproductTree R} (hleft : Valid left) (hright : Valid right) :
    Valid (combine M level left right) := by
  constructor
  · intro x hx
    rw [M.mulAtLevel_eq_mul, eval_mul]
    rcases List.mem_append.mp hx with hx | hx
    · rw [valid_root hleft hx]
      simp
    · rw [valid_root hright hx]
      simp
  · exact ⟨hleft, hright⟩

private theorem valid_combinePairs [Field R] [BEq R] [LawfulBEq R] (M : MulContext R)
    (level : Nat) :
    ∀ {trees : List (SubproductTree R)}, List.Forall Valid trees →
      List.Forall Valid (combinePairs M level trees)
  | [], _ => by
      simp [combinePairs]
  | [_], h => by
      simpa [combinePairs] using h
  | left :: right :: rest, h => by
      simp [combinePairs] at h ⊢
      exact ⟨valid_combine M level h.1 h.2.1, valid_combinePairs M level h.2.2⟩

private theorem pointsList_combinePairs [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (level : Nat) :
    ∀ trees : List (SubproductTree R),
      pointsList (combinePairs M level trees) = pointsList trees
  | [] => rfl
  | [_] => rfl
  | left :: right :: rest => by
      simp [combinePairs, combine, pointsList, points, pointsList_combinePairs M level rest,
        List.append_assoc]

private theorem length_combinePairs_le [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (level : Nat) :
    ∀ trees : List (SubproductTree R), (combinePairs M level trees).length ≤ trees.length
  | [] => by
      simp [combinePairs]
  | [_] => by
      simp [combinePairs]
  | _ :: _ :: rest => by
      simpa [combinePairs] using
        Nat.succ_le_succ
          (Nat.le_trans (length_combinePairs_le M level rest) (Nat.le_succ rest.length))

private theorem length_combinePairs_pair_le [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (level : Nat) (left right : SubproductTree R)
    (rest : List (SubproductTree R)) :
    (combinePairs M level (left :: right :: rest)).length ≤ rest.length + 1 := by
  simpa [combinePairs] using Nat.succ_le_succ (length_combinePairs_le M level rest)

private theorem combinePairs_ne_nil_of_ne_nil [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (level : Nat) :
    ∀ {trees : List (SubproductTree R)}, trees ≠ [] → combinePairs M level trees ≠ []
  | [], h => by
      contradiction
  | [_], _ => by
      simp [combinePairs]
  | _ :: _ :: _, _ => by
      simp [combinePairs]

private theorem buildFromTrees_exists_of_length_le [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) :
    ∀ (level fuel : ℕ) (trees : List (SubproductTree R)), trees ≠ [] →
      trees.length ≤ fuel + 1 → ∃ tree, buildFromTrees M level fuel trees = some tree := by
  intro level fuel
  induction fuel generalizing level with
  | zero =>
      intro trees hne hlen
      cases trees with
      | nil => contradiction
      | cons tree rest =>
          cases rest with
          | nil => exact ⟨tree, rfl⟩
          | cons _ _ => simp at hlen
  | succ fuel ih =>
      intro trees hne hlen
      cases trees with
      | nil => contradiction
      | cons left rest =>
          cases rest with
          | nil => exact ⟨left, rfl⟩
          | cons right rest =>
              have hlen' : (combinePairs M level (left :: right :: rest)).length ≤ fuel + 1 := by
                have hpair := length_combinePairs_pair_le M level left right rest
                have hlen_rest : rest.length + 2 ≤ fuel + 2 := by
                  simpa using hlen
                omega
              have hne' : combinePairs M level (left :: right :: rest) ≠ [] :=
                combinePairs_ne_nil_of_ne_nil M level (by simp)
              simpa [buildFromTrees] using
                ih (level + 1) (combinePairs M level (left :: right :: rest)) hne' hlen'

private theorem buildList_exists_of_ne_nil [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) {xs : List R} (hxs : xs ≠ []) :
    ∃ tree, buildList M xs = some tree := by
  have hleaves : xs.map leafFor ≠ [] := by
    cases xs with
    | nil => contradiction
    | cons _ _ => simp
  simpa [buildList] using
    buildFromTrees_exists_of_length_le M 0 (xs.map leafFor).length (xs.map leafFor)
      hleaves (Nat.le_succ _)

private theorem valid_leafFor_list [Field R] [BEq R] [LawfulBEq R] :
    ∀ xs : List R, List.Forall Valid (xs.map leafFor)
  | [] => by
      simp
  | x :: xs => by
      simp [valid_leafFor x, valid_leafFor_list xs]

private theorem pointsList_map_leafFor [Field R] [BEq R] [LawfulBEq R] :
    ∀ xs : List R, pointsList (xs.map leafFor) = xs
  | [] => rfl
  | _ :: xs => by
      simp [pointsList, points, leafFor, pointsList_map_leafFor xs]

private theorem buildFromTrees_valid_points [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) :
    ∀ (level fuel : ℕ) (trees : List (SubproductTree R)) (tree : SubproductTree R),
      buildFromTrees M level fuel trees = some tree → List.Forall Valid trees →
        Valid tree ∧ points tree = pointsList trees := by
  intro level fuel
  induction fuel generalizing level with
  | zero =>
      intro trees tree hbuild hvalid
      cases trees with
      | nil => simp [buildFromTrees] at hbuild
      | cons head rest =>
          cases rest with
          | nil =>
              simp [buildFromTrees] at hbuild
              subst hbuild
              have hhead : Valid head := by
                simpa using hvalid
              exact ⟨hhead, by simp [pointsList]⟩
          | cons _ _ => simp [buildFromTrees] at hbuild
  | succ fuel ih =>
      intro trees tree hbuild hvalid
      cases trees with
      | nil => simp [buildFromTrees] at hbuild
      | cons head rest =>
          cases rest with
          | nil =>
              simp [buildFromTrees] at hbuild
              subst hbuild
              have hhead : Valid head := by
                simpa using hvalid
              exact ⟨hhead, by simp [pointsList]⟩
          | cons second rest =>
              have hnext :
                  Valid tree ∧ points tree =
                    pointsList (combinePairs M level (head :: second :: rest)) :=
                ih (level + 1) (combinePairs M level (head :: second :: rest)) tree
                  (by simpa [buildFromTrees] using hbuild)
                  (valid_combinePairs M level hvalid)
              exact ⟨hnext.1,
                hnext.2.trans (pointsList_combinePairs M level (head :: second :: rest))⟩

private theorem buildList_valid_points [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) {xs : List R} {tree : SubproductTree R}
    (hbuild : buildList M xs = some tree) :
    Valid tree ∧ points tree = xs := by
  have h :=
    buildFromTrees_valid_points M 0 (xs.map leafFor).length (xs.map leafFor) tree
      (by simpa [buildList] using hbuild) (valid_leafFor_list xs)
  exact ⟨h.1, h.2.trans (pointsList_map_leafFor xs)⟩

private theorem buildArray_valid_points [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) {xs : Array R} {tree : SubproductTree R}
    (hbuild : buildArray M xs = some tree) :
    Valid tree ∧ points tree = xs.toList := by
  exact buildList_valid_points M (by simpa [buildArray] using hbuild)

private theorem map_eval_modContext_eq_map_eval [Field R] [BEq R] [LawfulBEq R]
    (D : ModContext R) (p q : CPolynomial R) :
    ∀ xs : List R, (∀ x, x ∈ xs → q.eval x = 0) →
      xs.map (fun x => (D.modByMonic p q).eval x) = xs.map (fun x => p.eval x)
  | [], _ => by
      simp
  | x :: xs, hroot => by
      have hx : q.eval x = 0 := hroot x (by simp)
      have htail : ∀ y, y ∈ xs → q.eval y = 0 := by
        intro y hy
        exact hroot y (by simp [hy])
      simp [eval_modContext_eq_self_of_eval_eq_zero D p q hx,
        map_eval_modContext_eq_map_eval D p q xs htail]

private theorem evalList_eq_map_eval [Field R] [BEq R] [LawfulBEq R]
    (D : ModContext R) :
    ∀ (p : CPolynomial R) (tree : SubproductTree R), Valid tree →
      evalList D p tree = (points tree).map fun x => p.eval x
  | p, leaf x leafPoly, hvalid => by
      have hroot : leafPoly.eval x = 0 :=
        valid_root hvalid (by simp [points])
      have hmod := eval_modContext_eq_self_of_eval_eq_zero D p leafPoly hroot
      simp [evalList, points, eval_horner_eq_eval, hmod]
  | p, node _ left right, hvalid => by
      have hleft : Valid left := by
        simpa [Valid] using hvalid.2.1
      have hright : Valid right := by
        simpa [Valid] using hvalid.2.2
      calc
        evalList D p (node _ left right)
            = evalList D (D.modByMonic p left.poly) left ++
                evalList D (D.modByMonic p right.poly) right := by
              rfl
        _ = (points left).map (fun x => (D.modByMonic p left.poly).eval x) ++
              (points right).map (fun x => (D.modByMonic p right.poly).eval x) := by
              rw [evalList_eq_map_eval D (D.modByMonic p left.poly) left hleft,
                evalList_eq_map_eval D (D.modByMonic p right.poly) right hright]
        _ = (points left).map (fun x => p.eval x) ++
              (points right).map (fun x => p.eval x) := by
              rw [map_eval_modContext_eq_map_eval D p left.poly (points left)
                  (fun x hx => valid_root hleft hx),
                map_eval_modContext_eq_map_eval D p right.poly (points right)
                  (fun x hx => valid_root hright hx)]
        _ = (points (node _ left right)).map (fun x => p.eval x) := by
              simp [points, List.map_append]

end SubproductTree

/-- Batched Horner evaluation agrees with the direct batched evaluator. -/
theorem evalBatchHorner_eq_evalBatch [Semiring R] (p : CPolynomial R) (xs : Array R) :
    evalBatchHorner p xs = evalBatch p xs := by
  simp [evalBatchHorner, evalBatch, eval_horner_eq_eval]

/-- Subproduct-tree batch evaluation agrees with the direct batched evaluator. -/
theorem evalBatchSubproduct_eq_evalBatch [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (D : ModContext R) (p : CPolynomial R) (xs : Array R) :
    evalBatchSubproduct M D p xs = evalBatch p xs := by
  apply Array.toList_inj.mp
  unfold evalBatchSubproduct
  cases hbuild : SubproductTree.buildArray M xs with
  | none =>
      have hnil : xs.toList = [] := by
        by_contra hne
        obtain ⟨tree, htree⟩ := SubproductTree.buildList_exists_of_ne_nil M hne
        simp [SubproductTree.buildArray, htree] at hbuild
      simp [evalBatch, hnil]
  | some tree =>
      have htree := SubproductTree.buildArray_valid_points M hbuild
      have heval := SubproductTree.evalList_eq_map_eval D p tree htree.1
      simp [evalBatch, heval, htree.2]

end CPolynomial
end CompPoly
