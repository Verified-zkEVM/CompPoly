/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.BatchEval.SubproductTree

/-!
# Vanishing Polynomials for Array Nodes

Reusable executable construction of `∏ x in xs, (X - x)`.
-/

namespace CompPoly

namespace CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Direct folded vanishing polynomial `∏ x in xs, (X - x)`. -/
def vanishingPolynomialArray (xs : Array F) : CPolynomial F :=
  xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) 1

private def subproductTreeListProduct (trees : List (CPolynomial.SubproductTree F)) :
    CPolynomial F :=
  trees.foldl (fun acc tree ↦ acc * CPolynomial.SubproductTree.poly tree) 1

private theorem subproductTreeFold_combinePairs
    (M : CPolynomial.MulContext F) :
    ∀ (trees : List (CPolynomial.SubproductTree F)) (acc : CPolynomial F),
      (CPolynomial.SubproductTree.combinePairs M trees).foldl
          (fun acc tree ↦ acc * CPolynomial.SubproductTree.poly tree) acc =
        trees.foldl (fun acc tree ↦ acc * CPolynomial.SubproductTree.poly tree) acc
  | [], _ => by
      rfl
  | [_], _ => by
      rfl
  | left :: right :: rest, acc => by
      simp [CPolynomial.SubproductTree.combinePairs, CPolynomial.SubproductTree.combine,
        M.mul_eq_mul]
      change (CPolynomial.SubproductTree.combinePairs M rest).foldl
          (fun acc tree ↦ acc * CPolynomial.SubproductTree.poly tree)
          (acc * (left.poly * right.poly)) =
        rest.foldl
          (fun acc tree ↦ acc * CPolynomial.SubproductTree.poly tree)
          ((acc * left.poly) * right.poly)
      rw [← CPolynomial.mul_assoc]
      exact subproductTreeFold_combinePairs M rest ((acc * left.poly) * right.poly)

private theorem subproductTreeListProduct_combinePairs
    (M : CPolynomial.MulContext F) (trees : List (CPolynomial.SubproductTree F)) :
    subproductTreeListProduct (CPolynomial.SubproductTree.combinePairs M trees) =
      subproductTreeListProduct trees := by
  exact subproductTreeFold_combinePairs M trees 1

private theorem buildFromTrees_poly_eq_listProduct
    (M : CPolynomial.MulContext F) :
    ∀ (fuel : Nat) (trees : List (CPolynomial.SubproductTree F))
        (tree : CPolynomial.SubproductTree F),
      CPolynomial.SubproductTree.buildFromTrees M fuel trees = some tree →
        CPolynomial.SubproductTree.poly tree = subproductTreeListProduct trees := by
  intro fuel
  induction fuel with
  | zero =>
      intro trees tree hbuild
      cases trees with
      | nil =>
          simp [CPolynomial.SubproductTree.buildFromTrees] at hbuild
      | cons head rest =>
          cases rest with
          | nil =>
              simp [CPolynomial.SubproductTree.buildFromTrees] at hbuild
              subst hbuild
              simp [subproductTreeListProduct]
          | cons _ _ =>
              simp [CPolynomial.SubproductTree.buildFromTrees] at hbuild
  | succ fuel ih =>
      intro trees tree hbuild
      cases trees with
      | nil =>
          simp [CPolynomial.SubproductTree.buildFromTrees] at hbuild
      | cons head rest =>
          cases rest with
          | nil =>
              simp [CPolynomial.SubproductTree.buildFromTrees] at hbuild
              subst hbuild
              simp [subproductTreeListProduct]
          | cons second rest =>
              have hrec :=
                ih (CPolynomial.SubproductTree.combinePairs M (head :: second :: rest))
                  tree (by simpa [CPolynomial.SubproductTree.buildFromTrees] using hbuild)
              rw [hrec, subproductTreeListProduct_combinePairs M]

private theorem subproductTreeFold_map_leafFor (xs : List F) (acc : CPolynomial F) :
    (xs.map CPolynomial.SubproductTree.leafFor).foldl
        (fun acc tree ↦ acc * CPolynomial.SubproductTree.poly tree) acc =
      xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [CPolynomial.SubproductTree.leafFor]
      exact ih (acc * CPolynomial.linearFactor x)

private theorem subproductTreeListProduct_map_leafFor (xs : List F) :
    subproductTreeListProduct (xs.map CPolynomial.SubproductTree.leafFor) =
      xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) 1 := by
  exact subproductTreeFold_map_leafFor xs 1

/-- Operation dictionary for array vanishing-polynomial construction. -/
structure VanishingPolynomialContext
    (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  vanishingPolynomial : Array F → CPolynomial F
  correct :
    ∀ xs, vanishingPolynomial xs = CPolynomial.vanishingPolynomialArray xs

namespace VanishingPolynomialContext

/-- Direct folded vanishing-polynomial context. -/
def direct : VanishingPolynomialContext F where
  vanishingPolynomial := CPolynomial.vanishingPolynomialArray
  correct := by
    intro xs
    rfl

/-- Subproduct-tree-backed vanishing-polynomial context. -/
def subproduct (M : CPolynomial.MulContext F) : VanishingPolynomialContext F where
  vanishingPolynomial := fun xs ↦
    match CPolynomial.SubproductTree.buildArray M xs with
    | none => CPolynomial.vanishingPolynomialArray xs
    | some tree => CPolynomial.SubproductTree.poly tree
  correct := by
    intro xs
    unfold CPolynomial.SubproductTree.buildArray CPolynomial.SubproductTree.buildList
    cases hbuild :
        CPolynomial.SubproductTree.buildFromTrees M
          (List.length (List.map CPolynomial.SubproductTree.leafFor xs.toList))
          (List.map CPolynomial.SubproductTree.leafFor xs.toList) with
    | none =>
        rfl
    | some tree =>
        change tree.poly = CPolynomial.vanishingPolynomialArray xs
        rw [buildFromTrees_poly_eq_listProduct M _ _ _ hbuild]
        rw [subproductTreeListProduct_map_leafFor]
        simp [CPolynomial.vanishingPolynomialArray]

end VanishingPolynomialContext

private theorem eval_linearFactor_self (x : F) :
    CPolynomial.eval x (CPolynomial.linearFactor x) = 0 := by
  rw [CPolynomial.eval_toPoly]
  simp [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]

private theorem eval_foldl_linearFactor_eq_zero_of_acc
    (ys : List F) {x : F} {acc : CPolynomial F}
    (hacc : CPolynomial.eval x acc = 0) :
    CPolynomial.eval x
      (ys.foldl (fun acc y ↦ acc * CPolynomial.linearFactor y) acc) = 0 := by
  induction ys generalizing acc with
  | nil =>
      simpa using hacc
  | cons y ys ih =>
      apply ih
      rw [CPolynomial.eval_mul, hacc]
      simp

private theorem eval_foldl_linearFactor_eq_zero_of_mem
    (ys : List F) {x : F} (acc : CPolynomial F) (hx : x ∈ ys) :
    CPolynomial.eval x
      (ys.foldl (fun acc y ↦ acc * CPolynomial.linearFactor y) acc) = 0 := by
  induction ys generalizing acc with
  | nil =>
      cases hx
  | cons y ys ih =>
      rw [List.foldl_cons]
      rw [List.mem_cons] at hx
      rcases hx with hxy | htail
      · subst y
        apply eval_foldl_linearFactor_eq_zero_of_acc
        rw [CPolynomial.eval_mul, eval_linearFactor_self]
        simp
      · exact ih (acc * CPolynomial.linearFactor y) htail

/-- Every listed node is a root of the direct vanishing polynomial. -/
theorem eval_vanishingPolynomialArray_eq_zero_of_mem
    (xs : Array F) {x : F} (hx : x ∈ xs.toList) :
    CPolynomial.eval x (CPolynomial.vanishingPolynomialArray xs) = 0 := by
  simpa [CPolynomial.vanishingPolynomialArray] using
    eval_foldl_linearFactor_eq_zero_of_mem xs.toList (1 : CPolynomial F) hx

end CPolynomial

end CompPoly
