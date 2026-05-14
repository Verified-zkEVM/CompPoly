/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Univariate.BatchEval.Context
import CompPoly.Univariate.BatchEval.Naive

/-!
# Subproduct-Tree Batch Evaluation

Executable subproduct-tree construction and descent for univariate batch
evaluation.
-/

namespace CompPoly
namespace CPolynomial

variable {R : Type*}

/-- The linear factor `X - C x` used as a subproduct-tree leaf. -/
def linearFactor [Field R] [BEq R] [LawfulBEq R] (x : R) : CPolynomial R :=
  X - C x

/-- A subproduct tree stores the product polynomial at every node. -/
inductive SubproductTree (R : Type*) [Zero R] where
  /-- A leaf for one evaluation point. The polynomial is `X - C x`. -/
  | leaf (x : R) (poly : CPolynomial R)
  /-- An internal node stores the product of its children. -/
  | node (poly : CPolynomial R) (left right : SubproductTree R)

namespace SubproductTree

/-- The product polynomial stored at the root of a subproduct tree. -/
def poly [Zero R] : SubproductTree R → CPolynomial R
  | leaf _ p => p
  | node p _ _ => p

/-- Build a leaf for one evaluation point. -/
def leafFor [Field R] [BEq R] [LawfulBEq R] (x : R) : SubproductTree R :=
  leaf x (linearFactor x)

/-- Combine two neighboring trees using the selected multiplication backend at this level. -/
def combine [Field R] [BEq R] [LawfulBEq R] (M : MulContext R)
    (level : Nat) (left right : SubproductTree R) : SubproductTree R :=
  node (M.mulAtLevel level left.poly right.poly) left right

/-- Pair adjacent trees into the next subproduct-tree level. -/
def combinePairs [Field R] [BEq R] [LawfulBEq R] (M : MulContext R) (level : Nat) :
    List (SubproductTree R) → List (SubproductTree R)
  | [] => []
  | [tree] => [tree]
  | left :: right :: rest => combine M level left right :: combinePairs M level rest

/-- Repeatedly combine tree levels, bounded by fuel for straightforward termination. -/
def buildFromTrees [Field R] [BEq R] [LawfulBEq R] (M : MulContext R) (level : Nat) :
    Nat → List (SubproductTree R) → Option (SubproductTree R)
  | 0, [tree] => some tree
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [tree] => some tree
  | fuel + 1, trees => buildFromTrees M (level + 1) fuel (combinePairs M level trees)

/-- Build a subproduct tree from an ordered list of evaluation points. -/
def buildList [Field R] [BEq R] [LawfulBEq R] (M : MulContext R)
    (xs : List R) : Option (SubproductTree R) :=
  let leaves := xs.map leafFor
  buildFromTrees M 0 leaves.length leaves

/-- Build a subproduct tree from an ordered array of evaluation points. -/
def buildArray [Field R] [BEq R] [LawfulBEq R] (M : MulContext R)
    (xs : Array R) : Option (SubproductTree R) :=
  buildList M xs.toList

/-- Descend a subproduct tree with remainders and return values in leaf order. -/
def evalList [Field R] [BEq R] [LawfulBEq R] (D : ModContext R)
    (p : CPolynomial R) : SubproductTree R → List R
  | leaf x leafPoly =>
      let rem := D.modByMonic p leafPoly
      [rem.evalHorner x]
  | node _ left right =>
      evalList D (D.modByMonic p left.poly) left ++
        evalList D (D.modByMonic p right.poly) right

end SubproductTree

/-- Evaluate a polynomial at many points using a subproduct tree. -/
def evalBatchSubproduct [Field R] [BEq R] [LawfulBEq R]
    (M : MulContext R) (D : ModContext R) (p : CPolynomial R) (xs : Array R) : Array R :=
  match SubproductTree.buildArray M xs with
  | none => #[]
  | some tree => (SubproductTree.evalList D p tree).toArray

end CPolynomial
end CompPoly
