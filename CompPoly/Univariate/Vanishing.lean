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
    sorry

end VanishingPolynomialContext

/-- Every listed node is a root of the direct vanishing polynomial. -/
theorem eval_vanishingPolynomialArray_eq_zero_of_mem
    (xs : Array F) {x : F} (hx : x ∈ xs.toList) :
    CPolynomial.eval x (CPolynomial.vanishingPolynomialArray xs) = 0 := by
  sorry

end CPolynomial

end CompPoly
