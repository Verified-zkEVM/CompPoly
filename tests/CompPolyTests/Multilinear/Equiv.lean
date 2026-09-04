/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Multilinear.Equiv

/-!
  # Multilinear Equiv Tests

  Regression checks for the new `CMlPolynomialEval` helpers added on top of the
  multilinear-to-Mathlib bridge.
-/

@[expose] public section

namespace CompPoly
namespace CMlPolynomialEval

example (p : CMlPolynomialEval ℚ 2) :
    toMvPolynomial p = CMlPolynomial.toMvPolynomial (CMlPolynomial.lagrangeToMono 2 p) := by
  rfl

example (p : CMlPolynomialEval ℚ 2) :
    toMvPolynomialDeg1 p = CMlPolynomial.toMvPolynomialDeg1 (CMlPolynomial.lagrangeToMono 2 p) := by
  rfl

example (w : Vector ℚ 2) :
    eqPolynomial w = toMvPolynomial (lagrangeBasis w) := by
  rfl

example (w : Vector ℚ 2) :
    eqPolynomialDeg1 w = toMvPolynomialDeg1 (lagrangeBasis w) := by
  rfl

example (w x : Vector ℚ 2) :
    eqTilde w x = eval (lagrangeBasis w) x := by
  rfl

example (w x : Vector ℚ 2) :
    eqTilde w x = ∏ i : Fin 2, (w[i] * x[i] + (1 - w[i]) * (1 - x[i])) := by
  exact eqTilde_eq_prod w x

example (w₁ x₁ : Vector ℚ 2) (w₂ x₂ : Vector ℚ 3) :
    eqTilde (w₁ ++ w₂) (x₁ ++ x₂) = eqTilde w₁ x₁ * eqTilde w₂ x₂ := by
  exact eqTilde_append w₁ x₁ w₂ x₂

end CMlPolynomialEval
end CompPoly
