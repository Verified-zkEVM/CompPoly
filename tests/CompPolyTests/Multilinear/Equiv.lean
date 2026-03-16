/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
import CompPoly.Multilinear.Equiv

/-!
  # Multilinear Equiv Tests

  Regression checks for the new `CMlPolynomialEval` helpers added on top of the
  multilinear-to-Mathlib bridge.
-/

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

end CMlPolynomialEval
end CompPoly
