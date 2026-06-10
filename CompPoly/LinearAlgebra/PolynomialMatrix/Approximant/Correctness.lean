/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation

/-!
# Approximant-Basis Correctness Surface

Named theorem surface for X-adic approximant bases and diagonal modular
solution bases.  The executable contexts carry the current proof obligations.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Rows returned by a modular solution-basis context satisfy the modular
equation. -/
theorem modularSolutionBasis_sound
    (ctx : ModularSolutionBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (ctx.solutionBasis equation shift)) :
    rowSatisfiesModularBool ctx.mulContext ctx.modContext row
      equation.matrix equation.moduli = true :=
  ctx.sound equation shift row hrow

/-- Solution-basis completeness/minimality contract.  The final Popov-strength
minimality facts are represented by the context field while proofs are
developed. -/
theorem modularSolutionBasis_complete_minimal
    (ctx : ModularSolutionBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) {row : PolynomialRow F}
    (hrow :
      rowSatisfiesModularBool ctx.mulContext ctx.modContext row
        equation.matrix equation.moduli = true) :
    ∃ basisRow,
      basisRow ∈ MatrixRows (ctx.solutionBasis equation shift) :=
  ctx.complete_minimal equation shift row hrow

end Approximant

end PolynomialMatrix

end CompPoly
