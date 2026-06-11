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
    (shift : Array Nat) (degreeBound? : Option Nat) {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (ctx.solutionBasis equation shift degreeBound?)) :
    rowSatisfiesModularBool ctx.mulContext ctx.modContext row
      equation.matrix equation.moduli = true :=
  ctx.sound equation shift degreeBound? row hrow

/-- Solution-basis completeness/minimality contract, relative to the
caller-supplied degree bound: a solution row within the bound (vacuous for
`none`) is matched by a returned basis row whose shifted degree does not
exceed the bound — the solution's own degree when no bound is supplied. -/
theorem modularSolutionBasis_complete_minimal
    (ctx : ModularSolutionBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (degreeBound? : Option Nat) {row : PolynomialRow F}
    {rowDegree : Nat}
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hshift : shift.size = equation.solutionWidth)
    (hrow :
      rowSatisfiesModularBool ctx.mulContext ctx.modContext row
        equation.matrix equation.moduli = true)
    (hnonzero : rowIsZero row = false)
    (hwidth : row.size ≤ equation.solutionWidth)
    (hdegree : rowShiftedDegree? row shift = some rowDegree)
    (hbound : ∀ bound, degreeBound? = some bound → rowDegree ≤ bound) :
    (∀ basisRow,
      basisRow ∈ MatrixRows (ctx.solutionBasis equation shift degreeBound?) →
        basisRow.size ≤ equation.solutionWidth) ∧
    ∃ basisRow degree,
      basisRow ∈ MatrixRows (ctx.solutionBasis equation shift degreeBound?) ∧
      rowShiftedDegree? basisRow shift = some degree ∧
      degree ≤ degreeBound?.getD rowDegree :=
  ctx.complete_minimal equation shift degreeBound? row rowDegree hmonic hcols
    hshift hrow hnonzero hwidth hdegree hbound

end Approximant

end PolynomialMatrix

end CompPoly
