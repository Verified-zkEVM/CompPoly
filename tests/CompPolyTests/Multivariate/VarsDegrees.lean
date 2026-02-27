/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Multivariate.VarsDegrees

/-!
  # Multivariate Vars/Degrees Tests

  Basic sanity checks for `vars`, `degrees`, and `degreeOf`.
-/

namespace CPoly

open CMvPolynomial

-- TODO: add nontrivial examples relating `vars`/`degrees` to explicit monomials.

example (i : Fin 3) : (0 : CMvPolynomial 3 ℚ).degreeOf i = 0 := by
  simp [degreeOf_zero]

example : (0 : CMvPolynomial 3 ℚ).degrees = 0 := by
  simp [degrees_zero]

example : (0 : CMvPolynomial 3 ℚ).vars = ∅ := by
  simp [vars_zero]

example : (1 : CMvPolynomial 3 ℚ).degrees = 0 := by
  simp [degrees_one]

example (p : CMvPolynomial 3 ℚ) (i : Fin 3) :
    i ∈ p.vars ↔ 0 < p.degreeOf i := by
  simp [mem_vars_iff_degreeOf_pos]

end CPoly
