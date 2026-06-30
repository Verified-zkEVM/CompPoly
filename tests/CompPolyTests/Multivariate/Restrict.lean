/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Multivariate.Restrict

/-!
  # Multivariate Restrict Tests

  Basic sanity checks for `restrictTotalDegree` and `restrictDegree`.
-/

namespace CPoly

open CMvPolynomial

-- TODO: add concrete finite-support examples exercising mixed degree bounds.

example (d : ℕ) :
    restrictTotalDegree (σ := Fin 2) (R := ℚ) d (0 : CMvPolynomial (Fin 2) ℚ) = 0 := by
  simp [restrictTotalDegree_zero]

example (d : ℕ) : restrictDegree (σ := Fin 2) (R := ℚ) d (0 : CMvPolynomial (Fin 2) ℚ) = 0 := by
  simp [restrictDegree_zero]

example (d d' : ℕ) (p : CMvPolynomial (Fin 2) ℚ) :
    restrictTotalDegree d (restrictTotalDegree d' p) = restrictTotalDegree (min d d') p := by
  simp [restrictTotalDegree_restrictTotalDegree]

example (d d' : ℕ) (p : CMvPolynomial (Fin 2) ℚ) :
    restrictDegree d (restrictDegree d' p) = restrictDegree (min d d') p := by
  simp [restrictDegree_restrictDegree]

example (d d' : ℕ) (p : CMvPolynomial (Fin 2) ℚ) :
    restrictTotalDegree d (restrictDegree d' p) = restrictDegree d' (restrictTotalDegree d p) := by
  simp [restrictTotalDegree_restrictDegree_comm]

end CPoly
