/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Multivariate.Restrict

/-!
  # Multivariate Restrict Tests

  Basic sanity checks for `restrictTotalDegreeOf` and `restrictDegreeOf`.
-/

@[expose] public section

namespace CPoly

open CMvPolynomial

-- TODO: add concrete finite-support examples exercising mixed degree bounds.

example (d : ℕ) : restrictTotalDegreeOf (n := 2) (R := ℚ) d (0 : CMvPolynomial 2 ℚ) = 0 := by
  simp [restrictTotalDegreeOf_zero]

example (d : ℕ) : restrictDegreeOf (n := 2) (R := ℚ) d (0 : CMvPolynomial 2 ℚ) = 0 := by
  simp [restrictDegreeOf_zero]

example (d d' : ℕ) (p : CMvPolynomial 2 ℚ) :
    restrictTotalDegreeOf d (restrictTotalDegreeOf d' p) = restrictTotalDegreeOf (min d d') p := by
  simp [restrictTotalDegreeOf_restrictTotalDegreeOf]

example (d d' : ℕ) (p : CMvPolynomial 2 ℚ) :
    restrictDegreeOf d (restrictDegreeOf d' p) = restrictDegreeOf (min d d') p := by
  simp [restrictDegreeOf_restrictDegreeOf]

example (d d' : ℕ) (p : CMvPolynomial 2 ℚ) :
    restrictTotalDegreeOf d (restrictDegreeOf d' p) =
      restrictDegreeOf d' (restrictTotalDegreeOf d p) := by
  simp [restrictTotalDegreeOf_restrictDegreeOf_comm]

end CPoly
