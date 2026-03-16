/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.ToMathlib.Polynomial.BivariateMultiplicity

/-!
# Bivariate Multiplicity Tests

Basic regression coverage for the multiplicity/discriminant helper layer.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

example (f : ℚ[X][Y]) (x y : ℚ) :
    shift f x y = (f.comp (Y + C (C y))).map ((X + C x).compRingHom) := by
  rfl

example (f : ℚ[X][Y]) (x y : ℚ) :
    rootMultiplicity f x y = rootMultiplicity₀ (shift f x y) := by
  rfl

example (x y : ℚ) :
    shift (0 : ℚ[X][Y]) x y = 0 := by
  simp [shift]

example :
    discr_y (0 : ℚ[X][Y]) = 0 := by
  simp [discr_y]

end Polynomial.Bivariate
