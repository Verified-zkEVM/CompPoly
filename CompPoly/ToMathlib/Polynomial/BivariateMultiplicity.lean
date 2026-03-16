/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import CompPoly.ToMathlib.Polynomial.BivariateDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Mathlib-Facing Bivariate Multiplicity Helpers

This file collects multiplicity- and discriminant-oriented helpers for Mathlib's
bivariate polynomial surface `R[X][Y]`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- Root multiplicity of a bivariate polynomial at the origin. -/
def rootMultiplicity₀ [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := weightedDegree f 1 1
  match deg with
  | none => none
  | some deg =>
      List.min? <|
        List.filterMap
          (fun (i, j) ↦ if coeff f i j = 0 then none else some (i + j))
          (List.product (List.range deg.succ) (List.range deg.succ))

end Semiring

section CommSemiring

variable [CommSemiring F]

/-- Shift a bivariate polynomial by `(x, y)`. -/
def shift (f : F[X][Y]) (x y : F) : F[X][Y] :=
  (f.comp (Y + C (C y))).map (Polynomial.compRingHom (X + C x : F[X]))

variable [DecidableEq F]

/-- Root multiplicity (order of vanishing) of a bivariate polynomial at `(x, y)`. -/
def rootMultiplicity (f : F[X][Y]) (x y : F) : Option ℕ :=
  rootMultiplicity₀ (shift f x y)

end CommSemiring

section CommRing

variable [CommRing F]

/-- A discriminant-like helper in the outer `Y` variable.

Unlike Mathlib's univariate `discr`, this returns `0` for constant bivariate polynomials. -/
def discr_y (f : F[X][Y]) : F[X] :=
  if 0 < f.degree then
    (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr
  else
    0

end CommRing

end
end Polynomial.Bivariate
