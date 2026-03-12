/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.ToMathlib.Polynomial.BivariateDegree

/-!
# Bivariate Degree Tests

Basic regression coverage for the Mathlib-facing bivariate degree and evaluation bridge.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

example (f : ℚ[X][Y]) : totalDegree f = natWeightedDegree f 1 1 := by
  exact total_deg_as_weighted_deg (f := f)

example (f : ℚ[X][Y]) : degreeX f = natWeightedDegree f 1 0 := by
  exact degreeX_as_weighted_deg (f := f)

example (f : ℚ[X][Y]) : natDegreeY f = natWeightedDegree f 0 1 := by
  exact degreeY_as_weighted_deg (f := f)

example (f g : ℚ[X][Y]) (hf : f ≠ 0) (hg : g ≠ 0) :
    degreeX (f * g) = degreeX f + degreeX g := by
  exact degreeX_mul f g hf hg

example (x : ℚ) (f : ℚ[X][Y]) :
    evalX x f = f.map (Polynomial.evalRingHom x) := by
  exact evalX_eq_map x f

example (y : ℚ) (f : ℚ[X][Y]) :
    evalY y f = evalX y (swap f) := by
  exact evalY_eq_evalX_swap y f

example (f : ℚ[X][Y]) :
    degreeX (swap f) = natDegreeY f := by
  exact degreeX_swap f

example (f : ℚ[X][Y]) :
    natDegreeY (swap f) = degreeX f := by
  exact natDegreeY_swap f

example (A : ℚ[X][Y]) (hA : A ≠ 0) (P : Finset ℚ) :
    (P.filter (fun x => evalX x A = 0)).card ≤ degreeX A := by
  exact card_evalX_eq_zero_le_degreeX A hA P

example {A B G A1 B1 : ℚ[X][Y]} (hA : A = G * A1) (hB : B = G * B1)
    (x : ℚ) (hx : evalX x G ≠ 0) (q : ℚ[X])
    (h : evalX x B = q * evalX x A) :
    evalX x B1 = q * evalX x A1 := by
  exact descend_evalX hA hB x hx q h

example (B : ℚ[X][Y]) (hB : B ≠ 0) (P : Finset ℚ) (hcard : degreeX B < P.card) :
    ∃ x ∈ P, (evalX x B).natDegree = natDegreeY B := by
  exact exists_x_preserve_natDegreeY B hB P hcard

end Polynomial.Bivariate

namespace CompPoly
namespace CBivariate

example (f : CBivariate ℚ) :
    Polynomial.Bivariate.natDegreeY (toPoly f) = CBivariate.natDegreeY (R := ℚ) f := by
  simpa [Polynomial.Bivariate.natDegreeY] using natDegreeY_toPoly (R := ℚ) f

example (f : CBivariate ℚ) :
    Polynomial.Bivariate.degreeX (toPoly f) = CBivariate.natDegreeX (R := ℚ) f := by
  exact degreeX_toPoly f

example (f : CBivariate ℚ) :
    Polynomial.Bivariate.totalDegree (toPoly f) = CBivariate.totalDegree (R := ℚ) f := by
  exact totalDegree_toPoly_spec f

example (f : CBivariate ℚ) :
    Polynomial.Bivariate.natWeightedDegree (toPoly f) 2 3 =
      CBivariate.natWeightedDegree (R := ℚ) f 2 3 := by
  exact natWeightedDegree_toPoly f 2 3

end CBivariate
end CompPoly
