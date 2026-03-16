/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree

/-!
# Bivariate Weighted-Degree Tests

Basic regression coverage for the weighted-degree helper layer.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

example (i j u v : ℕ) :
    natWeightedDegree (monomial (F := ℚ) i j) u v = u * i + v * j := by
  exact natWeightedDegree_monomial i j u v

example (p q : ℚ[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  exact natWeightedDegree_add_le p q u v

example {ι : Type*} (s : Finset ι) (f : ι → ℚ[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  exact natWeightedDegree_sum_le s f u v

example (a : ℚ) (p : ℚ[X][Y]) (u v : ℕ) :
    natWeightedDegree (a • p) u v ≤ natWeightedDegree p u v := by
  exact natWeightedDegree_smul_le a p u v

example (Q : ℚ[X][Y]) (P : ℚ[X]) (k : ℕ) (hP : P.natDegree ≤ k - 1) :
    (Q.eval P).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
  exact degree_eval_le_weightedDegree Q P k hP

end Polynomial.Bivariate
