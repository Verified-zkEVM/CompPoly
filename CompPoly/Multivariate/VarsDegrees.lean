/- 
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fawad Haider, Quang Dao
-/
import CompPoly.Multivariate.CMvPolynomial

/-!
# Lemmas for `CMvPolynomial.vars` and `CMvPolynomial.degrees`
-/

namespace CPoly

open Std

variable {σ : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ] {R : Type}

/-- `i ∈ p.vars` iff `0 < p.degreeOf i`. -/
@[simp]
lemma mem_vars_iff_degreeOf_pos [Zero R]
    (i : σ) (p : CMvPolynomial σ R) :
    i ∈ p.vars ↔ 0 < p.degreeOf i := by
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  unfold CMvPolynomial.vars CMvPolynomial.degreeOf
  simp [Multiset.mem_toFinset, Multiset.count_pos]

attribute [grind =] mem_vars_iff_degreeOf_pos

end CPoly
