/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Small-factor extraction for reducible polynomials

A reducible polynomial of degree `n` always has an irreducible factor of degree at most
`n / 2`: it splits as a product of two non-units whose degrees sum to `n`, and the smaller
of the two dominates an irreducible factor.

This is the pigeonhole step of Rabin's irreducibility test (see
`CompPoly/Data/Polynomial/Rabin.lean`), which needs to bound the degree of a hypothetical
small factor in order to derive a contradiction.

## Main statements

* `Polynomial.exists_factor_natDegree_le_of_reducible`: a reducible polynomial of degree `n`
  has an irreducible factor of degree at most `n / 2`.
-/

namespace Polynomial

variable {R : Type*} [Field R]

/--
A reducible polynomial of positive degree `n` has an irreducible factor of degree at most
`n / 2`.

Writing `P = a * b` with both factors non-units, their degrees sum to `n`, so the smaller one
has degree at most `n / 2`; any irreducible factor of it works.
-/
theorem exists_factor_natDegree_le_of_reducible (P : R[X]) {n : ℕ}
    (h_deg : P.natDegree = n) (h_pos : 0 < n) (h_red : ¬ Irreducible P) :
    ∃ q, Irreducible q ∧ q ∣ P ∧ q.natDegree ≤ n / 2 := by
  have h_ne_zero : P ≠ 0 := fun h => by
    rw [h, natDegree_zero] at h_deg; omega
  have h_not_unit : ¬ IsUnit P :=
    not_isUnit_of_natDegree_pos P (by omega)
  -- Reducible and not a unit: `P` splits into two non-units.
  obtain ⟨a, b, h_eq, ha_nu, hb_nu⟩ : ∃ a b, P = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    rw [irreducible_iff] at h_red
    push Not at h_red
    exact h_red h_not_unit
  have ha_ne_zero : a ≠ 0 := fun h => h_ne_zero (by rw [h_eq, h, zero_mul])
  have hb_ne_zero : b ≠ 0 := fun h => h_ne_zero (by rw [h_eq, h, mul_zero])
  have h_deg_sum : a.natDegree + b.natDegree = n := by
    rw [← h_deg, h_eq, natDegree_mul ha_ne_zero hb_ne_zero]
  -- Take an irreducible factor of whichever side has the smaller degree.
  rcases le_total a.natDegree b.natDegree with h_le | h_le
  · obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor ha_nu ha_ne_zero
    exact ⟨q, hq_irr, hq_dvd.trans (Dvd.intro b h_eq.symm),
      le_trans (natDegree_le_of_dvd hq_dvd ha_ne_zero) (by omega)⟩
  · obtain ⟨q, hq_irr, hq_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hb_nu hb_ne_zero
    exact ⟨q, hq_irr, hq_dvd.trans (Dvd.intro_left a h_eq.symm),
      le_trans (natDegree_le_of_dvd hq_dvd hb_ne_zero) (by omega)⟩

end Polynomial
