/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Multivariate.CMvMonomial
public meta import Mathlib.Algebra.Ring.Nat
public meta import CompPoly.Multivariate.CMvMonomial

/-!
  # Multivariate Monomial Tests

  First-pass sanity checks for `CompPoly.Multivariate.CMvMonomial`.
-/

@[expose] public section

namespace CPoly
namespace CMvMonomial

-- TODO: add more arithmetic compatibility checks with `MonoR.evalMonomial`.

example {n : ℕ} (m : CMvMonomial n) : ofFinsupp m.toFinsupp = m := by
  simp

example {n : ℕ} (m : Fin n →₀ ℕ) : (ofFinsupp m).toFinsupp = m := by
  simp

example {n : ℕ} (m : CMvMonomial n) : m + 0 = m := by
  simp [add_zero]

example : CMvMonomial.totalDegree (#m[1, 2] : CMvMonomial 2) = 3 := by
  decide

example : CMvMonomial.degreeOf (#m[3, 4] : CMvMonomial 2) ⟨1, by decide⟩ = 4 := by
  decide

/-! Divisibility is the exponent order: `m₁ ∣ m₂` iff `m₁[i] ≤ m₂[i]` for every `i`. -/

example : (show CMvMonomial 2 from #m[1, 0]) ∣ (show CMvMonomial 2 from #m[2, 1]) := by
  rw [dvd_iff]; decide

example : ¬ (show CMvMonomial 2 from #m[2, 1]) ∣ (show CMvMonomial 2 from #m[1, 0]) := by
  rw [dvd_iff]; decide

example : ¬ (show CMvMonomial 2 from #m[1, 0]) ∣ (show CMvMonomial 2 from #m[0, 1]) := by
  rw [dvd_iff]; decide

example : ¬ (show CMvMonomial 2 from #m[0, 1]) ∣ (show CMvMonomial 2 from #m[1, 0]) := by
  rw [dvd_iff]; decide

example : (show CMvMonomial 3 from 0) ∣ (show CMvMonomial 3 from #m[4, 0, 2]) := by
  rw [dvd_iff]; decide

example {n : ℕ} (m c : CMvMonomial n) : m ∣ m + c :=
  dvd_iff_exists_add.2 ⟨c, rfl⟩

#guard divides (show CMvMonomial 2 from #m[1, 0]) #m[2, 1]
#guard !divides (show CMvMonomial 2 from #m[2, 1]) #m[1, 0]

end CMvMonomial

namespace MonoR

/-! A term divides another when both its monomial and its coefficient do, in the same direction.
The last example fails if only the monomial half of the check points the right way. -/

example : (show MonoR 2 ℕ from (#m[1, 0], 2)) ∣ (show MonoR 2 ℕ from (#m[2, 1], 6)) := by
  change divides _ _ = true
  simp only [divides, decide_eq_true_eq]
  exact ⟨CMvMonomial.dvd_iff.2 (by decide), by decide⟩

example : ¬ (show MonoR 2 ℕ from (#m[2, 1], 6)) ∣ (show MonoR 2 ℕ from (#m[1, 0], 2)) := by
  change ¬ divides _ _ = true
  simp only [divides, decide_eq_true_eq]
  exact fun h ↦ absurd (CMvMonomial.dvd_iff.1 h.1 0 (by decide)) (by decide)

example : ¬ (show MonoR 2 ℕ from (#m[1, 0], 6)) ∣ (show MonoR 2 ℕ from (#m[2, 1], 2)) := by
  change ¬ divides _ _ = true
  simp only [divides, decide_eq_true_eq]
  exact fun h ↦ absurd h.2 (by decide)

#guard divides (show MonoR 2 ℕ from (#m[1, 0], 2)) (#m[2, 1], 6)
#guard !divides (show MonoR 2 ℕ from (#m[1, 0], 6)) (#m[2, 1], 2)

end MonoR
end CPoly
