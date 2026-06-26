/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Multivariate.CMvMonomial

/-!
  # Multivariate Monomial Tests

  First-pass sanity checks for `CompPoly.Multivariate.CMvMonomial`.
-/

namespace CPoly
namespace CMvMonomial

-- TODO: add more arithmetic compatibility checks with `MonoR.evalMonomial`.

example {σ : Type*} [FinEnum σ] (m : CMvMonomial σ) : ofFinsupp m.toFinsupp = m := by
  simp

example {σ : Type*} [FinEnum σ] (m : σ →₀ ℕ) : (ofFinsupp m).toFinsupp = m := by
  simp

example {σ : Type*} [FinEnum σ] (m : CMvMonomial σ) : m + 0 = m := by
  simp [add_zero]

example : let v : Vector ℕ 2 := #m[1, 2]; CMvMonomial.totalDegree (σ := Fin 2) v = 3 := by
  decide

example :
    let v : Vector ℕ 2 := #m[3, 4]
    CMvMonomial.degreeOf (σ := Fin 2) v ⟨1, by decide⟩ = 4 := by
  decide

end CMvMonomial
end CPoly
