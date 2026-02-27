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

example {n : ℕ} (m : CMvMonomial n) : ofFinsupp m.toFinsupp = m := by
  simp

example {n : ℕ} (m : Fin n →₀ ℕ) : (ofFinsupp m).toFinsupp = m := by
  simp

example {n : ℕ} (m : CMvMonomial n) : m + 0 = m := by
  simp [add_zero]

example : CMvMonomial.totalDegree (#m[1, 2] : CMvMonomial 2) = 3 := by
  native_decide

example : CMvMonomial.degreeOf (#m[3, 4] : CMvMonomial 2) ⟨1, by decide⟩ = 4 := by
  native_decide

end CMvMonomial
end CPoly
