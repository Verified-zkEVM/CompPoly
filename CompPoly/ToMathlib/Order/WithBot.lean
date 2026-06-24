/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import Mathlib.Algebra.Order.Monoid.WithTop

/-!
# Strict additive monotonicity on `WithBot ℕ`

Mathlib's `WithBot.add_lt_add_of_le_of_lt` / `WithBot.add_lt_add_of_lt_of_le` carry `≠ ⊥`
side conditions; the fully strict version below needs none of them over `ℕ`.
Upstreaming candidate.
-/

namespace WithBot

/-- Strict monotonicity of `+` on `WithBot ℕ`: `a < b → c < d → a + c < b + d`. -/
lemma add_lt_add {a b c d : WithBot ℕ} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [← WithBot.coe_add]; omega

end WithBot
