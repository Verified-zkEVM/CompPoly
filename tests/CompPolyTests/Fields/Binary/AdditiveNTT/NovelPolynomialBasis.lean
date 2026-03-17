/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis

/-!
  # NovelPolynomialBasis tests

  Regression examples from the NovelPolynomialBasis development.
-/

example {r : ℕ} [NeZero r]
  (i : Fin r) (h_i_eq_0 : i = 0) : Set.Ico 0 i = ∅ := by
  rw [h_i_eq_0] -- ⊢ Set.Ico 0 0 = ∅
  simp only [Set.Ico_eq_empty_iff]
  exact Nat.not_lt_zero 0
