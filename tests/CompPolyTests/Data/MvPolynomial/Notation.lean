/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Data.MvPolynomial.Notation

/-!
  # Notation Tests

  Examples showing that the notation is correct
-/

open MvPolynomial

example : (X 0 + X 1 * X 2 : ℕ[X Fin 3]) ⸨![1, 2], ![8], ![]⸩ = 17 := by simp +arith +decide

example {a b n : ℕ} (x : Fin a → ℕ) (y : Fin b → ℕ) (p : ℕ[X Fin n]) (h : a + b + 1 = n) :
  p ⸨x, ![n], y⸩ =
    MvPolynomial.eval (Fin.append (Fin.append x ![n]) y ∘ Fin.cast (by omega)) p := rfl

example {n : ℕ} (p : ℕ[X Fin (n + 1)]) (a : Fin n → ℕ) :
  p ⸨X ⦃0⦄, a⸩ = Polynomial.map (MvPolynomial.eval a) (MvPolynomial.finSuccEquivNth _ 0 p) := rfl
