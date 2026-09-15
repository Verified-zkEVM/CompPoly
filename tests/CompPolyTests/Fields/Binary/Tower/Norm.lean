/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.Field
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Binary tower norm tests

The irreducible quadratic over `ZMod 2` gives a valid norm certificate. Replacing its linear
coefficient with zero produces a nonzero pair of norm zero, so the no-root requirement is
necessary. Concrete field clients retain the existing arithmetic and inverse denominator.
-/

namespace CompPolyTests.BinaryTowerNorm

open ConcreteBinaryTower

-- The predecessor certificate applies to every nonzero element of the first extension.
example (a : ConcreteBTField 1) (ha : a ≠ 0) :
    let hi := (split (show 1 > 0 by decide) a).1
    let lo := (split (show 1 > 0 by decide) a).2
    concrete_mul lo (lo + concrete_mul hi (Z 0)) + concrete_mul hi hi ≠ 0 :=
  norm_of_ne_zero_is_ne_zero (getBTFResult 0) a ha

-- Field dictionaries still select the exact executable multiplication and inverse.
example (k : ℕ) (a b : ConcreteBTField k) :
    a * b = concrete_mul a b ∧ a⁻¹ = concrete_inv a := ⟨rfl, rfl⟩

-- All three nonzero low/high pairs have norm one over the two-element base field.
example :
    (concrete_mul (one (k := 0)) (one + concrete_mul zero (Z 0)) +
      concrete_mul zero zero = one) ∧
    (concrete_mul (zero (k := 0)) (zero + concrete_mul one (Z 0)) +
      concrete_mul one one = one) ∧
    (concrete_mul (one (k := 0)) (one + concrete_mul one (Z 0)) +
      concrete_mul one one = one) := by
  change (1 * (1 + 0 * 1) + 0 * 0 = (1 : ConcreteBTField 0)) ∧
    (0 * (0 + 1 * 1) + 1 * 1 = (1 : ConcreteBTField 0)) ∧
    (1 * (1 + 1 * 1) + 1 * 1 = (1 : ConcreteBTField 0))
  simp only [mul_zero, mul_one, add_zero, zero_add, add_self_cancel, and_self]

-- The no-root fact has a concrete inhabitant, independently of the tower recursion.
example (x : QuadraticAlgebra (ZMod 2) (-1) 1) :
    x.norm = 0 ↔ x = 0 := by
  let : Fact (∀ r : ZMod 2, r ^ 2 ≠ -1 + 1 * r) := ⟨by decide⟩
  exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero

-- Omitting the no-root condition would make norm nonvanishing false.
example :
    let x : QuadraticAlgebra (ZMod 2) (-1) 0 := ⟨1, 1⟩
    x ≠ 0 ∧ x.norm = 0 := by
  simp [QuadraticAlgebra.ext_iff, QuadraticAlgebra.norm_def]

example : ¬∀ r : ZMod 2, r ^ 2 ≠ -1 + 0 * r := by
  decide

end CompPolyTests.BinaryTowerNorm
