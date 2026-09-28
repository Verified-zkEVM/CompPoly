/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.CoordinateArithmetic

/-!
# Concrete successor arithmetic clients

Symbolic clients use public coordinate laws with the selected tower scalar action. Concrete
cases retain the generator term, distinguish low/high order, and include zero in the inverse
formula. The norm certificate's no-root counterexample is covered by the separate norm tests.
-/

namespace CompPolyTests.BinaryTowerCoordinateArithmetic

open ConcreteBinaryTower ConcreteBinaryTower.Coordinates

example (k : ℕ) (x : ConcreteBTField (k + 1)) :
    low k x⁻¹ = (norm k x)⁻¹ * (low k x + high k x * Z k) := by
  rw [inv_eq_joinSucc, low_joinSucc]

example (k : ℕ) (x : ConcreteBTField (k + 1)) :
    high k x⁻¹ = (norm k x)⁻¹ * high k x := by
  rw [inv_eq_joinSucc, high_joinSucc]

example (k : ℕ) (x : ConcreteBTField (k + 1)) (hx : norm k x = 0) : x = 0 := by
  by_contra h
  exact norm_ne_zero k x h hx

example (k : ℕ) (a : ConcreteBTField k) (x : ConcreteBTField (k + 1)) :
    let := ConcreteBTFieldAlgebra (Nat.le_succ k)
    conjugate k (a • x) = a • conjugate k x := by
  let := ConcreteBTFieldAlgebra (Nat.le_succ k)
  simp only [conjugate_eq_joinSucc, low_smul, high_smul, smul_joinSucc]
  congr 1
  ring

-- The linear coefficient of the defining polynomial cannot be dropped.
example : joinSucc 0 0 1 * joinSucc 0 0 1 ≠ joinSucc 0 1 0 := by
  rw [joinSucc_mul_joinSucc]
  simp only [zero_mul, one_mul, add_zero, zero_add]
  decide +kernel

-- At level two, asymmetric coordinates distinguish conjugation from exchanging halves.
example : conjugate 1 (joinSucc 1 (fromNat 1) (fromNat 2)) =
    joinSucc 1 (fromNat 2) (fromNat 2) := by
  simp only [conjugate_eq_joinSucc, low_joinSucc, high_joinSucc]
  change joinSucc 1 (fromNat 1 + concrete_mul (fromNat 2) (Z 1)) (fromNat 2) = _
  simp only [concrete_mul.eq_1, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceDIte]
  decide +kernel

example : conjugate 1 (joinSucc 1 (fromNat 1) (fromNat 2)) ≠
    joinSucc 1 (fromNat 2) (fromNat 1) := by
  intro h
  have hh := congrArg (high 1) h
  simp only [conjugate_eq_joinSucc, high_joinSucc] at hh
  exact (by decide : fromNat (k := 1) 2 ≠ fromNat 1) hh

example (k : ℕ) :
    norm k (joinSucc k 0 0) = 0 ∧
      conjugate k (joinSucc k 0 0) = joinSucc k 0 0 := by
  constructor
  · simp only [norm_eq, low_joinSucc, high_joinSucc, zero_mul, add_zero]
  · simp only [conjugate_eq_joinSucc, low_joinSucc, high_joinSucc, zero_mul, add_zero]

example (k : ℕ) : (joinSucc k 0 0)⁻¹ = joinSucc k 0 0 := by
  rw [inv_eq_joinSucc, norm_eq, low_joinSucc, high_joinSucc]
  simp only [zero_mul, add_zero, inv_zero]

end CompPolyTests.BinaryTowerCoordinateArithmetic
